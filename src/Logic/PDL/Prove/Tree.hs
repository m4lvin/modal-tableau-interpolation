{-# LANGUAGE FlexibleInstances, OverloadedStrings #-}

module Logic.PDL.Prove.Tree where

import Control.Arrow
import Data.Containers.ListUtils (nubOrd)
import qualified Data.GraphViz.Attributes.Complete as C
import qualified Data.GraphViz.Attributes.HTML as HTML
import qualified Data.Text.Lazy as T
import Data.GraphViz hiding (Shape(Star))
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List
import Data.Maybe
import Data.String( IsString(..) )
-- import Debug.Trace

import Logic.Internal
import Logic.PDL

-- | A Tableau is either a node or an end marker.
-- TODO: rename type to singular!
data Tableaux = Node -- ^ A node contains:
                [WForm]    -- ^ current weighted (and possibly marked) formulas
                History    -- ^ previous formula lists and rules up to the root
                RuleName   -- ^ name of the rule that is applied here
                [WForm]    -- ^ *active* wformulas to which the rule is applied
                [Tableaux] -- ^ child nodes
              | End -- ^ End of a tableau (not necessarily closed!)
  deriving (Eq,Ord,Show)

-- | All nodes of a tableau.
allNodesOf :: Tableaux -> [[WForm]]
allNodesOf (Node wfs _ _ _ ts) = wfs : concatMap allNodesOf ts
allNodesOf End = []

-- | A history is a list of pairs of a list of weighted formulas and the rule used.
-- Note: head of this list is the immediate predecessor, last element is the root!
type History = [([WForm],RuleName)]

data RuleName = NoR | CloseR | NegR | ConR | NConR | LoadR | ModR | BoxR | DiaR | LpR
  deriving (Eq,Ord,Show)

ruleNames :: [(String, RuleName)]
ruleNames =
  [ (""   , NoR)
  , ("✘" , CloseR)
  , ("¬"  , NegR)
  , ("∧"  , ConR)
  , ("¬∧" , NConR)
  , ("L+" , LoadR)
  , ("M"  , ModR)
  , ("□"  , BoxR)
  , ("♢"  , DiaR)
  , ("lpr", LpR)
  ]

instance Stringable RuleName where
  toString rln = case lookup rln (map (\(x,y) -> (y,x)) ruleNames) of
    Nothing -> error $ "unknown rule: " ++ show rln
    Just str -> str

instance IsString RuleName where
  fromString str = case lookup str ruleNames of
    Nothing -> error $ "unknown rule: " ++ str
    Just rln -> rln

-- | A loaded formula is prefixed by a negation and a non-empty sequence of boxes.
-- Example: (Neg f, [a,b]) stands for ¬[a][b]f with [a][b] underlined.
type Marked f = (f, [Prog]) -- where f starts with "Neg"
-- TODO: rename to Loaded, and flip around the order?

-- A WForm is weighted (Left/Right) and may have a marking.
type WForm = (Either Form Form, [Prog])

collapse :: WForm -> Marked Form
collapse (Left f,m)  = (f,m)
collapse (Right f,m) = (f,m)

isLeft :: WForm -> Bool
isLeft (Left  _, _) = True
isLeft (Right _, _) = False

isLoadedNode :: [WForm] -> Bool
isLoadedNode = not . all (null . snd)

ppWForms :: [WForm] -> [WForm] -> String
ppWForms wfs actives = intercalate ", " (map ppFormA (filter isLeft wfs)) ++ "   |   " ++ intercalate ", " (map ppFormA (filter (not . isLeft) wfs)) where
  ppFormA wf = [ '»' |  wf `elem` actives ] ++ ppLoadForm (collapse wf) ++ [ '«' |  wf `elem` actives ]

ppLoadForm :: Marked Form -> String
ppLoadForm (x, []) = toString x
ppLoadForm (Neg f, ps) = "~__[" ++ intercalate "][" (map toString ps) ++ "]__" ++ toString f
ppLoadForm bad = error $ "bad: " ++ show bad

htmlWForms :: [WForm] -> [WForm] -> HTML.Text
htmlWForms wfs actives = intercalate [strp ", "] (map ppFormA (filter isLeft wfs)) ++ [strp "   |   "] ++ intercalate [strp ", "] (map ppFormA (filter (not . isLeft) wfs)) where
  ppFormA :: WForm -> HTML.Text
  ppFormA wf = (if wf `elem` actives then \ts -> [HTML.Format HTML.Bold ts] else id) $ htmlLoadForm (collapse wf)

strp :: String -> HTML.TextItem
strp = HTML.Str . T.pack

htmlLoadForm :: Marked Form -> HTML.Text
htmlLoadForm (x, []) = [ strp $ removePars (toString x) ]
htmlLoadForm (Neg f, ps) = [ HTML.Format HTML.Underline [strp "¬[", strp $ intercalate "][" (map toString ps)], strp "]", strp $ toString f ]
htmlLoadForm bad = error $ "bad: " ++ show bad

instance DispAble Tableaux where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel ("." :: String)]
    toGraph' pref (Node wfs _ rule actives ts) = do
      node pref [shape PlainText, C.Label $ C.HtmlLabel $ HTML.Text $ htmlWForms wfs actives]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel ("(" ++ toString rule ++ ")")]
        ) (zip ts [(0::Integer)..])

type RulePriority = Int -- TODO: use a finite data RuleType = Local | Critical | Marking  or similar?

-- | Rules: Given a formula, is their an applicable rule?
-- If so, which rule, what replaces the active formula, and how do other formulas change and survive?
type RuleApplication = (RuleName, RulePriority, [[Marked Form]], Form -> Maybe Form)

noChange :: Form -> Maybe Form
noChange = Just

isMarked :: (a, [Prog]) -> Bool
isMarked (_, []) = False
isMarked (_, _:_ ) = True

-- | The (L+) rule, marking ¬[a_1]...[a_n]g  by loading the sequence of boxes.
-- This rule has priority 4.
markRulesFor :: Marked Form -> [RuleApplication]
markRulesFor (Neg f, []) = case boxesOf f of
  ([] , _)         -> []
  (ps@(_:_), g) -> [ ("L+", 4, [ [ (Neg g, ps) ] ], noChange) ]
markRulesFor (_, []) = []
markRulesFor (_, _:_)  = [] -- TODO add L- rule here, but avoid immediately after L+

boxesOf :: Form -> ([Prog], Form)
boxesOf (Box prog nextf) = let (rest,endf) = boxesOf nextf in (prog:rest, endf)
boxesOf endf = ([], endf)

-- Definition 9
projection :: Atom -> Form -> Maybe Form
projection x (Box (Ap y) g) | x == y = Just g
projection _ _                       = Nothing

-- | Unfold the program in the top level modality. Assuming "at least one step".
-- The two levels of lists are: branches, formulas.
-- TODO: rewrite this to use the "H" and "P" definition instead of f0 and nform.
unfold :: Form -> Maybe Form -> [[Form]]
unfold f0 nform = -- trace ("unfoldled " ++ toString f0 ++ " with nforms " ++ toStrings nforms ++ " to " ++ intercalate " ; " (map (intercalate "," . map toString) (g f0))) $
  nub $ g f0 where
  -- diamonds:
  g (Neg (Box (Ap ap)     f)) = [[Neg (Box (Ap ap) f)]]
  g (Neg (Box (Cup p1 p2) f)) = g (Neg (Box p1 f)) ++ g (Neg (Box p2 f))
  g (Neg (Box (pa :- pb)  f)) = g (Neg (Box pa (Box pb f)))
  g (Neg (Box (Test tf)   f)) = [ tf : rest | rest <- g (Neg f) ] -- diamond test is not branching.
  g (Neg (Box (Star pr)   f)) =
    if Just (Box (Star pr)   f) == nform
    then [ ] -- new way to do condition 4, never create a branch with ~[a^n]P
    else g (Neg f) ++ unfold (Neg (Box pr (Box (Star pr) f)))
                              (Just $ Box (Star pr ) f)
  -- boxes:
  g (Box (Ap ap)     f) = [[Box (Ap ap) f]]
  g (Box (Cup p1 p2) f) = g (Box p1 f) +.+ g (Box p2 f)
  g (Box (pa :- pb)  f) = g (Box pa (Box pb f))
  g (Box (Test tf)   f) = [Neg tf] : g f -- box test is branching.
  g (Box (Star pr)   f) =
    if Just (Box (Star pr) f) == nform
    then [ [] ] -- new way to do condition 2, avoid loops.
    else g f +.+ unfold (Box pr (Box (Star pr) f)) (Just $ Box (Star pr) f)
  -- other formulas, no unfolding:
  g f@(Neg Bot) = [[ f ]]
  g f@(Neg (At _)) = [[ f ]]
  g f@(Neg (Neg _)) = [[ f ]]
  g f@(Neg (Con _ _)) = [[ f ]]
  g f@Bot = [[ f ]]
  g f@(At _) = [[ f ]]
  g f@(Con _ _) = [[ f ]]

unfoldLoaded :: Marked Form -> Maybe (Marked Form) -> [[Marked Form]]
unfoldLoaded f0@(Neg _, _) nform = -- trace ("unfoldled " ++ toString f0 ++ " with nforms " ++ toStrings nforms ++ " to " ++ intercalate " ; " (map (intercalate "," . map toString) (g f0))) $
  nub $ g f0 where
  -- diamonds:
  g (f, []) = [[(f, [])]]
  g (Neg f, (Ap ap)     :rest) = [[(Neg f , Ap ap:rest)]]
  g (Neg f, (Cup p1 p2) :rest) = g (Neg f, p1:rest) ++ g (Neg f, p2:rest)
  g (Neg f, (pa :- pb)  :rest) = g (Neg f, pa:pb:rest)
  g (Neg f, (Test tf)   :rest) = [ (tf,[]) : next | next <- g (Neg f, rest) ] -- diamond test is not branching.
  g (Neg f, (Star pr)   :rest) =
    if Just (Neg f, Star pr:rest) == nform
    then [ ] -- new way to do condition 4, never create a branch with ~[a^n]P
    else g (Neg f, rest) ++ unfoldLoaded (Neg f, pr : Star pr : rest)
                                          (Just (Neg f, Star pr : rest))
  g f = error $ "will not happen:" ++ show f
unfoldLoaded  _ _ = error "bad form"

-- | Set of pairwise unions of elements of two sets of sets.
-- Helper function for `unfold`.
(+.+) :: [[a]] -> [[a]] -> [[a]]
(+.+) ls ks = [ l ++ k | l <- ls, k <- ks ]

-- | Eleven local rules (pages 15, 18, 19) and the atomic rule (page 24).
-- TODO: replace local rules with general unfold rules.
ruleFor :: Marked Form -> Maybe RuleApplication
-- The modal rule:
ruleFor (Neg f, Ap x:rest) = Just ("M", 4, [ [(Neg f, rest)]  ], projection x)

-- Nothing to do:
ruleFor (At _       ,[]) = Nothing
ruleFor (Neg (At _) ,[]) = Nothing
ruleFor (Bot        ,[]) = Nothing
ruleFor (Neg Bot    ,[]) = Nothing
-- Single-branch rules without markings:
ruleFor (Neg (Neg f)          , []) = Just ("¬",  1, [ [(f,[])]                         ], noChange)
ruleFor (Con f g              , []) = Just ("∧" , 1, [ [(f,[]), (g,[])]                 ], noChange)

-- Do nothing with unloaded atomic programs, modal rule may only be used on loaded formulas.
ruleFor (Box (Ap _) _      , []) = Nothing
ruleFor (Neg (Box (Ap _) _), []) = Nothing

-- The unfold rule for boxes, used for (*) and other non-atomic programs:
ruleFor (Box alpha f  ,[]) = Just ("□", 2, [ [ (newF, []) | newF <- fs ]
                                           | fs <- unfold (Box alpha f) Nothing    ], noChange)

-- The unfold rule for diamonds, used for (*) and other non-atomic programs:
ruleFor (Neg (Box alpha f) , [] ) = Just ("♢", 3, [ [ (newF, [])
                                                    | newF <- fs ]
                                                  | fs <- unfold (Neg (Box alpha f)) Nothing ], noChange)

-- Loaded formulas without negation at top are badly formed:
ruleFor (At _    , _:_) = error "bad form"
ruleFor (Bot     , _:_) = error "bad form"
ruleFor (Con _ _ , _:_) = error "bad form"
ruleFor (Box _ _ , _:_) = error "bad form"

-- Splitting rules without markings:
ruleFor (Neg (Con f g)   ,[]) = Just ("¬∧", 3, [ [(Neg f,[])]
                                               , [(Neg g,[])]                    ], noChange)

-- The loaded unfold rule for diamonds (will only match when alpha is non-atomic):
ruleFor (Neg f, alpha:rest) = Just ("♢", 3, unfoldLoaded (Neg f, alpha:rest) Nothing, noChange)

-- The loading rule should be here?

-- | Apply change function from a rule to a weighted formulas.
applyW :: (Form -> Maybe Form) -> WForm -> Maybe WForm
applyW fct (Left  f, m) = fmap (\g -> (Left  g, m)) (fct f)
applyW fct (Right f, m) = fmap (\g -> (Right g, m)) (fct f)

weightOf :: WForm -> (Marked Form -> WForm)
weightOf (Left  _, _) = first Left
weightOf (Right _, _) = first Right

unload :: Marked Form -> Form
unload (f, []) = f
unload (Neg f, ps) = Neg $ boxes ps f
unload bad = error $ "bad marked form: " ++ show bad

wUnload :: WForm -> Either Form Form
wUnload (Left f, ps) = Left $ unload (f, ps)
wUnload (Right f, ps) = Right $ unload (f, ps)

isClosedBy :: [WForm] -> [WForm]
isClosedBy wfs
  | Bot `elem` map (unload . collapse) wfs = take 1 [ wf | wf <- wfs, unload (collapse wf) == Bot ]
  | otherwise = [ wf | wf <- wfs, Neg (unload (collapse wf)) `elem` map (unload . collapse) wfs ]
                ++
                [ wf | wf <- wfs, Neg f <- [unload (collapse wf)], f `elem` map (unload . collapse) wfs ]

-- | Loaded-path repeats are end nodes.
-- In MB this is extra condition 6 (page 25).
isEndNodeBy :: [WForm] -> History -> [String]
isEndNodeBy wfsNow history =
  [ show k
  |
  -- There is a predecessor
  (k, (wfsBefore, _)) <- zip [(1 :: Int) ..] history
  -- with the same set of formulas:
  , wfsNow == wfsBefore -- Note: nodes are always sorted, and partitions must match (page 40).
  -- and the path since then is critical, i.e. (M) has been used: -- TODO: but ignore whether At is used for first node of path (= last list element) (Def 13)
  , "M" `elem` map snd (take k history)
  -- and if X is loaded, then the path from s to t is loaded:
  , isLoadedNode wfsNow  `implies` all (isLoadedNode . fst) (take k history)
  ]

extensions :: Tableaux -> [Tableaux]
extensions End             = [End]
extensions (Node wfs oldHistory "" [] [])
  | not (null (isClosedBy wfs))             = [ Node wfs oldHistory CloseR (isClosedBy wfs) [End] ]
  | not (null (isEndNodeBy wfs oldHistory)) = [ Node wfs oldHistory ("lpr") [] [End] ] -- TODO: show number of steps again for lpr ++ concat (isEndNodeBy wfs oldHistory)
  | null (whatshallwedo wfs)                = [ Node wfs oldHistory "" [] [] ] -- we are stuck!
  | otherwise =
      map (\ (wf,(ruleName,_,results,change)) ->
             let
               rest = delete wf wfs
               newHistory = ((wfs, ruleName) :  oldHistory)
               ts = [ Node (nubOrd . sort $ mapMaybe (applyW change) rest ++ newwfs) newHistory "" [] [] -- NOTE: nub and sort!
                    | newwfs <- map (map $ weightOf wf) results ]
             in
               Node wfs oldHistory ruleName [wf] ts)
          (whatshallwedo wfs)
extensions (Node wfs history rule actives ts@(_:_)) =
  [ Node wfs history rule actives ts' | ts' <- pickOneOfEach $ map (filterOneIfAny isClosedTab . extensions) ts ]
-- extensions (Node _  _ rule _     []) = error $ "Rule '" ++ toString rule ++ "' applied but no successors!"

extensionsUpTo :: Int -> Tableaux -> [Tableaux]
extensionsUpTo 0 _ = error "Tableau is too long, giving up!"
extensionsUpTo k t = if extensions t /= [t] then concatMap (extensionsUpTo (k-1)) (extensions t) else [t]

pairWithList :: (a -> [b]) -> [a] -> [(a,b)]
pairWithList f xs = [ (x, y) | x <- xs, y <- f x ]

whatshallwedo :: [WForm] -> [(WForm,RuleApplication)]
whatshallwedo wfs = chooseRule $ pairWithList (availableRules . collapse) wfs where
  availableRules mf =
    maybeToList (ruleFor mf)
    ++
    concat [ markRulesFor mf | not (any isMarked wfs) ]

-- | Choosing a rule. This is reduces the search space for efficiency.
-- We sort and group all possible rule applications by their priority.
-- Within each priority we pick one and postpone all others, with an
-- exception for priority 4 (i.e. (M) and (L+) rules) where always
-- all possible applications must be considered.
chooseRule :: [(WForm,RuleApplication)] -> [(WForm,RuleApplication)]
chooseRule moves
  -- if possible apply one priority 1 rule, ignore all else for now:
  | any ((== 1) . wOf) moves = take 1 (filter ((== 1) . wOf) moves)
  -- else, if possible apply one priority 2 rule, ignore else for now:
  | any ((== 2) . wOf) moves = take 1 (filter ((== 2) . wOf) moves)
  -- else, if possible apply one priority 3 rule, do it, ignore all else for now:
  | any ((== 3) . wOf) moves = take 1 (filter ((== 3) . wOf) moves)
  -- else, if possible apply all priority 4 rules in parallel:
  | any ((<= 4) . wOf) moves = filter ((== 4) . wOf) moves
  | otherwise = []
  where
     wOf (_,(_,priority,_,_))= priority

-- MB Definition 16, page 29
-- "A tableau T is called closed iff all normal free end nodes of T are closed."
isClosedTab :: Tableaux -> Bool
isClosedTab End = False -- check must succeed above the End!
isClosedTab (Node wfs _ _       _ [End]) | isLoadedNode wfs = True
isClosedTab (Node _   _ "✘"     _ [End]) = True
isClosedTab (Node _   _ "lpr"   _ [End]) = False -- loaded path repeat
isClosedTab (Node _   _ rule    _ [End]) = error $ "rule " ++ toString rule ++ " should not create an End node!"
isClosedTab (Node _   _ _       _ []   ) = False
isClosedTab (Node _   _ _       _ ts   ) = all isClosedTab ts

globalSearchLimit :: Int
globalSearchLimit = 200 -- TODO: remove or adjust depending on formula size, see page 20 and 26

-- To prove f --> g, start with proper partition.
-- To prove f, start with  ¬f.
prove :: Form -> Tableaux
prove frm = head $ filterOneIfAny isClosedTab $ extensionsUpTo globalSearchLimit $ case frm of
  (Neg (Con f (Neg g))) -> Node [(Left       f, []), (Right (Neg g), [])] [] "" [] []
  f                     -> Node [(Left $ Neg f, [])                     ] [] "" [] []

provable :: Form -> Bool
provable = isClosedTab . prove

-- | Prove and show the tableau.
proveSlideshow :: Form -> IO ()
proveSlideshow f = do
  let t = prove f
  print $ isClosedTab t
  disp t

tableauFor :: [Form] -> Tableaux
tableauFor fs = head $ filterOneIfAny isClosedTab $ extensionsUpTo globalSearchLimit $ case fs of
  [ Neg (Neg (Con f (Neg g))) ] -> Node [(Left f, []), (Right (Neg g), [])] [] "" [] []
  _anyOtherFormula              -> Node (map (\f -> (Left f, [])) fs)            [] "" [] []

inconsistent :: [Form] -> Bool
inconsistent = isClosedTab . tableauFor

consistent :: [Form] -> Bool
consistent = not . inconsistent

tableauShow :: [Form] -> IO ()
tableauShow fs = do
  let t = tableauFor fs
  print $ isClosedTab t
  disp t
