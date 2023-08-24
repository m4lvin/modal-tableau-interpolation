{-# LANGUAGE FlexibleInstances #-}

module Logic.PDL.Prove.Tree where

import Control.Arrow
import Data.Containers.ListUtils (nubOrd)
import Data.GraphViz hiding (Shape(Star))
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List
import Data.Maybe
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

type RuleName = String -- TODO: data RuleName = Con | NegCon | ...  and "¬" etc. with OverloadedStrings

-- We can mark formulas with other formulas
type Marked a = (a, Maybe a)

-- A WForm is weighted (Left/Right) and may have a marking.
type WForm = (Either Form Form, Maybe Form)

collapse :: WForm -> Marked Form
collapse (Left f,m)  = (f,m)
collapse (Right f,m) = (f,m)

isLeft :: WForm -> Bool
isLeft (Left  _, _) = True
isLeft (Right _, _) = False

isLoadedNode :: [WForm] -> Bool
isLoadedNode = any (isJust . snd)

ppWForms :: [WForm] -> [WForm] -> String
ppWForms wfs actives = intercalate ", " (map ppFormA (filter isLeft wfs)) ++ "   |   " ++ intercalate ", " (map ppFormA (filter (not . isLeft) wfs)) where
  ppFormA wf = [ '»' |  wf `elem` actives ] ++ toString (collapse wf) ++ [ '«' |  wf `elem` actives ]

instance DispAble Tableaux where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "."]
    toGraph' pref (Node wfs _ rule actives ts) = do
      node pref [shape PlainText, toLabel $ ppWForms wfs actives]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

type RulePriority = Int -- TODO: use a finite data RuleType = Local | Critical | Marking  or similar?

-- | Rules: Given a formula, is their an applicable rule?
-- If so, which rule, what replaces the active formula, and how do other formulas change and survive?
type RuleApplication = (RuleName, RulePriority, [[Marked Form]], Form -> Maybe Form)

noChange :: Form -> Maybe Form
noChange = Just

without :: Marked Form -> Form -> Marked Form
without (f,Nothing     ) _           = (f, Nothing)
without (f,Just current) toBeRemoved = (f, if current == toBeRemoved then Nothing else Just current)

isMarked :: (a, Maybe Form) -> Bool
isMarked (_,Nothing) = False
isMarked (_,Just _ ) = True

-- | The (M+) rule, marking ¬[a_1]...[a_n]g  with g.
-- This rule has priority 4.
markRulesFor :: Marked Form -> [RuleApplication]
markRulesFor (Neg f, Nothing) = case boxesOf f of
  ([] , _)         -> []
  (_:_, g) -> [ ("M+", 4, [ [ (Neg f, Just g) ] ], noChange) ]
markRulesFor (_, Nothing) = []
markRulesFor (_, Just _)  = [] -- TODO add M- rule here, but not immediately after M+

boxesOf :: Form -> ([Prog], Form)
boxesOf (Box prog nextf) = let (rest,endf) = boxesOf nextf in (prog:rest, endf)
boxesOf endf = ([], endf)

-- Definition 9
projection :: Atom -> Form -> Maybe Form
projection x (Box (Ap y) g) | x == y = Just g
projection _ _                       = Nothing

-- | Unravel the program in the top level modality. Assuming "at least one step".
-- This will be the even newer Definition 10.
-- The two levels of lists are: branches, formulas.
unravel :: Form -> [Form] -> [[Form]]
unravel f0 nforms = -- trace ("unravelled " ++ toString f0 ++ " with nform " ++ toString nform ++ " to " ++ intercalate " ; " (map (intercalate "," . map toString) (g f0))) $
  g f0 where
  -- diamonds:
  g (Neg f) | Neg f `elem` nforms = [ ] -- new way to do condition 4, never create a branch with ~[a^n]P
  g (Neg (Box (Ap ap)     f)) = [[Neg (Box (Ap ap) f)]]
  g (Neg (Box (Cup p1 p2) f)) = g (Neg (Box p1 f)) ++ g (Neg (Box p2 f))
  g (Neg (Box (pa :- pb)  f)) = g (Neg (Box pa (Box pb f)))
  g (Neg (Box (Test tf)   f)) = [ tf : rest | rest <- g (Neg f) ] -- diamond test is not branching.
  g (Neg (Box (Star pr)   f)) = g (Neg f) ++ unravel (Neg (Box pr (Box (Star pr) f)))
                                                     (Neg (Box (Star pr ) f) : nforms)
  -- boxes:
  g f | f `elem` nforms =  [ [] ] -- new way to do condition 2, avoid loops.
  g (Box (Ap ap)     f) = [[Box (Ap ap) f]]
  g (Box (Cup p1 p2) f) = g (Box p1 f) +.+ g (Box p2 f)
  g (Box (pa :- pb)  f) = g (Box pa (Box pb f))
  g (Box (Test tf)   f) = [Neg tf] : g f -- box test is branching.
  g (Box (Star pr)   f) = g f +.+ unravel (Box pr (Box (Star pr) f)) (Box (Star pr) f : nforms)
  -- other formulas, no unraveling:
  g f@(Neg Bot) = [[ f ]]
  g f@(Neg (At _)) = [[ f ]]
  g f@(Neg (Neg _)) = [[ f ]]
  g f@(Neg (Con _ _)) = [[ f ]]
  g f@Bot = [[ f ]]
  g f@(At _) = [[ f ]]
  g f@(Con _ _) = [[ f ]]

-- | Set of pairwise unions of elements of two sets of sets.
-- Helper function for `unravel`.
(+.+) :: [[a]] -> [[a]] -> [[a]]
(+.+) ls ks = [ l ++ k | l <- ls, k <- ks ]

-- | Eleven local rules (pages 15, 18, 19) and the atomic rule (page 24).
ruleFor :: Marked Form -> Maybe RuleApplication
-- Nothing to do:
ruleFor (At _       ,_) = Nothing
ruleFor (Neg (At _) ,_) = Nothing
ruleFor (Bot        ,_) = Nothing
ruleFor (Neg Bot    ,_) = Nothing
-- Single-branch rules:
-- Note: page 19 says that (only) the local rules ¬u, ¬; ¬n and ¬? should be applied to marked formulas.
ruleFor (Neg (Neg f)     ,Nothing) = Just ("¬",  1, [ [(f,Nothing)]                            ], noChange)
ruleFor (Neg (Neg _)     ,Just _ ) = Nothing
ruleFor (Con f g         ,Nothing) = Just ("∧" , 1, [ [(f,Nothing), (g,Nothing)]               ], noChange)
ruleFor (Con _ _         ,Just _ ) = Nothing
ruleFor (Neg (Box (Test f) g)  ,m) = Just ("¬?", 1, [ [(f,Nothing), (Neg g,m) `without` g ]    ], noChange)
ruleFor (Neg (Box (x:-y) f)    ,m) = Just ("¬;", 1, [ [(Neg $ Box x (Box y f),m)]              ], noChange)
ruleFor (Box (Ap _) _          ,_) = Nothing
ruleFor (Box (Cup x y) f ,Nothing) = Just ("∪",  1, [ [(Box x f, Nothing), (Box y f, Nothing)] ], noChange)
ruleFor (Box (Cup _ _) _ ,Just _ ) = Nothing
ruleFor (Box (x :- y) f  ,Nothing) = Just (";",  1, [ [(Box x (Box y f),Nothing)]              ], noChange)
ruleFor (Box (_ :- _) _  ,Just _ ) = Nothing
-- The (*) rule, using unravel:
ruleFor (Box (Star x) f, Nothing) = Just ("*", 2, [ [ (newF, Nothing) | newF <- fs ] -- look ma, no f
                                                  | fs <- unravel (Box (Star x) f) [] ] , noChange)
ruleFor (Box (Star _) _  ,Just _ ) = Nothing -- (*) maye not be applied to marked formulas (before Def 13)
-- Splitting rules:
ruleFor (Neg (Con f g)   ,Nothing) = Just ("¬∧", 3, [ [(Neg f,Nothing)]
                                                    , [(Neg g,Nothing)]                    ], noChange)
ruleFor (Neg (Con _ _)   ,Just _ ) = Nothing
-- TODO: Can we delete this case, which was for NStar and extra condition 2 before?
-- ruleFor (Box (Test f) (Box (Star _) _)  ,Nothing) = Just ("?",  3, [ [(Neg f,Nothing)]
--                                                                    , []                   ], noChange)
ruleFor (Box (Test f) g                  ,Nothing) = Just ("?",  3, [ [(Neg f,Nothing)]
                                                                    , [(g,Nothing)]        ], noChange)
ruleFor (Box (Test _) _  ,Just _ ) = Nothing
ruleFor (Neg (Box (Cup x y) f),m ) = Just ("¬∪", 3, [ [(Neg $ Box x f,m)]
                                                    , [(Neg $ Box y f,m)]                  ], noChange)
-- The (¬*) rule, also using unravel:
ruleFor (Neg (Box (Star x) f) ,m ) = Just ("¬*", 3, [ [ case m of
                                                          Just g -> if newF == Neg g then (newF, Nothing) else (newF, m)
                                                          Nothing -> (newF, m)
                                                      | newF <- fs ]
                                                    | fs <- unravel (Neg (Box (Star x) f)) [] ], noChange)
-- The critical rule:
ruleFor (Neg (Box (Ap x) f), Just mf) = Just ("At", 4, [ [(Neg f, Just mf) `without` f]   ], projection x)
ruleFor (Neg (Box (Ap _) _), Nothing) = Nothing

-- | Apply change function from a rule to a weighted formulas.
applyW :: (Form -> Maybe Form) -> WForm -> Maybe WForm
applyW fct (Left  f, m) = fmap (\g -> (Left  g, m)) (fct f)
applyW fct (Right f, m) = fmap (\g -> (Right g, m)) (fct f)

weightOf :: WForm -> (Marked Form -> WForm)
weightOf (Left  _, _) = first Left
weightOf (Right _, _) = first Right

isClosedBy :: [WForm] -> [WForm]
isClosedBy wfs
  -- REMOVE? -- | not (all (isNormal . fst . collapse) wfs) = [] -- Never close n-nodes (note after Definition 12)
  | Bot `elem` map (fst . collapse) wfs = take 1 [ wf | wf <- wfs, fst (collapse wf) == Bot ]
  | otherwise = [ wf | wf <- wfs, Neg (fst (collapse wf)) `elem` map (fst . collapse) wfs ]
                ++
                [ wf | wf@(Left (Neg f), _) <- wfs, f `elem` map (fst . collapse) wfs ]
                ++
                [ wf | wf@(Right (Neg f), _) <- wfs, f `elem` map (fst . collapse) wfs ]

-- | End nodes due to to extra condition 6 (page 25).
isEndNodeBy :: [WForm] -> History -> [String]
isEndNodeBy wfsNow history =
  [ show k
  |
  -- There is a predecessor
  (k, (wfsBefore, _)) <- zip [(1 :: Int) ..] history
  -- with the same set of formulas:
  , wfsNow == wfsBefore -- Note: nodes are always sorted, and partitions must match (page 40).
  -- and the path since then is critical, i.e. (At) has been used: -- TODO: but ignore whether At is used for first node of path (= last list element) (Def 13)
  , "At" `elem` map snd (take k history)
  -- and if X is loaded, then the path from s to t is loaded:
  , isLoadedNode wfsNow  `implies` all (isLoadedNode . fst) (take k history)
  ]

extensions :: Tableaux -> [Tableaux]
extensions End             = [End]
extensions (Node wfs oldHistory "" [] [])
  | not (null (isClosedBy wfs))             = [ Node wfs oldHistory "✘"                                          (isClosedBy wfs)   [End] ]
  | not (null (isEndNodeBy wfs oldHistory)) = [ Node wfs oldHistory ("6: " ++ show (isEndNodeBy wfs oldHistory)) []                 [End] ]
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
extensions (Node _  _ []         (_:_) []) = error "Cannot have active formulas without a rule!"
extensions (Node _  _ rule@(_:_) _     []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"

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
-- exception for priority 4 (i.e. (At) and (M+) rules) where always
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

-- Definition 16, page 29
-- "A tableau T is called closed iff all normal free end nodes of T are closed."
isClosedTab :: Tableaux -> Bool
isClosedTab End = False -- check must succeed above the End!
isClosedTab (Node wfs _ _       _ [End]) | isLoadedNode wfs = True
isClosedTab (Node _   _ "✘"     _ [End]) = True
isClosedTab (Node _   _ "4"     _ [End]) = False -- end node, see page 15
isClosedTab (Node _   _ ('6':_) _ [End]) = False -- normal and free, but might be not closed
isClosedTab (Node _   _ rule    _ [End]) = error $ "rule " ++ rule ++ " should not create an End node!"
isClosedTab (Node _   _ _       _ []   ) = False
isClosedTab (Node _   _ _       _ ts   ) = all isClosedTab ts

globalSearchLimit :: Int
globalSearchLimit = 200 -- TODO: remove or adjust depending on formula size, see page 20 and 26

-- To prove f --> g, start with proper partition.
-- To prove f, start with  ¬f.
prove :: Form -> Tableaux
prove frm = head $ filterOneIfAny isClosedTab $ extensionsUpTo globalSearchLimit $ case frm of
  (Neg (Con f (Neg g))) -> Node [(Left       f, Nothing), (Right (Neg g), Nothing)] [] "" [] []
  f                     -> Node [(Left $ Neg f, Nothing)                          ] [] "" [] []

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
  [ Neg (Neg (Con f (Neg g))) ] -> Node [(Left f, Nothing), (Right (Neg g), Nothing)] [] "" [] []
  _anyOtherFormula              -> Node (map (\f -> (Left f, Nothing)) fs)            [] "" [] []

inconsistent :: [Form] -> Bool
inconsistent = isClosedTab . tableauFor

consistent :: [Form] -> Bool
consistent = not . inconsistent

tableauShow :: [Form] -> IO ()
tableauShow fs = do
  let t = tableauFor fs
  print $ isClosedTab t
  disp t
