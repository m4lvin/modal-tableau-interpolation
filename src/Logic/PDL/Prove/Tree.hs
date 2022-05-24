{-# LANGUAGE FlexibleInstances #-}

module Logic.PDL.Prove.Tree
  ( provable
  , inconsistent
  , prove
  , proveSlideshow
  , isClosedTab
  , tableauShow
  , tableauFor
  ) where

import Control.Arrow
import Data.GraphViz hiding (Shape(Star))
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List
import Data.Maybe
import System.IO.Unsafe (unsafePerformIO)
import System.Console.ANSI

import Logic.Internal
import Logic.PDL

-- | A Tablaux is either a node or an end marker.
data Tableaux = Node -- ^ A node contains:
                [WForm]    -- ^ current list of weighted (and possibly marked) formulas
                History    -- ^ previous formula lists and rules up to the root
                RuleName   -- ^ name of the rule that is applied here
                [WForm]    -- ^ list of *active* wformulas to which the rule is applied
                [Tableaux] -- ^ list of child nodes
              | End
  deriving (Eq,Ord,Show)

-- | A history is a list of pairs of a list of weighted formulas and the rule used.
-- Note: head of this list is the immediate predecessor, last element is the root!
type History = [([WForm],RuleName)]

type RuleName = String -- FIXME: use data RuleName = Con NegCon etc.

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

isNormalNode :: [WForm] -> Bool
isNormalNode = all (isNormal . fst. collapse)

ppWForms :: [WForm] -> [WForm] -> String
ppWForms wfs actives = intercalate ", " (map ppFormA (filter isLeft wfs)) ++ "   |   " ++ intercalate ", " (map ppFormA (filter (not . isLeft) wfs)) where
  ppFormA wf = [ '»' |  wf `elem` actives ] ++ toString (collapse wf) ++ [ '«' |  wf `elem` actives ]

instance DispAble Tableaux where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "✘"]
    toGraph' pref (Node wfs _ rule actives ts) = do
      node pref [shape PlainText, toLabel $ ppWForms wfs actives]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

type RuleWeight = Int -- IDEA: use data RuleType = Local | Critical | Marking  or similar?

-- | Rules: Given a formula, is their an applicable rule?
-- If so, which rule, what replaces the active formula, and how do other formulas change and survive?
type RuleApplication = (RuleName, RuleWeight, [[Marked Form]], Form -> Maybe Form)

noChange :: Form -> Maybe Form
noChange = Just

without :: Marked Form -> Form -> Marked Form
without (f,Nothing     ) _           = (f, Nothing)
without (f,Just current) toBeRemoved = (f, if current == toBeRemoved then Nothing else Just current)

isMarked :: (a, Maybe Form) -> Bool
isMarked (_,Nothing) = False
isMarked (_,Just _ ) = True

-- Mark  ¬[a_1]...[a_n]g  with  g.
markRulesFor :: Marked Form -> [RuleApplication]
markRulesFor (Neg f, Nothing) = case boxesOf f of
  ([] , _)         -> []
  (_:_, g) -> [ ("M+", 0, [ [ (Neg f, Just g) ] ], noChange) ]
markRulesFor (_, Nothing) = []
markRulesFor (_, Just _)  = [] -- TODO add M- rule here, but not immediately after M+

boxesOf :: Form -> ([Prog], Form)
boxesOf (Box prog nextf) = let (rest,endf) = boxesOf nextf in (prog:rest, endf)
boxesOf endf = ([], endf)

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
-- The (n) rule (note extra condition 1 below)
ruleFor (Box (Star x) f  ,Nothing) = Just ("n",  2, [ [(f,Nothing), (Box x (Box (NStar x) f),Nothing)] ], noChange)
ruleFor (Box (Star _) _  ,Just _ ) = Nothing -- (n) maye not be applied to marked formulas.
-- Splitting rules:
ruleFor (Neg (Con f g)   ,Nothing) = Just ("¬∧", 3, [ [(Neg f,Nothing)]
                                                    , [(Neg g,Nothing)]                    ], noChange)
ruleFor (Neg (Con _ _)   ,Just _ ) = Nothing
ruleFor (Box (Test f) g  ,Nothing) = Just ("?",  3, [ [(Neg f,Nothing)]
                                                    , [(g,Nothing)]                        ], noChange)
ruleFor (Box (Test _) _  ,Just _ ) = Nothing
ruleFor (Neg (Box (Cup x y) f),m ) = Just ("¬∪", 3, [ [(Neg $ Box x f,m)]
                                                    , [(Neg $ Box y f,m)]                  ], noChange)
ruleFor (Neg (Box (Star x) f) ,m ) = Just ("¬n", 3, [ [(Neg f,m) `without` f]
                                                    , [(Neg $ Box x (Box (NStar x) f),m)]  ], noChange)
-- The critical rule:
ruleFor (Neg (Box (Ap x) f), Just mf) = Just ("At", 4, [ [(Neg f, Just mf) `without` f]   ], projection) where
  projection :: Form -> Maybe Form -- Definition 9
  projection (Box (Ap y) g) | x == y = Just g
  projection _                       = Nothing
ruleFor (Neg (Box (Ap _) _), Nothing) = Nothing
ruleFor (Neg (Box (NStar _) _)    ,_) = Nothing -- per condition 4 no rule may be applied here - see page 19.
ruleFor (Box (NStar _) _          ,_) = Nothing -- FIXME: should this be an error? can there be Box NStar nodes at all?

extraNewFormChanges :: RuleApplication -> RuleApplication
extraNewFormChanges (ruleName, ruleWeight, newFormLists, changeFunction) =
  (ruleName, ruleWeight, map (map con1backToStar) newFormLists, changeFunction)
  where
  -- extra condition 1
  con1backToStar :: Marked Form -> Marked Form
  con1backToStar (f@(Box (Ap _) _)      ,m) = (nToStar f, m)
  con1backToStar (f@(Neg (Box (Ap _) _)),m) = (nToStar f, m)
  con1backToStar mf = mf

-- | Apply change function from a rule to a weighted formulas.
applyW :: (Form -> Maybe Form) -> WForm -> Maybe WForm
applyW fct (Left  f, m) = fmap (\g -> (Left  g, m)) (fct f)
applyW fct (Right f, m) = fmap (\g -> (Right g, m)) (fct f)

weightOf :: WForm -> (Marked Form -> WForm)
weightOf (Left  _, _) = first Left
weightOf (Right _, _) = first Right

isClosedBecause :: [WForm] -> [WForm]
isClosedBecause wfs =
  [ wf | wf <- wfs, fst (collapse wf) == Bot ]
  ++
  [ wf | wf <- wfs, Neg (fst (collapse wf)) `elem` map (fst . collapse) wfs ]

-- | Detect end nodes due to to extra condition 6.
isEndNodeBy :: [WForm] -> History -> [String]
isEndNodeBy wfsNow history =
  [ show k
  | isNormalNode wfsNow
  , (k, (wfsBefore, _)) <- zip [(1 :: Int) ..] history
  -- There is a predecessor
  -- with the same set of formulas:
  , wfsNow == wfsBefore -- Note: nodes are always sorted, and partitions must match (page 40).
  -- and the path since then is critical, i.e. (At) has been used: -- TODO: but ignore whether At is used for first node of path (= last list element) (Def 13)
  , "At" `elem` map snd (take k history)
  -- new version:
  -- for each node on the path:  it is loaded *iff* the current node is loaded:
  , all ((any isMarked wfsNow ==) . any isMarked . fst) (take k history) --- now <a*>[a]p yields an infinite tableau :-/

  -- alternative versions/readings of condition 6:
  -- - for each node on the path:  it is loaded *iff* the current node is loaded:
  -- , all ((any isMarked wfsNow ==) . any isMarked . fst) (take k history) --- <a*>[a]p yields an infinite tableau :-/
  -- - all nodes on the path  are loaded  *iff*  the current node is loaded:
  -- , all (any isMarked . fst) (take k history) == any isMarked wfsNow -- with this <a*>[a]¬p is valid :-(
  ]

-- | End nodes due to extra condition 4.
isNotNStarNodeBecause :: [WForm] -> [WForm]
isNotNStarNodeBecause = filter (isNotNStar . (fst . collapse)) where
  isNotNStar (Neg (Box (NStar _) _)) = True
  isNotNStar _ = False

extensions :: Tableaux -> [Tableaux]
extensions End             = [End]
extensions (Node wfs oldHistory "" [] [])
  | not (null (isClosedBecause wfs))        = [ Node wfs oldHistory "✘" (isClosedBecause wfs)                       [End] ]
  | not (null (isEndNodeBy wfs oldHistory)) = [ Node wfs oldHistory ("6: " ++ show (isEndNodeBy wfs oldHistory)) [] [End] ]
  | not (null (isNotNStarNodeBecause wfs))  = [ Node wfs oldHistory "4" (isNotNStarNodeBecause wfs)                 [End] ]
  | null (whatshallwedo wfs)                = [ Node wfs oldHistory "" [] [] ] -- we are stuck!
  | otherwise =
      map (\ (wf,(ruleName,_,results,change)) ->
             let
               rest = delete wf wfs
               newHistory = ((wfs, ruleName) :  oldHistory)
               ts = [ Node (nub . sort $ mapMaybe (applyW change) rest ++ newwfs) newHistory "" [] [] -- NOTE: nub and sort!
                    | newwfs <- map (map $ weightOf wf) results ]
             in
               Node wfs oldHistory ruleName [wf] ts)
          (whatshallwedo wfs)
extensions (Node wfs history rule actives ts@(_:_)) =
  [ Node wfs history rule actives ts' | ts' <- pickOneOfEach $ map (filterOneIfAny isClosedTab . extensions) ts ]
extensions (Node _  _ []         (_:_) []) = error "Cannot have active formulas without a rule!"
extensions (Node _  _ rule@(_:_) _     []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"

extensionsUpTo :: Int -> Tableaux -> [Tableaux]
extensionsUpTo 0 t = unsafePerformIO (let msg = "   [ !!! Tableau is too long, giving up !!! ]   "
                                      in putStr msg >> cursorBackward (length msg) >> return [t]) -- TODO error or [] or Nothing?!
extensionsUpTo k t = if extensions t /= [t] then concatMap (extensionsUpTo (k-1)) (extensions t) else [t]

pairWithList :: (a -> [b]) -> [a] -> [(a,b)]
pairWithList f xs = [ (x, y) | x <- xs, y <- f x ]

whatshallwedo :: [WForm] -> [(WForm,RuleApplication)]
whatshallwedo wfs = chooseRule $ pairWithList (map extraNewFormChanges . availableRules . collapse) wfs where
  availableRules mf =
    maybeToList (ruleFor mf)
    ++
    concat [ markRulesFor mf | not (any isMarked wfs) ]

-- | Choosing a rule.
-- There might be multiple applicable rules of the same or different weight.
-- (or lower is for marking rules which have 0)
chooseRule :: [(WForm,RuleApplication)] -> [(WForm,RuleApplication)]
chooseRule moves
  -- if possible apply one weight 1 rule, ignore all larger for now:
  | any ((== 1) . wOf) moves = take 1 $ filter ((<= 1) . wOf) moves
  -- else, if possible apply one weight 2 rule, ignore all larger for now:
  | any ((== 2) . wOf) moves = take 1 $ filter ((<= 2) . wOf) moves
  -- else, if possible apply one weight 3 rule, do it, ignore all larger for now:
  | any ((== 3) . wOf) moves = take 1 $ filter ((<= 3) . wOf) moves
  -- else, if possible apply all weight 4 or lower rules in parallel:
  | any ((<= 4) . wOf) moves = filter ((<= 4) . wOf) moves
  | otherwise = []
  where
     wOf (_,(_,weight,_,_))= weight

isClosedTab :: Tableaux -> Bool
isClosedTab End = True
isClosedTab (Node _ _ _ _ ts) = ts /= [] && all isClosedTab ts

globalSearchLimit :: Int
globalSearchLimit = 30 -- TODO: adjust depending on formula size, see page 20 and 26

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
  _                             -> Node (map (\f -> (Left f, Nothing)) fs)            [] "" [] []

inconsistent :: [Form] -> Bool
inconsistent = isClosedTab . tableauFor

tableauShow :: [Form] -> IO ()
tableauShow fs = do
  let t = tableauFor fs
  print $ isClosedTab t
  disp t
