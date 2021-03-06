{-# LANGUAGE FlexibleInstances #-}

module Logic.PDL.Prove.Tree
  ( provable
  , proveSlideshow
  ) where

import Data.GraphViz hiding (Shape(Star))
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List
import Data.Maybe
import System.IO.Unsafe (unsafePerformIO)

import Logic.Internal
import Logic.PDL

-- | Nodes are lists of weighted formulas, together
-- with a rule that was applied to get the children.
data Tableaux = Node [WForm] RuleName [Tableaux] | End
  deriving (Eq,Ord,Show)

type RuleName = String

-- We can mark formuals with other formulas
type Marked a = (a, Maybe a)

-- A WForm is weighted (Left/Right) and may have a marking.
type WForm = (Either Form Form, Maybe Form)

collapse :: WForm -> Marked Form
collapse (Left f,m)  = (f,m)
collapse (Right f,m) = (f,m)

collapseList :: [WForm] -> [Marked Form]
collapseList = map collapse

leftsOf, rightsOf :: [WForm] -> [Marked Form]
leftsOf  wfs = [(f,m) | (Left f,m) <- wfs]
rightsOf wfs = [(f,m) | (Right f,m) <- wfs]

ppWForms :: [WForm] -> String
ppWForms wfs = toStrings (leftsOf wfs) ++ "  |  " ++ toStrings (rightsOf wfs)

instance DispAble Tableaux where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "✘"]
    toGraph' pref (Node wfs rule ts) = do
      node pref [shape PlainText, toLabel $ ppWForms wfs]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

type RuleWeight = Int

-- | Rules: Given a formula, is their an applicable rule?
-- If so, which rule, what replaces the active formula, and how do other formulas change and survive?
type RuleApplication = (RuleName, RuleWeight, [[Marked Form]], Form -> Maybe Form)

noChange :: Form -> Maybe Form
noChange = Just

without :: Marked Form -> Form -> Marked Form
without (f,Nothing) _ = (f, Nothing)
without (f,Just current) toBeRemoved = (f, if current == toBeRemoved then Nothing else Just current)


-- TODO rule which allows to add markers!!

ruleFor :: Marked Form -> Maybe RuleApplication
-- Nothing to do:
ruleFor (At _,_)          = Nothing
ruleFor (Neg (At _),_)    = Nothing
ruleFor (Bot,_)           = Nothing
ruleFor (Neg Bot,_)       = Nothing
-- Single-branch rules:
ruleFor (Neg (Neg f)          ,m) = Just ("¬¬", 1, [ [(f,m)]                                ], noChange)
ruleFor (Con f g              ,m) = Just ("^" , 1, [ [(f,m), (g,m)]                         ], noChange)
ruleFor (Neg (Box (Test f) g) ,m) = Just ("¬?", 1, [ [(f,Nothing), (Neg g,m) `without` f ]  ], noChange)
ruleFor (Neg (Box (x:-y) f)   ,m) = Just ("¬;", 1, [ [(Neg $ Box x (Box y f),m)]            ], noChange)
ruleFor (Box (Ap _) _         ,_) = Nothing
ruleFor (Box (Cup x y) f      ,m) = Just ("∪",  1, [ [(Box x f, m), (Box y f, m)]           ], noChange)
ruleFor (Box (x :- y) f       ,m) = Just (";",  1, [ [(Box x (Box y f),m)]                  ], noChange)
-- The (n) rule infers NStar, but not of x is atomic:
-- TODO: assumption for now: only may be applied if there is a marking!?
ruleFor (Box (Star x) f       ,m) = Just ("n",  1, [ [(f,m), (Box x (Box (starOperator x) f),m)] ], noChange) where
  starOperator = if isAtomic x then Star else NStar -- per condition 1 -- FIXME this should also replace NStar with Star within f, I think? -- TODO remove this, condition is done later!
-- Splitting rules:
ruleFor (Neg (Con f g)        ,m) = Just ("¬^", 2, [ [(Neg f,m)], [(Neg g,m)]               ], noChange)
ruleFor (Box (Test f) g       ,m) = Just ("?",  2, [ [(Neg f,m)], [(g,m)]                   ], noChange) -- marker also on Test?
ruleFor (Neg (Box (Cup x y) f),m) = Just ("¬∪", 2, [ [(Neg $ Box x f,m)], [(Neg $ Box y f,m)] ], noChange)
ruleFor (Neg (Box (Star x) f) ,m) = Just ("¬n", 2, [ [(Neg f,m) `without` f], [(Neg $ Box x (Box (Star x) f),m)] ], noChange)
-- TODO: need a marker here:
ruleFor (Neg (Box (Ap x) f),m)    = Just ("At", 3, [ [(Neg f, m) `without` f] ], projection) where -- the critical rule
  projection :: Form -> Maybe Form
  projection (Box (Ap y) g) | x == y = Just g
  projection _                       = Nothing
ruleFor (Neg (Box (NStar _) _),_) = Nothing -- per condition 4 no rule may be applied here. See Borzechowski page 19.
ruleFor mf@(Box (NStar _) _   ,_) = error $ "I have no rule for this, There should never be an NStar node: " ++ show mf

extraConditions :: RuleApplication -> RuleApplication
extraConditions (ruleName, ruleWeight, newFormLists, changeFunction) = (ruleName, ruleWeight, map (map con1backToStar) newFormLists, changeFunction) where
  con1backToStar :: Marked Form -> Marked Form
  con1backToStar (f@(Box (Ap _) _)      ,m) = (nToStar f, m)
  con1backToStar (f@(Neg (Box (Ap _) _)),m) = (nToStar f, m)
  con1backToStar mf = mf

-- | Apply change function from a rule to a weighted formulas.
applyW :: (Form -> Maybe Form) -> WForm -> Maybe WForm
applyW fct (Left  f, m) = fmap (\g -> (Left  g, m)) (fct f)
applyW fct (Right f, m) = fmap (\g -> (Right g, m)) (fct f)

weightOf :: WForm -> (Marked Form -> WForm)
weightOf (Left  _, _) = \(f,m) -> (Left  f, m)
weightOf (Right _, _) = \(f,m) -> (Right f, m)

isClosedNode :: [Marked Form] -> Bool
isClosedNode mfs = Bot `elem` map fst mfs || any (\(f,_) -> Neg f `elem` map fst mfs) mfs
-- TODO should we also check extra condition 6 or 7 here??

extend :: Tableaux -> Tableaux
extend End             = End
extend (Node wfs "" [])
  | isClosedNode (collapseList wfs) = Node wfs "✘" [End]
  | otherwise = uncurry (Node wfs) $ case whatshallwedo wfs of
    []     -> (""     ,[])
    ((wf,(therule,_,results,change)):_) -> (therule,ts) where
      rest = delete wf wfs
      ts = [ Node (nub . sort $ mapMaybe (applyW change) rest ++ newwfs) "" [] | newwfs <- map (map $ weightOf wf) results ]
extend (Node fs rule ts@(_:_)) = Node fs rule [extend t | t <- ts]
extend (Node _  rule@(_:_) []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"

extendUpTo :: Int -> Tableaux -> Tableaux
extendUpTo 0 t = unsafePerformIO (putStrLn "\n ERROR too many steps! \n" >> return t) -- TODO throw error!
extendUpTo k t = if extend t /= t then extendUpTo (k-1) (extend t) else t

pairWithMaybe :: (a -> Maybe b) -> [a] -> [(a,b)]
pairWithMaybe f xs = [ (x, fromJust $ f x) | x <- xs, isJust (f x) ]

whatshallwedo :: [WForm] -> [(WForm,RuleApplication)]
whatshallwedo = sortOn (\(_,(_,weight,_,_)) -> weight) . pairWithMaybe (fmap extraConditions . ruleFor . collapse)

isClosedTab :: Tableaux -> Bool
isClosedTab End = True
isClosedTab (Node _ _ ts) = ts /= [] && all isClosedTab ts

-- To prove f --> g, start with proper partition.
-- To prove f, start with  ¬f.
prove :: Form -> Tableaux
prove (Neg (Con f (Neg g))) = extendUpTo 40 $ Node [(Left       f, Nothing), (Right (Neg g), Nothing)] "" []
prove f                     = extendUpTo 40 $ Node [(Left $ Neg f, Nothing)                          ] "" []

provable :: Form -> Bool
provable = isClosedTab . prove

-- | Prove and show the tableau.
proveSlideshow :: Form -> IO ()
proveSlideshow f = do
  let t = prove f
  print $ isClosedTab t
  disp t
