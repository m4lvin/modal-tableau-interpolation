{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

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

type WForm = Either Form Form

collapse :: WForm -> Form
collapse (Left f)  = f
collapse (Right f) = f

collapseList :: [Either Form Form] -> [Form]
collapseList = map collapse

leftsOf, rightsOf :: [WForm] -> [Form]
leftsOf  wfs = [f | Left f <- wfs]
rightsOf wfs = [f | Right f <- wfs]

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
type RuleApplication = (RuleName, RuleWeight, [[Form]], Form -> Maybe Form)

noChange :: Form -> Maybe Form
noChange = Just

ruleFor :: Form -> Maybe RuleApplication
-- Nothing to do:
ruleFor (At _)          = Nothing
ruleFor (Neg (At _))    = Nothing
ruleFor Bot             = Nothing
ruleFor (Neg Bot)       = Nothing
-- Single-branch rules:
ruleFor (Neg (Neg f))           = Just ("¬¬", 1, [ [f]                            ], noChange)
ruleFor (Con f g)               = Just ("^" , 1, [ [f, g]                         ], noChange)
ruleFor (Neg (Box (Test f) g))  = Just ("¬?", 1, [ [f, Neg g]                     ], noChange)
ruleFor (Neg (Box (x:-y) f))    = Just ("¬;", 1, [ [Neg $ Box x (Box y f)]        ], noChange)
ruleFor (Box (Ap _) _)          = Nothing
ruleFor (Box (Cup x y) f)       = Just ("∪",  1, [ [Box x f, Box y f]             ], noChange)
ruleFor (Box (x :- y) f)        = Just (";",  1, [ [Box x (Box y f)]              ], noChange)
-- The (n) rule infers NStar, but not of x is atomic:
ruleFor (Box (Star x) f)        = Just ("n",  1, [ [f, Box x (Box (starOperator x) f)]    ], noChange) where
  starOperator = if isAtomic x then Star else NStar -- per condition 1 -- FIXME this should also replace NStar with Star within f, I think?
-- Splitting rules:
ruleFor (Neg (Con f g))         = Just ("¬^", 2, [ [Neg f], [Neg g]               ], noChange)
ruleFor (Box (Test f) g)        = Just ("?",  2, [ [Neg f], [g]                   ], noChange)
ruleFor (Neg (Box (Cup x y) f)) = Just ("¬∪", 2, [ [Neg $ Box x f, Neg $ Box y f] ], noChange)
ruleFor (Neg (Box (Star x) f))  = Just ("¬*", 2, [ [Neg f], [Neg $ Box x (Box (Star x) f)] ], noChange)
-- TODO: need a marker here:
ruleFor (Neg (Box (Ap x) f))    = Just ("At", 3, [ [Neg f] ], projectionWith x) -- the critical rule
ruleFor (Neg (Box (NStar _) _)) = Nothing -- per condition 4 no rule may be applied here. See Borzechowski page 19.
ruleFor f@(Box (NStar _) _)     = error $ "I have no rule for this, There should never be an NStar node: " ++ show f

extraConditions :: RuleApplication -> RuleApplication
extraConditions (ruleName, ruleWeight, newFormLists, changeFunction) = (ruleName, ruleWeight, map (map con1backToStar) newFormLists, changeFunction) where
  con1backToStar :: Form -> Form
  con1backToStar f@(Box (Ap _) _) = nToStar f
  con1backToStar f@(Neg (Box (Ap _) _)) = nToStar f
  con1backToStar f = f

-- | Apply change function from a rule to a weighted formulas.
applyW :: (Form -> Maybe Form) -> WForm -> Maybe WForm
applyW fct (Left  f) = fmap Left  (fct f)
applyW fct (Right f) = fmap Right (fct f)

projectionWith :: Atom -> Form -> Maybe Form
projectionWith x (Box (Ap y) f) | x == y = Just f
projectionWith _ _                       = Nothing

weightOf :: WForm -> (Form -> WForm)
weightOf (Left  _) = Left
weightOf (Right _) = Right

isClosedNode :: [Form] -> Bool
isClosedNode fs = Bot `elem` fs || any (\f -> Neg f `elem` fs) fs

extend :: Tableaux -> Tableaux
extend End             = End
extend (Node wfs "" [])
  | isClosedNode (collapseList wfs) = Node wfs "✘" [End]
  | otherwise = uncurry (Node wfs) $ case whatshallwedo wfs of
    []     -> (""     ,[])
    ((wf,(therule,_,results,change)):_) -> (therule,ts) where
      rest = delete wf wfs
      ts = [ Node (nub . sort $ catMaybes (map (applyW change) rest) ++ newwfs) "" [] | newwfs <- map (map $ weightOf wf) results ]
extend (Node fs rule ts@(_:_)) = Node fs rule [extend t | t <- ts]
extend (Node _  rule@(_:_) []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"

extendUpTo :: Int -> Tableaux -> Tableaux
extendUpTo 0 t = unsafePerformIO (putStrLn "\n ERROR too many steps! \n" >> return t) -- TODO throw error!
extendUpTo k t = extendUpTo (k-1) (extend t)

pairWithMaybe :: (a -> Maybe b) -> [a] -> [(a,b)]
pairWithMaybe f xs = [ (x, fromJust $ f x) | x <- xs, isJust (f x) ]

whatshallwedo :: [WForm] -> [(WForm,RuleApplication)]
whatshallwedo = sortOn (\(_,(_,weight,_,_)) -> weight) . pairWithMaybe (fmap (extraConditions) . ruleFor . collapse)

isClosedTab :: Tableaux -> Bool
isClosedTab End = True
isClosedTab (Node _ _ ts) = ts /= [] && all isClosedTab ts

-- To prove f, start with  ¬(minLang f) and extend up to 40 steps.
-- To prove f --> g, start with proper partition.
prove :: Form -> Tableaux
prove (Neg (Con f (Neg g))) = extendUpTo 40 $ Node [Left  f, Right (Neg g)] "" []
prove f                     = extendUpTo 40 $ Node [Left $ Neg f          ] "" []

provable :: Form -> Bool
provable = isClosedTab . prove

-- | Prove and show the tableau.
proveSlideshow :: Form -> IO ()
proveSlideshow f = do
  let t = prove f
  print $ isClosedTab t
  disp t
