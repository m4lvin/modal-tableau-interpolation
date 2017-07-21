{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Logic.PDL.Prove.Tree
  ( provable
  , proveSlideshow
  ) where

import Data.GraphViz hiding (Shape(Star))
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List
import Data.Maybe

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

-- | Rules: Given a formula, is their an applicable simple rule?
-- If so, which rule, what replaces the active formula, and does the rest change?
type RuleApplication = (RuleName, RuleWeight, [[Form]], [Form] -> [Form])

ruleFor :: Form -> Maybe RuleApplication
-- Nothing to do:
ruleFor (At _)          = Nothing
ruleFor (Neg (At _))    = Nothing
ruleFor Top             = Nothing
ruleFor Bot             = Nothing
ruleFor (Neg Top)       = Nothing
ruleFor (Neg Bot)       = Nothing
-- Single-branch rules:
ruleFor (Neg (Neg f))           = Just ("¬¬", 1, [ [f]                            ], id)
ruleFor (Neg (Imp f g))         = Just ("¬→", 1, [ [f, Neg g]                     ], id)
ruleFor (Neg (Box (Test f) g))  = Just ("¬?", 1, [ [f, Neg g]                     ], id)
ruleFor (Neg (Box (x:-y) f))    = Just ("¬;", 1, [ [Neg $ Box x (Box y f)]        ], id)
ruleFor (Box (Ap _) _)          = Nothing
ruleFor (Box (Cup x y) f)       = Just ("∪",  1, [ [Box x f, Box y f]             ], id)
ruleFor (Box (x :- y) f)        = Just (";",  1, [ [Box x (Box y f)]              ], id)
-- TODO: Infer NStar here? Why? How to use it later?
ruleFor (Box (Star x) f)        = Just ("*",  1, [ [f, Box x (Box (Star x) f)]   ], id)
-- Splitting rules:
ruleFor (Imp f g)               = Just ("→" , 2, [ [Neg f], [g]                   ], id)
ruleFor (Box (Test f) g)        = Just ("?",  2, [ [Neg f], [g]                   ], id)
ruleFor (Neg (Box (Cup x y) f)) = Just ("¬∪", 2, [ [Neg $ Box x f, Neg $ Box y f] ], id)
ruleFor (Neg (Box (Star x) f))  = Just ("¬*", 2, [ [Neg f], [Neg $ Box x (Box (Star x) f)] ], id)
-- TODO: need a marker here:
ruleFor (Neg (Box x@(Ap _) f))  = Just ("At", 3, [ [Neg f] ], project x) -- die kritische Regel
ruleFor _ = Nothing

applyW :: ([Form] -> [Form]) -> [WForm] -> [WForm]
applyW fct wfs = map Left (fct $ leftsOf wfs) ++ map Right (fct $ rightsOf wfs)

project :: Prog -> [Form] -> [Form]
project x fs = [ f | Box y f <- fs, x == y ]

weightOf :: WForm -> (Form -> WForm)
weightOf (Left  _) = Left
weightOf (Right _) = Right

isClosedNode :: [Form] -> Bool
isClosedNode fs = Bot `elem` fs || Neg Top `elem` fs || any (\f -> Neg f `elem` fs) fs

extend :: Tableaux -> Tableaux
extend End             = End
extend (Node wfs "" [])
  | isClosedNode (collapseList wfs) = Node wfs "✘" [End]
  | otherwise = uncurry (Node wfs) $ case whatshallwedo wfs of
    []     -> (""     ,[])
    ((wf,(therule,_,results,change)):_) -> (therule,ts) where
      rest = delete wf wfs
      ts = [ Node (nub . sort $ applyW change rest ++ newwfs) "" [] | newwfs <- map (map $ weightOf wf) results ]
extend (Node fs rule ts@(_:_)) = Node fs rule [extend t | t <- ts]
extend (Node _  rule@(_:_) []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"

extendUpTo :: Int -> Tableaux -> Tableaux
extendUpTo 0 t = t -- TODO throw error!
extendUpTo k t = extendUpTo (k-1) (extend t)

pairWithMaybe :: (a -> Maybe b) -> [a] -> [(a,b)]
pairWithMaybe f xs = [ (x, fromJust $ f x) | x <- xs, isJust (f x) ]

whatshallwedo :: [WForm] -> [(WForm,RuleApplication)]
whatshallwedo = sortOn (\(_,(_,weight,_,_)) -> weight) . pairWithMaybe (ruleFor . collapse)

isClosedTab :: Tableaux -> Bool
isClosedTab End = True
isClosedTab (Node _ _ ts) = ts /= [] && all isClosedTab ts

-- To prove f, start with  ¬(minLang f) and extend up to 80 steps.
prove :: Form -> Tableaux
prove f = extendUpTo 80 $ Node [Left $ Neg $ minLang f] "" []

provable :: Form -> Bool
provable = isClosedTab . prove

-- | Prove and show the tableau.
proveSlideshow :: Form -> IO ()
proveSlideshow f = do
  let t = prove f
  print $ isClosedTab t
  disp t
