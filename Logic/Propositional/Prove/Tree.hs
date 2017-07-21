{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- A Tableaux prover.
-- Nodes in the trees are lists of formulas with weights, together
-- with a rule that was applied to get the children.

module Logic.Propositional.Prove.Tree where

import Data.GraphViz
import Data.GraphViz.Types.Monadic
import Data.List

import Logic.Internal
import Logic.Propositional

data Tableaux = Node [WForm] RuleName [Tableaux] | End
  deriving (Eq,Ord,Show)

type RuleName = String

type WForm = Either Form Form

data Side = L | R

collapse :: WForm -> Form
collapse (Left f)  = f
collapse (Right f) = f

collapseList :: [Either Form Form] -> [Form]
collapseList = map collapse

leftsOf, rightsOf :: [WForm] -> [Form]
leftsOf  wfs = [f | Left f <- wfs]
rightsOf wfs = [f | Right f <- wfs]

ppWForms :: [WForm] -> String
ppWForms wfs = show (leftsOf wfs) ++ " | " ++ show (rightsOf wfs)

instance DispAble Tableaux where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "✘"]
    toGraph' pref (Node fs rule ts) = do
      node pref [shape PlainText, toLabel $ show fs]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

-- Given a formula, is their an applicable rule?
-- If so, which one, and what formulas are the result?
simpleRule :: Form -> Maybe (RuleName, [[Form]])
-- Nothing to do:
simpleRule (At _)          = Nothing
simpleRule (Neg (At _))    = Nothing
simpleRule Top             = Nothing
simpleRule (Neg Top)       = Nothing
-- Single-branch rules:
simpleRule (Neg (Neg f))   = Just ("¬¬", [ [f] ])
simpleRule (Neg (Imp f g)) = Just ("¬→", [ [f, Neg g] ])
-- Splitting rules:
simpleRule (Imp f g)       = Just ("→" , [ [ Neg f ], [g] ])

usable :: WForm -> Bool
usable wf = case simpleRule (collapse wf) of
  (Just _) -> True
  Nothing  -> False

weightOf :: WForm -> (Form -> WForm)
weightOf (Left  _) = Left
weightOf (Right _) = Right

isClosedNode :: [Form] -> Bool
isClosedNode fs = bot `elem` fs || any (\f -> Neg f `elem` fs) fs

extend :: Tableaux -> Tableaux
extend End             = End
extend (Node wfs "" [])
  | isClosedNode (collapseList wfs) = Node wfs "✘" [End]
  | otherwise = uncurry (Node wfs) $ case filter usable wfs of
    []     -> (""     ,[])
    (wf:_) -> (therule,ts) where
      rest = delete wf wfs
      Just (therule,results) = simpleRule (collapse wf)
      ts = [ extend $ Node (nub . sort $ rest++newwfs) "" [] | newwfs <- map (map $ weightOf wf) results ]
extend (Node fs rule ts@(_:_)) = Node fs rule [extend t | t <- ts]
extend (Node _  rule@(_:_) []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"

append :: RuleName -> [Tableaux] -> Tableaux -> Tableaux
append rule tsToAdd (Node fs _  []) = Node fs rule tsToAdd
append rule tsToAdd (Node fs r0 ts) = Node fs r0 [append rule tsToAdd t | t <- ts]
append _    _       End             = End

-- To prove f, start with ¬f.
startFor :: Form -> Tableaux
startFor f = Node [Left $ Neg f] "" []

isClosedTab :: Tableaux -> Bool
isClosedTab End = True
isClosedTab (Node _ _ ts) = ts /= [] && all isClosedTab ts

prove :: Form -> Tableaux
prove = extend . startFor

provable :: Form -> Bool
provable = isClosedTab . prove

-- | Prove and show the tableau.
proveSlideshow :: Form -> IO Bool
proveSlideshow f = do
  let t = extend (startFor f)
  disp t
  return $ isClosedTab t

-- | Soundness and Completeness, to be used with QuickCheck.
soundness, completeness :: Form -> Bool
soundness    f = provable f `implies` isValid  f
completeness f = isValid  f `implies` provable f
