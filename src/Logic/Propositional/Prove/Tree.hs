{-# LANGUAGE FlexibleInstances #-}

-- A Tableaux prover.
-- Nodes in the trees are lists of formulas with weights, together
-- with a rule that was applied to get the children.

module Logic.Propositional.Prove.Tree where

import Data.Either (lefts, rights)
import Data.GraphViz
import Data.GraphViz.Types.Monadic
import Data.List
import Data.Maybe (fromJust, isJust)

import Logic.Internal
import Logic.Propositional

data Tableaux = Node [WForm] RuleName [Tableaux] | End
  deriving (Eq,Ord,Show)

type RuleName = String

type WForm = Either Form Form

collapse :: WForm -> Form
collapse (Left f)  = f
collapse (Right f) = f

collapseList :: [Either Form Form] -> [Form]
collapseList = map collapse

ppWForms :: [WForm] -> String
ppWForms wfs = show (lefts wfs) ++ "  ;  " ++ show (rights wfs)

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
simpleRule (Con f g)       = Just ("&" , [ [f,     g] ])
-- Splitting rules:
simpleRule (Imp f g)       = Just ("→" , [ [ Neg f ], [    g] ])
simpleRule (Neg (Con f g)) = Just ("¬&", [ [ Neg f ], [Neg g] ])

usable :: WForm -> Bool
usable = isJust . simpleRule . collapse

weightOf :: WForm -> (Form -> WForm)
weightOf (Left  _) = Left
weightOf (Right _) = Right

isClosedNode :: [Form] -> Bool
isClosedNode fs = bot `elem` fs || any (\f -> Neg f `elem` fs) fs

extend :: Tableaux -> Tableaux
extend End             = End
extend (Node wfs "" []) = case (isClosedNode (collapseList wfs), filter usable wfs) of
  (True,_   ) -> Node wfs "✘" [End]
  (_   ,[]  ) -> Node wfs ""     []
  (_   ,wf:_) -> Node wfs therule ts where
    rest = delete wf wfs
    (therule,results) = fromJust $ simpleRule (collapse wf)
    ts = [ extend $ Node (nub . sort $ rest++newwfs) "" [] | newwfs <- map (map $ weightOf wf) results ]
extend (Node fs rule ts@(_:_)) = Node fs rule (map extend ts)
extend (Node _  rule@(_:_) []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"

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
