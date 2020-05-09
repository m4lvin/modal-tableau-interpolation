{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Logic.BasicModal.Prove.Tree where

import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List

import Logic.Internal
import Logic.BasicModal

-- | Nodes are lists of weighed formulas, together
-- with a rule that was applied to get the children.
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
ppWForms wfs = intercalate ", " (map ppForm (leftsOf wfs)) ++ "  |  " ++ intercalate ", " (map ppForm (rightsOf wfs))

instance DispAble Tableaux where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "✘"]
    toGraph' pref (Node fs rule ts) = do
      node pref [shape PlainText, toLabel $ ppWForms fs]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

project :: [Form] -> [Form]
project fs = [ f | Box f <- fs ]

applyW :: ([Form] -> [Form]) -> [WForm] -> [WForm]
applyW fct wfs = map Left (fct $ leftsOf wfs) ++ map Right (fct $ rightsOf wfs)

-- | Rules: Given a formula, is their a simple rule?
-- If so, which rule, what replaces the active formula, and how do the other formulas change?
simpleRule :: Form -> Maybe (RuleName, [[Form]], [Form] -> [Form])
-- Nothing to do:
simpleRule Top             = Nothing
simpleRule Bot             = Nothing
simpleRule (At _)          = Nothing
simpleRule (Neg (At _))    = Nothing
simpleRule (Neg Top)       = Nothing
simpleRule (Neg Bot)       = Nothing
simpleRule (Box _)         = Nothing -- FIXME really?
-- Single-branch rules:
simpleRule (Neg (Neg f))   = Just ("¬¬", [ [f]        ], id)
simpleRule (Neg (Imp f g)) = Just ("¬→", [ [f, Neg g] ], id)
simpleRule (Imp _ _)       = Nothing -- advanced!
simpleRule (Neg (Box _ ))  = Nothing -- advanced!

advancedRule :: Form -> Maybe (RuleName, [[Form]], [Form] -> [Form])
-- Splitting rule for implication
advancedRule (Imp f g)       = Just ("→" , [ [Neg f], [g] ], id)
-- single-branching but throwing away the rest!
advancedRule (Neg (Box f))   = Just ("¬☐", [ [Neg f]    ], project)
advancedRule _               = Nothing

simplyUsable :: WForm -> Bool
simplyUsable wf = case simpleRule (collapse wf) of
  (Just _) -> True
  Nothing  -> False

advancedlyUsable :: WForm -> Bool
advancedlyUsable wf = case advancedRule (collapse wf) of
  (Just _) -> True
  Nothing  -> False

weightOf :: WForm -> (Form -> WForm)
weightOf (Left  _) = Left
weightOf (Right _) = Right

isClosedNode :: [Form] -> Bool
isClosedNode fs = Bot `elem` fs || Neg Top `elem` fs || any (\f -> Neg f `elem` fs) fs

extensions :: Tableaux -> [Tableaux]
extensions End = [End]
extensions (Node wfs "" [])
  | isClosedNode (collapseList wfs) = [Node wfs "✘" [End]]
  | otherwise = case (filter simplyUsable wfs, filter advancedlyUsable wfs) of
    ([],[])  -> [ Node wfs "" [] ] -- We're stuck here.
    ([],usablewfs)  -> concatMap (\wf -> let
        Just (therule,results,change) = advancedRule (collapse wf)
        rest = delete wf wfs
        tss = [ Node (nub . sort $ applyW change rest ++ newwfs) "" [] | newwfs <- map (map $ weightOf wf) results ]
      in extensions (Node wfs therule tss)) usablewfs
    (usablewfs,_) -> concatMap (\wf -> let
        Just (therule,results,change) = simpleRule (collapse wf)
        rest = delete wf wfs
        tss = [ Node (nub . sort $ applyW change rest ++ newwfs) "" [] | newwfs <- map (map $ weightOf wf) results ]
      in extensions (Node wfs therule tss)) usablewfs
extensions (Node fs rule ts@(_:_)) = [ Node fs rule ts' | ts' <- pickOneOfEach $ map extensions ts ]
extensions (Node _  rule@(_:_) []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"
-- FIXME use filterOneClosedIfAny ????

pickOneOfEach :: [[a]] -> [[a]]
pickOneOfEach [] = [[]]
pickOneOfEach (l:ls) = [ x:xs | x <- l, xs <- pickOneOfEach ls ]

-- To prove f, start with ¬f.
startFor :: Form -> Tableaux
startFor (Imp f g) = Node [Left f, Right (Neg g)] "" []
startFor f = Node [Left $ Neg f] "" []

isClosedTab :: Tableaux -> Bool
isClosedTab End = True
isClosedTab (Node _ _ ts) = ts /= [] && all isClosedTab ts

filterOneClosedIfAny :: [Tableaux] -> [Tableaux]
filterOneClosedIfAny ts
  | any isClosedTab ts = take 1 (filter isClosedTab ts)
  | otherwise          = ts

-- | Try to prove something by generating all extended tableauxs.
-- Returns a closed tableaux if there is one in the list.
prove :: Form -> Tableaux
prove f = head $ filterOneClosedIfAny $ extensions $ startFor f

provable :: Form -> Bool
provable = isClosedTab . prove

-- | Prove and show the tableau.
proveSlideshow :: Form -> IO Bool
proveSlideshow f = do
  let t = prove f
  disp t
  return $ isClosedTab t
