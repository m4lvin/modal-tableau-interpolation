{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Logic.BasicModal.Prove.Tree where

import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List
import Data.Maybe (isJust)

import Logic.Internal
import Logic.BasicModal

-- | A Tableaux is either a Node or an End marker.
data Tableaux = Node -- ^ A node contains:
                  [WForm]    -- ^ current list of weighted formulas
                  RuleName   -- ^ name of the rule that is applied here
                  [WForm]    -- ^ list of *active* weighted formulas to which the rule is applied
                  [Tableaux] -- ^ list of child nodes
              | End
  deriving (Eq,Ord,Show)

type RuleName = String

type WForm = Either Form Form

collapse :: WForm -> Form
collapse (Left  f) = f
collapse (Right f) = f

collapseList :: [Either Form Form] -> [Form]
collapseList = map collapse

leftsOf, rightsOf :: [WForm] -> [Form]
leftsOf  wfs = [f | Left  f <- wfs]
rightsOf wfs = [f | Right f <- wfs]

ppWForms :: [WForm] -> [WForm] -> String
ppWForms wfs actives = intercalate ", " (map ppFormA (filter isLeft wfs)) ++ "   |   " ++ intercalate ", " (map ppFormA (filter (not . isLeft) wfs)) where
  ppFormA wf = [ '»' |  wf `elem` actives ] ++ ppForm (collapse wf) ++ [ '«' |  wf `elem` actives ]

instance DispAble Tableaux where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "✘"]
    toGraph' pref (Node fs rule actives ts) = do
      node pref [shape PlainText, toLabel $ ppWForms fs actives]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

project :: [Form] -> [Form]
project fs = [ f | Box f <- fs ]

-- | Apply change function from a rule to a list of weighted formulas.
-- Note: This assume that `fct` still does the same when given a subset!
applyW :: ([Form] -> [Form]) -> [WForm] -> [WForm]
applyW fct wfs = map Left (fct $ leftsOf wfs) ++ map Right (fct $ rightsOf wfs)

-- | Rules: Given a formula, is their a simple rule?
-- If so, which rule, what replaces the active formula, and how do the other formulas change?
simpleRule :: Form -> Maybe (RuleName, [[Form]], [Form] -> [Form])
-- Nothing to do:
simpleRule Bot             = Nothing
simpleRule (At _)          = Nothing
simpleRule (Neg (At _))    = Nothing
simpleRule (Neg Bot)       = Nothing
simpleRule (Box _)         = Nothing -- yes, really
-- Single-branch rules:
simpleRule (Neg (Neg f))   = Just ("¬¬", [ [f]        ], id)
simpleRule (Neg (Imp f g)) = Just ("¬→", [ [f, Neg g] ], id)
simpleRule (Imp _ _)       = Nothing -- see advancedRule
simpleRule (Neg (Box _ ))  = Nothing -- see advancedRule

advancedRule :: Form -> Maybe (RuleName, [[Form]], [Form] -> [Form])
-- Splitting rule for implication
advancedRule (Imp f g)       = Just ("→" , [ [Neg f], [g] ], id)
-- single-branching but throwing away the rest!
advancedRule (Neg (Box f))   = Just ("¬☐", [ [Neg f] ], project)
advancedRule _               = Nothing

simplyUsable :: WForm -> Bool
simplyUsable = isJust . simpleRule . collapse

advancedlyUsable :: WForm -> Bool
advancedlyUsable = isJust . advancedRule . collapse

weightOf :: WForm -> (Form -> WForm)
weightOf (Left  _) = Left
weightOf (Right _) = Right

isLeft :: WForm -> Bool
isLeft (Left  _) = True
isLeft (Right _) = False

isClosedNode :: [Form] -> Bool
isClosedNode fs = Bot `elem` fs || any (\f -> Neg f `elem` fs) fs

isClosedBecause :: [WForm] -> [WForm]
isClosedBecause wfs = foo wfs where
  foo []        = []
  foo (wf:rest) | wf `elem` [Left Bot, Right Bot] = [wf]
                | Left  (Neg $ collapse wf) `elem` wfs = [wf, Left  (Neg $ collapse wf)]
                | Right (Neg $ collapse wf) `elem` wfs = [wf, Right (Neg $ collapse wf)]
                | otherwise = foo rest

extensions :: Tableaux -> [Tableaux]
extensions End = [End]
extensions (Node wfs "" _ [])
  | isClosedNode (collapseList wfs) = [Node wfs "✘" (isClosedBecause wfs) [End]]
  | otherwise = case (filter simplyUsable wfs, filter advancedlyUsable wfs) of
    ([],[])  -> [ Node wfs "" [] [] ] -- We're stuck here.
    ([],usablewfs)  -> concatMap (\wf -> let
        Just (therule,results,change) = advancedRule (collapse wf)
        rest = delete wf wfs
        tss = [ Node (nub . sort $ applyW change rest ++ newwfs) "" [] [] | newwfs <- map (map $ weightOf wf) results ]
      in extensions (Node wfs therule [wf] tss)) usablewfs
    (usablewfs,_) -> concatMap (\wf -> let
        Just (therule,results,change) = simpleRule (collapse wf)
        rest = delete wf wfs
        tss = [ Node (nub . sort $ applyW change rest ++ newwfs) "" [] [] | newwfs <- map (map $ weightOf wf) results ]
      in extensions (Node wfs therule [wf] tss)) usablewfs
extensions (Node fs rule actives ts@(_:_)) = [ Node fs rule actives ts' | ts' <- pickOneOfEach $ map extensions ts ]
extensions (Node _  rule@(_:_) _ []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"
-- FIXME use filterOneClosedIfAny ????

pickOneOfEach :: [[a]] -> [[a]]
pickOneOfEach [] = [[]]
pickOneOfEach (l:ls) = [ x:xs | x <- l, xs <- pickOneOfEach ls ]

-- To prove f, start with ¬f.
startFor :: Form -> Tableaux
startFor (Imp f g) = Node [Left f, Right (Neg g)] "" [] []
startFor f         = Node [Left $ Neg f]          "" [] []

isClosedTab :: Tableaux -> Bool
isClosedTab End = True
isClosedTab (Node _ _ _ ts) = ts /= [] && all isClosedTab ts

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
