{-# LANGUAGE FlexibleInstances #-}

module Logic.BasicModal.Prove.Tree where

import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List
import Data.Maybe (mapMaybe,isJust)

import Logic.Internal
import Logic.BasicModal

-- | A Tableaux is either a Node or an End marker.
data Tableaux = Node -- ^ A node contains:
                  [WForm]    -- ^ current list of weighted formulas
                  RuleName   -- ^ name of the rule that is applied here
                  [WForm]    -- ^ list of *active* wformulas where rule is applied
                  [Tableaux] -- ^ list of child nodes
              | End
  deriving (Eq,Ord,Show)

type RuleName = String -- FIXME: use data RuleName = Con NegCon etc.

type WForm = Either Form Form

collapse :: WForm -> Form
collapse (Left  f) = f
collapse (Right f) = f

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

project :: Form -> Maybe Form
project (Box f) = Just f
project _       = Nothing

-- | Apply change function from a rule to a weighted formulas.
applyW :: (Form -> Maybe Form) -> WForm -> Maybe WForm
applyW fct (Left  f) = fmap Left  (fct f)
applyW fct (Right f) = fmap Right (fct f)

-- | Rules: Given a formula, is their a simple rule?
-- If so, which rule, what replaces the active formula, and how do other formulas change and survive?
type RuleApplication = (RuleName, [[Form]], Form -> Maybe Form)

noChange :: Form -> Maybe Form
noChange = Just

simpleRule :: Form -> Maybe RuleApplication
-- Nothing to do:
simpleRule Bot             = Nothing
simpleRule (At _)          = Nothing
simpleRule (Neg (At _))    = Nothing
simpleRule (Neg Bot)       = Nothing
simpleRule (Box _)         = Nothing -- yes, really
-- Single-branch rules:
simpleRule (Neg (Neg f))   = Just ("¬", [ [f]    ], noChange)
simpleRule (Con f g     )  = Just ("∧", [ [f, g] ], noChange)
simpleRule (Neg (Con _ _)) = Nothing -- see advancedRule
simpleRule (Neg (Box _ ))  = Nothing -- see advancedRule

advancedRule :: Form -> Maybe (RuleName, [[Form]], Form -> Maybe Form)
-- Splitting rule:
advancedRule (Neg (Con f g)) = Just ("¬∧" , [ [Neg f], [Neg g] ], noChange)
-- single-branching but throwing away the rest!
advancedRule (Neg (Box f)) = Just ("¬☐", [ [Neg f] ], project)
advancedRule _             = Nothing

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
  | isClosedNode (map collapse wfs) = [Node wfs "✘" (isClosedBecause wfs) [End]]
  | otherwise = case (filter simplyUsable wfs, filter advancedlyUsable wfs) of
    ([],[])  -> [ Node wfs "" [] [] ] -- We're stuck here.
    ([],usablewfs)  -> concatMap (\wf -> let
        Just (therule,results,change) = advancedRule (collapse wf)
        rest = delete wf wfs
        tss = [ Node (nub . sort $ mapMaybe (applyW change) rest ++ newwfs) "" [] [] | newwfs <- map (map $ weightOf wf) results ]
      in extensions (Node wfs therule [wf] tss)) usablewfs
    (usablewfs,_) -> concatMap (\wf -> let
        Just (therule,results,change) = simpleRule (collapse wf)
        rest = delete wf wfs
        tss = [ Node (nub . sort $ mapMaybe (applyW change) rest ++ newwfs) "" [] [] | newwfs <- map (map $ weightOf wf) results ]
      in extensions (Node wfs therule [wf] tss)) usablewfs
extensions (Node fs rule actives ts@(_:_)) = [ Node fs rule actives ts' | ts' <- pickOneOfEach $ map (filterOneIfAny isClosedTab . extensions) ts ]
extensions (Node _  rule@(_:_) _ []) = error $ "Rule '" ++ rule ++ "' applied but no successors!"


-- To prove f, start with ¬f.
-- Special case: to prove f --> g (which is ¬(f & ¬g)) start with partition [f ; ¬g]
startFor :: Form -> Tableaux
startFor (Neg (f `Con` Neg g)) = Node [Left f, Right (Neg g)] "" [] []
startFor f                     = Node [Left $ Neg f]          "" [] []

isClosedTab :: Tableaux -> Bool
isClosedTab End = True
isClosedTab (Node _ _ _ ts) = ts /= [] && all isClosedTab ts

-- | Try to prove something by generating all extended tableauxs.
-- Returns a closed tableaux if there is one in the list.
prove :: Form -> Tableaux
prove f = head $ filterOneIfAny isClosedTab $ extensions $ startFor f

tableauFor :: [Form] -> Tableaux
tableauFor fs = head . filterOneIfAny isClosedTab $ extensions $
  Node (map Left fs) "" [] []

inconsistent :: [Form] -> Bool
inconsistent = isClosedTab . tableauFor

provable :: Form -> Bool
provable = isClosedTab . prove

-- | Prove and show the tableau.
proveSlideshow :: Form -> IO Bool
proveSlideshow f = do
  let t = prove f
  disp t
  return $ isClosedTab t
