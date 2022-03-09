module Logic.BasicModal.Consistent where

import Data.Maybe

import Logic.BasicModal
import Logic.BasicModal.Prove.Tree

-- | Given a tableaux, build a Kripke model if possible.
tabToMod :: Tableaux -> Maybe (Model [Form], [Form])
-- no model when closed:
tabToMod End = Nothing -- FIXME: make error, should never be reached anyway?
tabToMod (Node _ "✘" _ _) = Nothing
-- same model as child for single-branch rules:
tabToMod (Node _ "¬" _ [child]) = tabToMod child
tabToMod (Node _ "∧" _ [child]) = tabToMod child
-- splitting rule:
tabToMod (Node _ "¬∧" _ children) =
  listToMaybe $ mapMaybe tabToMod children
-- atomic rule:
tabToMod (Node wfs "¬☐" _ [child]) =
  case tabToMod child of
    Nothing -> Nothing
    Just _  ->
      -- NOTE: using only one child model would not be enough!
      -- We need to get open tableaus for all diamonds:
      let
        childMs =
          [ tabToMod (tableauFor (Neg f : mapMaybe (project . collapse) wfs) )
          | Neg (Box f) <- map collapse wfs ]
      in
        if all isJust childMs
          then Just $ comboModel (map collapse wfs) [ c | At c <- map collapse wfs ] (map fromJust childMs)
          else Nothing
-- open leaf, create a single world model:
tabToMod (Node wfs "" _ []) =
  Just (KrM [w] theVal theRel, w) where
  w = map collapse wfs
  theRel x = if x == w then [ ] else undefined
  theVal x = if x == w then [ c | At c <- map collapse wfs ] else undefined
tabToMod (Node _ rule _ _) = error $ "unknown rule: " ++ rule

-- | Combine a single world and valuation with multiple pointed models.
-- The new world is added "before" the previous points and becomes the new point.
-- Preconditions:
-- - the new world must be fresh, i.e. not be in the models already!
-- - the given models must not overlap in worlds!
comboModel :: Eq w => w -> [Atom] -> [(Model w, w)] -> (Model w, w)
comboModel w localTruths oldModels = (newM, w) where
  newM = KrM (w : concatMap (worlds . fst) oldModels) newVal newRel
  newVal x = if x == w then localTruths else oldIn val x (map fst oldModels)
  newRel x = if x == w then map snd oldModels else oldIn rel x (map fst oldModels)
  oldIn _ _ [] = undefined
  oldIn f x (m:ms) | x `elem` worlds m = f m x
                   | otherwise         = oldIn f x ms
