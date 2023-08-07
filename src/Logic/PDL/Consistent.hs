module Logic.PDL.Consistent where

import Data.List
import Data.Maybe

import Logic.Internal
import Logic.PDL
import Logic.PDL.Prove.Tree


-- | A possible world for the model construction,
-- given by consistent a list starting with consistent root X and ending with consistent end node Y.
type TabWorld = [Tableaux]

squash :: ([TabWorld],[TabWorld]) -> [TabWorld]
squash (ws, vs) = vs ++ ws -- FIXME: is this the right thing to do?!?!

-- | Get worlds for this tableaux: pair of current worlds and other worlds.
worldsFor :: Tableaux -> ([TabWorld],[TabWorld])
-- closed, no worlds:
worldsFor End = ([],[])
worldsFor (Node _ _ "✘" _ _) = ([],[])
-- open leaf, create a single world:
worldsFor n@(Node _ _ "" _ []) = ([[n]],[])
-- Atomic rule:
worldsFor n@(Node wfs _ "At" _ [child]) =
  case worldsFor child of
    -- If inconsistent, make no world:
    ([], _) -> ([], [])
    -- otherwise, ...
    (_:_, _) ->
      let
        childMs = -- ... get open tableaux for all diamonds ...
          [ worldsFor (tableauFor (Neg f : mapMaybe (projection aprog . fst . collapse) wfs)  )
          | Neg (Box (Ap aprog) f) <- map (fst . collapse) wfs ]
      in
        if any (null . fst) childMs
          then ([],[])
          -- ... then make one world here and start collecting new ones:
          else ([[n]], concatMap squash childMs)
-- all other rules with children, make
worldsFor n@(Node _ _ rule _ children)
  | head rule `elem` "¬∧∪;nM4?" = --- FIXME: incredibly ugly rule check & BUG misisng
    let chWorlds = map worldsFor children
        localWorlds = concatMap fst chWorlds
        rest = concatMap snd chWorlds
      in (map (n:) localWorlds, rest)
worldsFor (Node _ _ rule _ _) = error $ "unknown rule: " ++ rule

-- | Given an tableau, build a model.
-- Uses the construction in the proof of Theorem 3.
-- TODO: should worlds be [Form] or TabWorld?
makeModel :: Tableaux -> (Model TabWorld, TabWorld)
makeModel t = (KrM worlds progs, truthsHere) where
  tss = squash $ worldsFor t
  worlds = nub [ (ts, [ x | (Node wfs _ _ _ _ ) <- ts, (At x) <- map (fst . collapse) wfs ] )
               | ts <- tss ]
  -- FIXME: should probably use something like "allProgsIn" here:
  allprogs = nub [ prg | (Neg (Box (Ap prg) _)) <- concatMap formsAtWorld tss ]
  formsAtWorld = concatMap (map (fst . collapse) . (\(Node wfs _ _ _ _ ) -> wfs))
  -- Like MB we define \pi(A) the easy way, not caring if actually coming from same tableau!!
  progs = [ (prg, [ (w1, w2) | w1 <- tss
                             , w2 <- tss
                             , mapMaybe (projection prg) (formsAtWorld w1)
                               `subseteq` formsAtWorld w2
                             ] )
          | prg <- allprogs ]
  truthsHere = head (map fst worlds) -- FIXME: can we be sure that this is the actual world?

-- BUG, probably above here: [a*]p runs forever now, creating an infinite model?


-- | Given a tableaux, build a pointed Kripke model if possible.
tabToMod :: Tableaux -> Maybe (Model [Form], [Form])
-- no model when closed:
tabToMod End = Nothing
tabToMod (Node _ _ "✘" _ _) = Nothing
-- single-branch rules:
-- IDEA: should we still add the current formula to the current world??
tabToMod (Node _ _ "¬"  _ [child]) = tabToMod child
tabToMod (Node _ _ "∧"  _ [child]) = tabToMod child
tabToMod (Node _ _ "¬?" _ [child]) = tabToMod child
tabToMod (Node _ _ "¬;" _ [child]) = tabToMod child
tabToMod (Node _ _ "∪"  _ [child]) = tabToMod child
tabToMod (Node _ _ ";"  _ [child]) = tabToMod child
-- special rules:
tabToMod (Node _ _ "M+" _ [child]) = tabToMod child
tabToMod (Node _ _ ('6':':':' ':_) _ [child]) = tabToMod child
  -- TODO: identify worlds here, based on the number of back-steps given by condition 6 marker?
tabToMod (Node _ _ "4"  _ [child]) = tabToMod child
-- splitting rules:
tabToMod (Node _ _ "*"  _ children) = listToMaybe $ mapMaybe tabToMod children -- now can be splitting!
tabToMod (Node _ _ "¬∧" _ children) = listToMaybe $ mapMaybe tabToMod children
tabToMod (Node _ _ "?"  _ children) = listToMaybe $ mapMaybe tabToMod children
tabToMod (Node _ _ "¬∪" _ children) = listToMaybe $ mapMaybe tabToMod children
tabToMod (Node _ _ "¬*" _ children) = listToMaybe $ mapMaybe tabToMod children
-- atomic rule:
tabToMod (Node wfs _ "At" _ [child]) =
  case tabToMod child of
    Nothing -> Nothing
    Just _  ->
      let
        childMs = -- we need open tableaux for all diamonds!
          [ (aprog , tabToMod (tableauFor (Neg f : mapMaybe (projection aprog . fst . collapse) wfs) ) )
          | Neg (Box (Ap aprog) f) <- map (fst . collapse) wfs ]
      in
        if all (isJust . snd) childMs
          then Just $ comboModel
                      (map (fst . collapse) wfs)
                      [ prp | At prp <- map (fst . collapse) wfs ]
                      (map (fmap fromJust) childMs)
          else Nothing
-- open leaf, create a single world model:
tabToMod (Node wfs _ "" _ []) =
  Just (KrM [(w, truthsHere)] noProgs, w) where
  w = map (fst . collapse) wfs
  noProgs = []
  truthsHere = [ prp | At prp <- map (fst . collapse) wfs ]
tabToMod (Node _ _ rule _ _) = error $ "unknown rule: " ++ rule

mergeProg :: Eq a=> (Atom,[(a,a)]) -> [(Atom,[(a,a)])] -> [(Atom,[(a,a)])]
mergeProg (pa,ra) [] = [(pa,ra)]
mergeProg (pa,ra) ((pb,rb):rest)
  | pa == pb  = (pa, nub $ ra ++ rb) : rest
  | otherwise = (pb,rb) : mergeProg (pa,ra) rest

comboProgs :: Eq a => [(Atom,[(a,a)])] -> [(Atom,[(a,a)])]
comboProgs [] = []
comboProgs [ar] = [ar]
comboProgs (ar:rest) = mergeProg ar $ comboProgs rest

-- | Combine a single world and valuation with multiple pointed models.
-- The new world is added "before" the previous points and becomes the new point.
-- Preconditions:
-- - the new world must be fresh, i.e. not be in the models already!
-- - the given models must not overlap in worlds!
-- Differences compared to BasicModal:
-- - [X] we now also need an atom for the program label.
-- - [ ] when and how to create loops? we need them to stick to finite models.
comboModel :: (Show w, Eq w) => w -> [Atom] -> [(Atom, (Model w, w))] -> (Model w, w)
comboModel w localTruths oldModels = (newM, w) where
  newM = KrM ((w, localTruths) : concatMap (worldsOf . fst . snd) oldModels) newProgs
  oldLinks = concatMap (progsOf . fst . snd) oldModels
  newLinks = [ (prg, [(w,w')]) | (prg,(_,w')) <- oldModels ]
  newProgs = comboProgs (newLinks ++ oldLinks)

toIntModel :: Eq a => (Model a, a) -> (Model Int, Int)
toIntModel (KrM ws rl, oldActual) =
  (KrM [ (k, v) | ((_, v), k) <- mapping ]
       [ (prg, map myMapPair prel) | (prg, prel) <- rl ]
  , myMap oldActual)
  where
    myMap old = fromJust (lookup old worldMap)
    myMapPair (w, w') = (myMap w, myMap w')
    mapping = zip ws [0..]
    worldMap = zip (map fst ws) [0..]
