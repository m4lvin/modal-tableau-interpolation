{-# LANGUAGE OverloadedStrings #-}

module Logic.PDL.Consistent where

import Data.Maybe
import Data.Containers.ListUtils (nubOrd)

import Logic.PDL
import Logic.PDL.Loaded
import Logic.PDL.Prove.Tree

-- | M_0 from Proof of Theorem 3, sort of.
m0 :: Tableaux -> [Tableaux]
m0 t0 = closeWith closure [t0] where
  closeWith f ts = case f ts of
    [] -> ts
    (_:_) -> closeWith f (ts ++ f ts)
  closure :: [Tableaux] -> [Tableaux]
  closure ts = nubOrd [ newT
                      | t <- ts
                      , n <- map (map (fst . collapse)) (allNodesOf t)
                      , isSimple n
                      , consistent n
                      , newT <- tableauFor n : allDiamondTableauxFor n -- take care of all diamonds!
                      , newT `notElem` ts ]

-- | Generate tableaux with given root for all possible choice of diamonds.
allDiamondTableauxFor :: [Form] -> [Tableaux]
allDiamondTableauxFor fs =
  [ Node (weightify fs) [] "M" (weightify [dmf]) [tableauFor $ Neg f : mapMaybe (projection aprog) fs]
  | isSimple fs
  , dmf@(Neg (Box (Ap aprog) f)) <- fs
  ] where
  weightify nfs = [(Left f, []) | f <- nfs]

-- | Set of S_{X,Y} for a given T from M_0.
-- Instead of finding the root and end node and everything in between,
-- we collect all formulas anywhere in the history of open end nodes.
pathSetsOf :: Tableaux -> [[Form]]
-- local end node because open / no children:
pathSetsOf n@(Node _ _ _ _ []) = [ localForms n ]
-- local end node because loaded-path-repeat, closed and not needed:
pathSetsOf (Node _ _ (LpR _) _ [End]) = [ ]
-- local end node because free repeat, open and needed:
pathSetsOf n@(Node _ _ (FRep _) _ [End]) = [ localForms n ]
-- local end node because (L+) and then (M) rule is used:
pathSetsOf n@(Node _ _ "L+" _ ts) = [ localForms n | not (all (null . pathSetsOf) ts) ]
-- anywhere else, recurse until we get an open end node:
pathSetsOf (Node _ _ _ _ ts@(_:_)) = concatMap pathSetsOf ts
pathSetsOf End = []

-- | Local part of a history, i.e. until the last application of the atomic rule.
localPartOf :: History -> History
localPartOf [] = []
localPartOf ((_,"L+"):_) = []
localPartOf ((wfs,rule):rest) = (wfs,rule) : localPartOf rest

-- | All formulas true on the local path.
-- The "(wfs:)" is to include formulas from the current node itself.
localForms :: Tableaux -> [Form]
localForms (Node wfs hist _ _ _) =
  nubOrd . concatMap (map (fst . collapse)) . (wfs:) . map fst . localPartOf $ hist
localForms End = []

-- | Theorem 3: Given an open tableau, build a pointed Kripke model.
tabToMod :: Tableaux -> Maybe (Model [Form], [Form])
tabToMod End = Nothing
tabToMod t | isClosedTab t = Nothing
tabToMod t@(Node wfs _ _ _ _) = Just (KrM ws rl, actual) where
  ws = nubOrd [ (w,v) | w <- concatMap pathSetsOf (m0 t)
                      , let v = [ prp | At prp <- w ] ]
  rl :: [(Atom,[([Form],[Form])])]
  rl = [ (prg, connectionsFor prg) | prg <- nubOrd $ progsIn (map fst ws) ]
  connectionsFor :: Atom -> [([Form],[Form])]
  connectionsFor prg = [ (fs,gs) | fs <- map fst ws
                                 , gs <- map fst ws
                                 , all (`elem` gs) (mapMaybe (projection prg) fs)
                                 -- We only add outgoing arrows if `fs` contains some `prg` diamond.
                                 -- This is not needed for correctness but makes the model nicer.
                                 , not . null $ [ () | Neg (Box (Ap prg') _) <- fs
                                                     , prg == prg' ]
                                 ]
  actual :: [Form]
  actual = case filter consistent (filter containsRoot $ pathSetsOf t) of
    [] -> error "No pathSet for given tableau?"
    (ps:_) -> ps
  containsRoot :: [Form] -> Bool
  containsRoot fs = all ((`elem` fs) . fst . collapse) wfs

-- | Convert a model to use integers as worlds.
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
