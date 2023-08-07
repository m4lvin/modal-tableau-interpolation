module Logic.PDL.Consistent where

import Data.List
import Data.Maybe

import Logic.Internal
import Logic.PDL
import Logic.PDL.Prove.Tree

-- | M_0 from Proof of Theorem 3, sort of.
m0 :: Tableaux -> [Tableaux]
m0 t0 = lfp closure [t0] where
  closure :: [Tableaux] -> [Tableaux]
  closure ts = ts ++ [ newT
                     | t <- ts
                     , n_ <- allNodesOf t
                     , let n = map (fst . collapse) n_
                     , isSimple n
                     , consistent n
                     , newT <- tableauFor n : allDiamondTableauxFor n -- take care of all diamonds!
                     , newT `notElem` ts ]

-- | Generate tableaux with given root for all possible choice of diamonds.
allDiamondTableauxFor :: [Form] -> [Tableaux]
allDiamondTableauxFor fs =
  [ Node (weightify fs) [] "At" (weightify [dmf]) [tableauFor $ Neg f : mapMaybe (projection aprog) fs]
  | isSimple fs
  , dmf@(Neg (Box (Ap aprog) f)) <- fs
  ] where
  weightify nfs = [(Left f, Nothing) | f <- nfs]

-- | Set of S_{X,Y} for a given T from M_0.
-- Instead of finding the root and end node and everything in between,
-- we collect all formulas anywhere in the history of the end node.
pathSetsOf :: Tableaux -> [[Form]]
-- local end node because open / no children:
pathSetsOf n@(Node _ _ _ _ []) = [ localForms n ]
-- local end node because atomic rule is used:
pathSetsOf n@(Node _ _ "M+" _ _ts) = [localForms n] -- : concatMap pathSetsOf ts -- not because closure?
-- anywhere else, recurse until we get an end node:
pathSetsOf (Node _ _ _ _ ts@(_:_)) = concatMap pathSetsOf ts
pathSetsOf End = []

-- | Local part of a history, i.e. until the last application of the atomic rule.
localPartOf :: History -> History
localPartOf [] = []
localPartOf ((_,"M+"):_) = []
localPartOf ((wfs,rule):rest) = (wfs,rule) : localPartOf rest

-- | All formulas true on the local path.
-- The "(wfs:)" is to include formulas from the current node itself.
localForms :: Tableaux -> [Form]
localForms (Node wfs hist _ _ _) =
  nub . concatMap (map (fst . collapse)) . (wfs:) . map fst . localPartOf $ hist
localForms End = []

-- | Theorem 3: Given an open tableau, build a pointed Kripke model.
tabToMod :: Tableaux -> Maybe (Model [Form], [Form])
tabToMod End = Nothing
tabToMod t | isClosedTab t = Nothing
tabToMod t@(Node wfs _ _ _ _) = Just (KrM ws rl, actual) where
  ws = nub [ (w,v) | w <- filter consistent $ concatMap pathSetsOf (m0 t)
                   , let v = [ prp | At prp <- w ] ]
  rl :: [(Atom,[([Form],[Form])])]
  rl = [ (prg, connectionsFor prg) | prg <- nub $ progsIn (map fst ws) ]
  connectionsFor :: Atom -> [([Form],[Form])]
  connectionsFor prg = [ (fs,gs) | fs <- map fst ws
                                 , gs <- map fst ws
                                 , all (`elem` gs) (mapMaybe (projection prg) fs)]
  actual :: [Form]
  actual = case filter containsRoot (filter consistent $ pathSetsOf t) of
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

testModelConstruction :: Form -> IO ()
testModelConstruction f = do
  pp f
  let t = tableauFor [Neg f]
  disp t
  putStrLn "\n\n M0:\n"
  mapM_ disp $ m0 t

  putStrLn "\nTableau roots and resulting formula-set worlds:"
  mapM_ (\n@(Node wfs _ _ _ _) -> do
            putStrLn $ toStrings $ map collapse wfs
            mapM_ (\fs -> putStrLn $ "  " ++ toStrings fs) (pathSetsOf n)) (m0 t)
  putStrLn "\n\n toIntModel:\n"
  -- print (tabToMod t)
  print (toIntModel <$> tabToMod t)
