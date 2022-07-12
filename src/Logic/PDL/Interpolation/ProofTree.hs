module Logic.PDL.Interpolation.ProofTree where

import Data.Either (isRight)
import Data.GraphViz (shape, Shape(PlainText), toLabel)
import Data.GraphViz.Types.Monadic (edge, node)
import Data.Maybe (listToMaybe, catMaybes)
import Data.List ((\\), intercalate)

import Logic.PDL
import Logic.PDL.Prove.Tree hiding (Node,End)
import qualified Logic.PDL.Prove.Tree as T (Tableaux(Node,End))
import Logic.Internal

type Interpolant = Maybe Form

-- | A Tableau with interpolants.
data TableauxIP = Node
                  [WForm]
                  Interpolant -- ^ Maybe a formula that is an interpolant for this node.
                  (Maybe TypeTK)
                  History
                  RuleName
                  [WForm]
                  [TableauxIP]
                | End
  deriving (Eq,Ord,Show)

-- Type markers for T^K which is annotated with 1,2,3.
data TypeTK = One | Two | Three
  deriving (Eq,Ord,Show)

isEndNode :: TableauxIP -> Bool
isEndNode (Node _ _ _ _ _ _ [End]) = True
isEndNode _ = False

ppIP :: Interpolant -> String
ppIP (Just f) = toString f
ppIP Nothing  = "∅"

ppWFormsTyp :: Maybe TypeTK -> [WForm] -> [WForm] -> String
ppWFormsTyp mtyp wfs actives = concat
  [ intercalate ", " (map ppFormA (filter isLeft wfs))
  , "   |"
  , maybe "" show mtyp
  , "   "
  , intercalate ", " (map ppFormA (filter (not . isLeft) wfs)) ]
  where
    ppFormA wf = [ '»' |  wf `elem` actives ] ++ toString (collapse wf) ++ [ '«' |  wf `elem` actives ]

instance DispAble TableauxIP where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "."]
    toGraph' pref (Node wfs mip mtyp _ rule actives ts) = do
      node pref [shape PlainText, toLabel $ ppWFormsTyp mtyp wfs actives ++ "  ::  " ++ ppIP mip]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

toEmptyTabIP :: Tableaux -> TableauxIP
toEmptyTabIP T.End = End
toEmptyTabIP (T.Node wfs history rule actives ts) =
  Node wfs Nothing Nothing history rule actives (map toEmptyTabIP ts)

hasIP :: TableauxIP -> Bool
hasIP End = False
hasIP (Node _ (Just _) _ _ _ _ _) = True
hasIP (Node _ Nothing  _ _ _ _ _) = False

ipOf :: TableauxIP -> Form
ipOf End = error "End nodes do not have interpolants."
ipOf (Node _ (Just f ) _ _ _ _ _) = f
ipOf (Node _ Nothing   _ _ _ _ _) = error "No interpolant here (yet)."

-- Get left or right formulas, and ignore markings!
leftsOf, rightsOf :: [WForm] -> [Form]
leftsOf  wfs = [f | (Left  f,_) <- wfs]
rightsOf wfs = [f | (Right f,_) <- wfs]

-- For any branching rule we combine the two previous interpolants
-- with a connective depending on the side of the active formula (see page ??)
branchIP :: ([TableauxIP] -> [(Either Form Form, Maybe Form)] -> Maybe Form)
branchIP [t1,t2] actives  = Just $ connective (ipOf t1) (ipOf t2) where
  connective = case actives of
    [(Left  _, _)] -> dis -- left side is active, use disjunction
    [(Right _, _)] -> Con -- right side is active, use conjunction
    _              -> error $ "Could not find the active side: " ++ show actives
branchIP _ _ = error "branchIP only works for exactly two branches."

fillIPs :: TableauxIP -> TableauxIP
-- Ends and already interpolated nodes: nothing to do:
fillIPs End = End
fillIPs t@(Node _ (Just _) _ _ _ _ _) = t
-- Closed end nodes: use the active formulas or a constant as interpolant:
fillIPs (Node wfs Nothing mtyp history "✘" actives [End]) = Node wfs mip mtyp history "✘" actives [End] where
  candidates = map fst actives -- NOTE: ignore markings
  mip = listToMaybe $ lrIp candidates
  lrIp fs = [ Bot | Left  Bot `elem` fs ]
         ++ [ top | Right Bot `elem` fs ]
         ++ [     f | Left  f <- fs, Right (Neg f) `elem` fs ]
         ++ [ Neg f | Right f <- fs, Left  (Neg f) `elem` fs ]
         ++ [ Bot   | Left  f <- fs, Left  (Neg f) `elem` fs ] -- inconsistency implies bot
         ++ [ top   | Right f <- fs, Right (Neg f) `elem` fs ] -- top implies Neg inconsistency
fillIPs n@(Node wfs Nothing _ history rule actives ts)
-- Non-end nodes where children are missing IPs: recurse
  | not (all hasIP ts) = Node wfs Nothing Nothing history rule actives (map fillIPs ts)
-- If left side is empty, then T is an interpolant:
  | null (leftsOf wfs) = Node wfs (Just top) Nothing history rule actives ts
-- Non-end nodes where children already have IPs: distinguish rules
  | otherwise = let
      newMIP = case (rule,actives) of
        -- single-child rules are easy, the interpolant stays the same:
        ("¬" ,_) -> Just $ ipOf t where [t] = ts
        ("∧" ,_) -> Just $ ipOf t where [t] = ts
        ("¬?",_) -> Just $ ipOf t where [t] = ts
        ("¬;",_) -> Just $ ipOf t where [t] = ts
        ("∪" ,_) -> Just $ ipOf t where [t] = ts
        (";" ,_) -> Just $ ipOf t where [t] = ts
        ("n" ,_) -> Just $ ipOf t where [t] = ts -- QUESTION: is this okay?
        ("M+",_) -> Just $ ipOf t where [t] = ts -- QUESTION: is this okay?
        ("M-",_) -> Just $ ipOf t where [t] = ts -- QUESTION: is this okay?
        -- for the branching rule we combine the two previous interpolants
        -- with a connective depending on the side of the active formula:
        ("¬∧",_) -> branchIP ts actives
        ("?" ,_) -> branchIP ts actives
        ("¬∪",_) -> branchIP ts actives
        ("¬n",_) -> branchIP ts actives
        -- for the critical rule we prefix the previous interpolant with diamond or Box, depending on the active side
        -- if the other side is empty, then use Bot or Top as interpolant (note: <a>T and T have different voc) - see page 44
        ("At",[(Left  (Neg (Box (Ap x) _)),_)]) ->
          let [t] = ts
          in Just $ if null $ catMaybes [ projection x g | (Right g, _) <- wfs ] then Bot else dia (Ap x) (ipOf t)
        ("At",[(Right (Neg (Box (Ap x) _)),_)]) ->
          let [t] = ts
          in Just $ if null $ catMaybes [ projection x g | (Left g, _) <- wfs ] then top else Box (Ap x) (ipOf t)
        (rl  ,_) -> error $ "Rule " ++ rl ++ " applied to " ++ ppWForms wfs actives ++ "\n  Unable to interpolate: " ++ show n
      in Node wfs newMIP Nothing history rule actives ts

fillAllIPs :: TableauxIP -> TableauxIP
fillAllIPs = fixpoint fillIPs -- FIXME: is this necessary?

-- Definitions to deal with condition 6 end nodes

wfsOf :: TableauxIP -> [WForm]
wfsOf (Node wfs _ _ _ _ _ _) = wfs
wfsOf End = []

-- Definition 27: sub-tableau T^J
tjOf :: TableauxIP -> TableauxIP
tjOf (Node wfs ip _ history rule actives ts) =
  Node wfs ip Nothing history rule actives (if stop then [] else map tjOf ts) where
  stop = or
    [ rule == "M-" -- Stop when the rule (M-) is applied.
    , (not . isLoadedNode) wfs -- Stop at free nodes.
    , length ts == 1 && null (leftsOf (wfsOf (head ts))) -- Stop when first component of (unique!?) successor is empty.
    , wfs `elem` map fst history -- Stop when there is a predecessor with same pair. -- FIXME? History might go too far up?
    ]
tjOf End = End

-- Definition 28
-- D(T): disjunction of conjunctions of each of the given nodes (of T^J)
dOf :: [[WForm]] -> Form
dOf tjNodes = multidis [ multicon [ f | (Left f, _) <- wfs ] | wfs <- tjNodes ]
-- T(Y): all nodes where the right side is Y
pathsInToNodeWith :: TableauxIP -> [Form] -> [Path]
pathsInToNodeWith t y = filter (seteq y . rightsOf . wfsOf . at t) (allPathsIn t)

dtyOf :: TableauxIP -> [Form] -> Form
dtyOf t y = dOf $ map (wfsOf . at t) $ pathsInToNodeWith t y

-- A path, given by the indices to go from start to end.
type Path = [Int]

at :: TableauxIP -> Path -> TableauxIP
at n [] = n
at (Node _ _ _ _ _ _ ts) (i:rest) = ts !! i `at` rest
at End _ = error "Reached End marker."

allPathsIn :: TableauxIP -> [Path]
allPathsIn (Node _ _ _ _ _ _ ts) = [] : [ i:rest | (i,t) <- zip [0..] ts, rest <- allPathsIn t ]
allPathsIn End = error "Reached End marker."

-- ≤
isPrefixOf :: Path -> Path -> Bool
isPrefixOf p1 p2 = take (length p1) p2 == p1

-- <
isProperPrefixOf :: Path -> Path -> Bool
isProperPrefixOf p1 p2 = take (length p1) p2 == p1 && length p1 /= length p2

-- ◁
isImmediatePredOf :: Path -> Path -> Bool
isImmediatePredOf p1 p2 = p1 `isPrefixOf` p2 && length p1 + 1 == length p2

-- Definition 15: ◁' which is ◁ plus "loops" (page 21, needed for Def 29)
-- NOTE: s and t are given by paths from tab root; tab and sp need not be the same.
trianglePrime :: TableauxIP -> Path -> Path -> Bool
trianglePrime tab sp tp =
  tp `isImmediatePredOf` sp
  ||
  (    isEndNode (tab `at` sp)
    && any (\up -> up `isProperPrefixOf` sp
                   && up `isImmediatePredOf` tp
                   && wfsOf (tab `at ` up) == wfsOf (tab `at` sp))
           (allPathsIn tab) )

-- Definition 29:
-- T(Y)^ε
tOfEpsilon :: TableauxIP -> [Form] -> [Path]
tOfEpsilon tabTJ y = [ root_to_s | root_to_s <- pathsInToNodeWith tabTJ y
                                 , not $ any (trianglePrime tabTJ root_to_s) (pathsInToNodeWith tabTJ y) ]
-- T(Y)^I  -- nodes where we (should) already have interpolants!
tOfI :: TableauxIP -> [Form] -> [Path]
tOfI tabTJ y = filter (\root_to_s -> not $ any (trianglePrime tabTJ root_to_s) (allPathsIn tabTJ))
                      (tOfEpsilon tabTJ y)
-- T(Y)^◁
tOfTriangle :: TableauxIP -> [Form] -> [Path]
tOfTriangle tabTJ y = tOfEpsilon tabTJ y \\ tOfI tabTJ y

-- Definition 30: I(Y)
-- NOTE: different from ipOf
iOf :: TableauxIP -> [Form] -> Form
iOf t y = case tOfI t y of
  [] -> Bot
  ts -> multidis (map (ipOf . at t) ts)


-- Definition 31: T^K
-- Idea: Nodes in T^K here correspond to Y-regions in T^J.
-- Input should be the node Y1/Y2 obtained using M+ (page 35)
tkOf :: TableauxIP -> TableauxIP
tkOf End = error "Cannot make T^K for End marker."
tkOf (Node _ (Just _) _ _ _ _ _ ) = error "Already have an interpolant, why bother with T^K?"
tkOf t@(Node t_wfs Nothing _ t_history t_rule t_actives _) =
  Node
    ((Left (dtyOf t y2), Nothing) : rightY2) -- D(T(Y2)) / Y2
    Nothing -- no interpolant yet
    (Just One)
    t_history
    t_rule
    t_actives -- QUESTION: active formulas stay the same? needed in Def 32!
    (tkSuccessors t One t) -- FIXME: ugly but necessary?!
  where
    y2 = rightsOf t_wfs
    rightY2 = map (\f -> (Right f, Nothing)) y2
-- three cases for the successors:
tkSuccessors :: TableauxIP -> TypeTK -> TableauxIP -> [TableauxIP]
tkSuccessors _ _ End = error "End marker has no successors!"
-- 1 to 2 has one or no successors:
tkSuccessors topT One (Node wfs _ _ history rule actives [childT])
  -- PROBLEM: need correct k( ) function on history to check the condition!?
  | any (\_ -> undefined) history = [] -- end node!
  | otherwise = [ Node
                    ((Left (dOf (map (wfsOf . at topT) $ tOfTriangle topT y)), Nothing) : rightY)
                    Nothing -- no interpolant yet
                    (Just Two)
                    history
                    rule
                    actives
                    (tkSuccessors topT Two childT) -- unsafe!?
                ]
  where
    y = rightsOf wfs
    rightY = map (\f -> (Right f, Nothing)) y
tkSuccessors _ One Node{} = error "Type One node must have exactly one child."
-- 2 to 3 has one or no successors:
tkSuccessors topT Two (Node wfs _ _ history rule actives [childT])
  | null (tOfTriangle topT y) = [] -- end node when T(Y)◁ is empty
  | otherwise = [ Node
                    ((Left (dOf (map (wfsOf . at topT) $ tOfTriangle topT y)), Nothing) : rightY)
                    Nothing -- no interpolant yet
                    (Just Three)
                    history
                    rule
                    actives
                    (tkSuccessors topT Three childT)
                ]
  where
    y = rightsOf wfs
    rightY = map (\f -> (Right f, Nothing)) y
tkSuccessors _ Two Node{} = error "Type Two node must have exactly one child."
-- 3 to 1 has n many successors:
tkSuccessors topT Three (Node _ _ _ history rule actives ts) =
  [ Node
      ( (Left (dOf (map (wfsOf . at topT) $ tOfTriangle topT z)), Nothing)
        : [ mf | mf <- wfsOf childT, isRight (fst mf) ] )
      Nothing -- no interpolant yet
      (Just One)
      history
      rule
      actives
      (tkSuccessors topT One childT)
  | childT <- ts -- getting Z1 to Zn
  , let z = rightsOf (wfsOf childT) ]

-- All successors of a node in a TK tableau, with the paths to them.
-- This is <, transitive closure of ◁.
allSuccsOf :: TableauxIP -> [(Path, TableauxIP)]
allSuccsOf End = []
allSuccsOf (Node _ _ _ _ _ _ tks) = nexts ++ laters where
  nexts = zip (map return [0..]) tks
  laters = [ (i:path,suc)
           | ([i],tk) <- nexts
           , (path,suc) <- allSuccsOf tk ]

-- canonical program from s to t along a path
-- IDEA: Instead of using index-paths here, add "Maybe Prog" to [TK] in data TK?
canonProg :: TableauxIP -> Path -> Prog
canonProg _    []  = error "No canonical program for empty path."
canonProg tk_s [i] = fst $ canonProgStep tk_s !! i
canonProg tk_s (i:rest) =
  let (prog, next) = canonProgStep tk_s !! i
  in prog :- canonProg next rest

-- Definition 32: canonical programs
-- One step programs, from given node to all immediate successors:
canonProgStep :: TableauxIP -> [(Prog, TableauxIP)]
canonProgStep End = []
canonProgStep (Node _ _ Nothing _ _ _ _) = error "Need type for canonProgStep."
canonProgStep si@(Node si_wfs _ (Just itype) si_history si_rule si_actives tks) =
  [ (progTo t, t) | t <- tks ] where
  progTo End = error "No program to End marker."
  progTo (Node _ _ Nothing _ _ _ _) = error "Need type for progTo."
  progTo (Node sj_wfs _ (Just jtype) _ _ _ _) = case (itype, jtype) of
    -- distinguish three cases:
    (Two, Three) -> Test $ Neg $ iOf undefined y where y = rightsOf sj_wfs
                    -- PROBLEM: iOf (Def 30) needs original TableauxIP ??
    (One, Two)   -> let
      tls = [ (tl, si_to_tl) -- TODO: si_to_tl, but we want sj_to_tl.
            -- QUESTION: What if si_to_tl does not include sj? Is that possible?
            | (si_to_tl , tl@(Node tl_wfs _ (Just One) _ _ _ _)) <- allSuccsOf si
            , tl_wfs == si_wfs ]
      n = length tls
      in if n == 0
           then Test top
           else Star $ multicup (map (uncurry canonProg) tls)
    (Three, One) ->
      if si_rule == "At"
        then let [(Neg (Box (Ap x) _), _)] = map collapse si_actives
             in Ap x -- Get program from active formula.
        else Test top
    ij -> error $ "Impossible transition in TK: " ++ show ij

-- Definition 33: Interpolants for T^K nodes
ipFor :: TableauxIP -> TableauxIP -> Form
-- end nodes of T^K:
ipFor _ End = error "No interpolants for End markers!"
ipFor topT (Node t_wfs _ _ _ _ _ [])
  | not $ any (\_ -> undefined) history = iOf topT (rightsOf t_wfs)
  | otherwise = top
  where history = [ undefined ] :: [a] -- TODO: need history in NodeTK to check for pred-with-same-pair :-/
ipFor topT (Node _ _ _ _ _ _ s1_to_sn) -- n≤2
  | length s1_to_sn == 1 && x /= Test top = Box x (ipFor topT (head s1_to_sn))
  | otherwise = multicon $ map (ipFor topT) s1_to_sn
  where x = fst (head (canonProgStep (head s1_to_sn))) -- FIXME: rewrite to avoid unsafe head

-- General functions --

proveWithInt :: Form -> TableauxIP
proveWithInt f = ipt1 where
  t1 = prove f
  ipt0 = toEmptyTabIP t1 :: TableauxIP
  ipt1 = fillAllIPs ipt0

proveAndInterpolate :: (Form,Form) -> (TableauxIP,Maybe Form)
proveAndInterpolate (ante,cons)
  | not $ provable (ante --> cons) = error $ "This implication is not valid " ++ toString (ante --> cons)
  | otherwise = (ipt1,mip) where
      t1 = prove (ante --> cons)
      ipt0 = toEmptyTabIP t1 :: TableauxIP
      ipt1@(Node _ mip _ _ _ _ _) = fillAllIPs ipt0

interpolate :: (Form,Form) -> Maybe Form
interpolate = snd . proveAndInterpolate

isNice :: (Form,Form) -> Bool
isNice (f,g) = provable (f `imp` g)
            && atomsIn f /= [] && atomsIn g /= []
            && atomsIn f /= atomsIn g
            && (not . provable . Neg $ f)
            && (not . provable $ g)
