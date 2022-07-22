module Logic.PDL.Interpolation.ProofTree where

import Control.Monad (when)
import Data.Either (isRight)
import Data.GraphViz (shape, Shape(PlainText), toLabel)
import Data.GraphViz.Types.Monadic (edge, node)
import Data.Maybe (listToMaybe, catMaybes, mapMaybe)
import Data.List ((\\), intercalate, isPrefixOf)

import Logic.PDL
import Logic.PDL.Prove.Tree hiding (Node,End)
import qualified Logic.PDL.Prove.Tree as T (Tableaux(Node,End))
import Logic.Internal

type Interpolant = Maybe Form

-- | A Tableau with interpolants.
data TableauxIP = Node
                  { wfsOf :: [WForm]
                  , mipOf :: Interpolant -- ^ Maybe a formula that is an interpolant for this node.
                  , mtypOf :: Maybe TypeTK
                  , ruleOf :: RuleName
                  , activesOf :: [WForm]
                  , childrenOf :: [TableauxIP] }
  deriving (Eq,Ord,Show)

-- Type markers for T^K which is annotated with 1,2,3.
data TypeTK = One | Two | Three
  deriving (Eq,Ord,Show)

showTyp :: TypeTK -> String
showTyp One   = "1"
showTyp Two   = "2"
showTyp Three = "3"

isEndNode :: TableauxIP -> Bool
isEndNode (Node _ _ _ _ _ []) = True
isEndNode _ = False

ppIP :: Interpolant -> String
ppIP (Just f) = toString f
ppIP Nothing  = "∅"

ppWFormsTyp :: Maybe TypeTK -> [WForm] -> [WForm] -> String
ppWFormsTyp mtyp wfs actives = concat
  [ intercalate ", " (map ppFormA (filter isLeft wfs))
  , "   |"
  , maybe "" showTyp mtyp
  , "   "
  , intercalate ", " (map ppFormA (filter (not . isLeft) wfs)) ]
  where
    ppFormA wf = [ '»' |  wf `elem` actives ]
              ++ removePars (toString (collapse wf))
              ++ [ '«' |  wf `elem` actives ]
    removePars ('(':rest) | last rest == ')' = init rest
    removePars str = str

instance DispAble TableauxIP where
  toGraph = toGraph' "" where
    toGraph' pref (Node wfs mip mtyp rule actives ts) = do
      node pref [shape PlainText, toLabel $ ppWFormsTyp mtyp wfs actives ++ "  ::  " ++ ppIP mip]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])
      when (null ts) $ do
        node (pref ++ "end") [shape PlainText, toLabel "."]
        edge pref (pref ++ "end") [toLabel rule]

ppTab :: TableauxIP -> IO ()
ppTab = putStr . ppTabStr

ppTabStr :: TableauxIP -> String
ppTabStr = ppTab' "" where
  ppTab' pref (Node wfs mip mtyp rule actives ts) =
    let mipstr = maybe "" (("I = " ++) . toString) mip
    in pref ++ ppWFormsTyp mtyp wfs actives ++ "      " ++ mipstr ++ "\n"
       ++
       pref ++ "(" ++ rule ++ ")"  ++ "\n"
       ++
       concatMap (\t -> (if length ts > 1 then pref ++ ".\n" else "") ++ ppTab' (pref ++ if length ts > 1 then "   " else "") t) ts

toEmptyTabIP :: Tableaux -> TableauxIP
toEmptyTabIP T.End = error "boom"
toEmptyTabIP (T.Node wfs _ rule actives [T.End]) =
  Node wfs Nothing Nothing rule actives []
toEmptyTabIP (T.Node wfs _ rule actives ts) =
  Node wfs Nothing Nothing rule actives (map toEmptyTabIP ts)

hasIP :: TableauxIP -> Bool
hasIP (Node _ (Just _) _ _ _ _) = True
hasIP (Node _ Nothing  _ _ _ _) = False

ipOf :: TableauxIP -> Form
ipOf (Node _ (Just f ) _ _ _ _) = f
ipOf n@(Node _ Nothing   _ _ _ _) = error $ "No interpolant here (yet):" ++ ppTabStr n

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

-- | Fill interpolants for the easy cases, not involving extra conditions.
fillIPs :: TableauxIP -> TableauxIP
-- Ends and already interpolated nodes: nothing to do:
fillIPs t@(Node _ (Just _) _ _ _ _) = t
-- Closed end nodes: use the active formulas or a constant as interpolant:
fillIPs (Node wfs Nothing mtyp "✘" actives []) = Node wfs mip mtyp "✘" actives [] where
  candidates = map fst actives -- NOTE: ignore markings
  mip = listToMaybe $ lrIp candidates
  lrIp fs = [ Bot | Left  Bot `elem` fs ]
         ++ [ top | Right Bot `elem` fs ]
         ++ [     f | Left  f <- fs, Right (Neg f) `elem` fs ]
         ++ [ Neg f | Right f <- fs, Left  (Neg f) `elem` fs ]
         ++ [ Bot   | Left  f <- fs, Left  (Neg f) `elem` fs ] -- inconsistency implies bot
         ++ [ top   | Right f <- fs, Right (Neg f) `elem` fs ] -- top implies Neg inconsistency
fillIPs n@(Node wfs Nothing _ rule actives ts)
-- Non-end nodes where children are missing IPs: recurse
  | not (all hasIP ts) = Node wfs Nothing Nothing rule actives (map fillIPs ts)
-- If left side is empty, then T is an interpolant:
  | null (leftsOf wfs) = Node wfs (Just top) Nothing rule actives ts
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
        ("n" ,_) -> Just $ ipOf t where [t] = ts
        ("M+",_) -> Just $ ipOf t where [t] = ts -- Start of a T^J, deal with it later!
        ("M-",_) -> Just $ ipOf t where [t] = ts
        -- for the branching rule we combine the two previous interpolants
        -- with a connective depending on the side of the active formula:
        ("¬∧",_) -> branchIP ts actives
        ("?" ,_) -> branchIP ts actives
        ("¬∪",_) -> branchIP ts actives
        ("¬n",_) -> branchIP ts actives
        -- critical rule: prefix previous interpolant with diamond or Box, depending on active side
        -- if the other side is empty, use ⊥ or T, because <a>T and T have different voc (page 44)
        ("At",[(Left  (Neg (Box (Ap x) _)),_)]) ->
          let [t] = ts
          in Just $ if null $ catMaybes [ projection x g | (Right g, _) <- wfs ] then Bot else dia (Ap x) (ipOf t)
        ("At",[(Right (Neg (Box (Ap x) _)),_)]) ->
          let [t] = ts
          in Just $ if null $ catMaybes [ projection x g | (Left g, _) <- wfs ] then top else Box (Ap x) (ipOf t)
        -- end nodes due to extra conditions:
        ('4':_,_) -> Nothing
        ('6':_,_) -> Nothing
        -- There should not be any remaining cases:
        (rl  ,_) -> error $ "Rule " ++ rl ++ " applied to " ++ ppWForms wfs actives ++ "\n  Unable to interpolate: " ++ show n
      in Node wfs newMIP Nothing rule actives ts

fillAllIPs :: TableauxIP -> TableauxIP
fillAllIPs = fixpoint fillIPs -- FIXME: is this necessary?

-- Definitions to deal with condition 6 end nodes

-- Definition 26: remove n-nodes to obtain T^I
tiOf :: TableauxIP -> TableauxIP
tiOf n@(Node wfs mip mtyp rule actives ts)
  | not (isNormalNode wfs) = error "Too late, cannot delete this n-node."
  -- if all children are normal, then just recurse: (this also deals with [], i.e. end nodes)
  | all (isNormalNode . wfsOf) ts = Node wfs mip mtyp rule actives (map tiOf ts)
  -- if there is exactly one child and it is non-normal, then remove it and adopt its children:
  | length ts == 1 && not (isNormalNode (wfsOf (head ts))) =
      let
        new_rule = rule ++ "," ++ ruleOf (head ts)
        new_ts = childrenOf (head ts)
      in tiOf $ Node wfs mip mtyp new_rule actives new_ts
  -- Example: [a*]p -> [a**]p matters for the next two cases?!
  -- if there are two children and one is a non-normal end node, then just remove it.
  | length ts == 2
    && length (filter (isNormalNode . wfsOf) ts) == 1
    && null (childrenOf (head (filter (not . isNormalNode . wfsOf) ts))) =
      let
        new_ts = filter (isNormalNode . wfsOf) ts
      in tiOf $ Node wfs mip mtyp rule actives new_ts
  -- if there are two children and one is a non-normal node with at most one normal child, then replace it by that child.
  | length ts == 2
    && length (filter (not . isNormalNode . wfsOf) ts) == 1
    && length (filter (isNormalNode . wfsOf) $ childrenOf (head (filter (not . isNormalNode . wfsOf) ts))) <=1  =
      let
        new_ts = filter (isNormalNode . wfsOf) ts ++ filter (isNormalNode . wfsOf) (childrenOf (head (filter (not . isNormalNode . wfsOf) ts)))
      in tiOf $ Node wfs mip mtyp rule actives new_ts
  -- Otherwise, give up!
  | otherwise = error $ "Tricky situation, cannot define T^I:\n" ++ ppTabStr n
  -- QUESTION: What if there are multiple sucessors of an n-node?

-- Find a node where M+ is applied, we have no interpolant yet, and there is no such node below.
lowestMplusWithoutIP :: TableauxIP -> Maybe TableauxIP
lowestMplusWithoutIP n@(Node _ Nothing _ "M+" _ _) =
  case mapMaybe lowestMplusWithoutIP (childrenOf n) of
    [] -> Just n
    _ -> listToMaybe $ mapMaybe lowestMplusWithoutIP (childrenOf n)
lowestMplusWithoutIP n = listToMaybe $ mapMaybe lowestMplusWithoutIP (childrenOf n)

-- Definition 27: sub-tableau T^J
tjOf :: TableauxIP -> TableauxIP
tjOf = tjOf' [] where
  tjOf' history (Node wfs ip _ rule actives ts) =
    Node wfs ip Nothing rule actives (if stop then [] else map (tjOf' (wfs:history)) ts) where
    stop = or
      [ rule == "M-" -- Stop when the rule (M-) is applied.
      , (not . isLoadedNode) wfs -- Stop at free nodes.
      , length ts == 1 && null (leftsOf (wfsOf (head ts))) -- Stop when first component of (unique!?) successor is empty.
      , wfs `elem` history -- Stop when there is a predecessor with same pair.
      ]

-- Definition 28
-- D(T): disjunction of conjunctions of each of the given nodes (of T^J)
dOf :: [[WForm]] -> Form
dOf tjNodes = multidis [ multicon (leftsOf wfs) | wfs <- tjNodes ]
-- T(Y): all nodes where the right side is Y
tOf :: TableauxIP -> [Form] -> [Path]
tOf tj y = filter (seteq y . rightsOf . wfsOf . at tj) (allPathsIn tj)

dtyOf :: TableauxIP -> [Form] -> Form
dtyOf t y = dOf $ map (wfsOf . at t) $ tOf t y

-- A path, given by the indices to go from start to end.
type Path = [Int]

at :: TableauxIP -> Path -> TableauxIP
at n [] = n
at n@(Node _ _ _ _ _ ts) (i:rest)
  | i > (length ts - 1) = error $ "This node has no child " ++ show i ++ ":\n" ++ ppTabStr n
  | otherwise = (ts !! i) `at` rest

allPathsIn :: TableauxIP -> [Path]
allPathsIn (Node _ _ _ _ _ ts) = [] : [ i:rest | (i,t) <- zip [0..] ts, rest <- allPathsIn t ]

-- | History from root up to the node given by a path.
historyTo :: TableauxIP -> Path -> [TableauxIP]
historyTo _ [] = []
historyTo n@(Node _ _ _ _ _ ts) (i:rest)
  | i > (length ts - 1) = error $ "This node has no child " ++ show i ++ ":\n" ++ ppTabStr n
  | otherwise =  n : historyTo (ts !! i) rest

-- ≤
-- Data.List.isPrefixOf

-- <
isProperPrefixOf :: Path -> Path -> Bool
isProperPrefixOf p1 p2 = p1 `isPrefixOf` p2 && length p1 /= length p2

-- ◁
isImmediatePredOf :: Path -> Path -> Bool
isImmediatePredOf p1 p2 = p1 `isPrefixOf` p2 && length p1 + 1 == length p2

-- Definition 15: ◁' which is ◁ plus "loops" (page 21, needed for Def 29)
-- NOTE: s and t are given by paths from tab root; tab and sp need not be the same.
trianglePrime :: TableauxIP -> Path -> Path -> Bool
trianglePrime tab sp tp =
  sp `isImmediatePredOf` tp
  ||
  (    isEndNode (tab `at` sp)
    && any (\up -> up `isProperPrefixOf` sp
                   && up `isImmediatePredOf` tp
                   && wfsOf (tab `at ` up) == wfsOf (tab `at` sp))
           (allPathsIn tab) )

-- Definition 29:
-- T(Y)^ε
tOfEpsilon :: TableauxIP -> [Form] -> [Path]
tOfEpsilon tabTJ y = [ root_to_s | root_to_s <- tOf tabTJ y
                                 , not $ any (trianglePrime tabTJ root_to_s) (tOf tabTJ y) ]
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
iOf topT y = case tOfI topT y of
  [] -> Bot
  tsPths -> multidis (map (iOf topT . leftsOf . wfsOf . at topT) tsPths)

-- Definition 31: T^K
-- Idea: Nodes in T^K here correspond to Y-regions in T^J.
-- Input should be the node Y1/Y2 obtained using M+ (page 35)
tkOf :: TableauxIP -> TableauxIP
tkOf (Node _ (Just _) _ _ _ _) = error "Already have an interpolant, why bother with T^K?"
tkOf n@(Node t_wfs Nothing _ _ _ _) = tk where
  tk =
    Node
      ((Left (dtyOf n y2), Nothing) : yWithMarkings) -- D(T(Y2)) / Y2
      Nothing -- no interpolant yet at root
      (Just One)
      "" -- anarchy, no rule!?
      [] -- PROBLEM: no actives but needed in Def 32 later?!
      (tkSuccessorsAt n tk []) -- empty path to point to root
  y2 = rightsOf t_wfs
  yWithMarkings = filter (isRight . fst) t_wfs

-- Define the successors in T^K, three cases as in Definition 31.
tkSuccessorsAt :: TableauxIP -> TableauxIP -> Path -> [TableauxIP]
tkSuccessorsAt tj tk pth
-- 1 to 2 has one or no successors:
  | mtyp == Just One =
      [ Node
        ((Left (dOf (map (wfsOf . at tj) $ tOf tj y)), Nothing) : yWithMarkings)
        Nothing -- no interpolants in TK??
        (Just Two)
        "" -- anarchy, no rule!?
        [] -- no actives??
        (tkSuccessorsAt tj tk (pth ++ [0]))
      | not $ or [ otherWfs == wfs -- end node if there is a predecessor t with same pair and k(t)=1
                 | (Node otherWfs _ (Just One) _ _ _)  <- historyTo tk pth ] ]
-- 2 to 3 has one or no successors:
  | mtyp == Just Two =
      [ Node
        ((Left (dOf (map (wfsOf . at tj) $ tOfTriangle tj y)), Nothing) : yWithMarkings)
        Nothing -- no interpolants in TK??
        (Just Three)
        (ruleOf witness)
        (activesOf witness) -- needed for Def 32 below
        (tkSuccessorsAt tj tk (pth ++ [0]))
      | not (null (tOfTriangle tj y))  -- end node when T(Y)◁ is empty
      , let witness = at tj $ head $ tOfTriangle tj y ] -- CHOICE! -- should only matter for Three-to-One, why is this here?
-- 3 to 1 has n many successors:
  | mtyp == Just Three =
      [ Node
      ( (Left (dOf (map (wfsOf . at tj) $ tOf tj z)), Nothing)
        : [ mf | mf <- wfsOf childT, isRight (fst mf) ] )
        Nothing -- no interpolants in TK??
        (Just One)
        "" -- anarchy, no rule!?
        [] -- no actives??
        (tkSuccessorsAt tj tk (pth ++ [k]))
      | let (Node _ _ _ _ _ z1_zn) = at tj $ head $ tOfTriangle tj y -- CHOICE!
      , (k, childT) <- zip [0,1] z1_zn
      , let z = rightsOf (wfsOf childT) ]
  | otherwise = error $ "Wrong combination of type and number of children: " ++ ppTabStr n
  where
    n@(Node wfs _ mtyp _ _ _) = tk `at`pth
    y = rightsOf wfs
    yWithMarkings = filter (isRight . fst) wfs

-- All successors of a node in a TK tableau, with the paths to them.
-- This is <, transitive closure of ◁.
allSuccsOf :: TableauxIP -> [(Path, TableauxIP)]
allSuccsOf (Node _ _ _ _ _ tks) = nexts ++ laters where
  nexts = zip [[0],[1]] tks
  laters = [ (i:path,suc)
           | ([i],tk) <- nexts
           , (path,suc) <- allSuccsOf tk ]

-- | Canonical program from s to t along a path in TK
canonProg :: TableauxIP -> TableauxIP -> TableauxIP -> Path -> Prog
canonProg _  _  _    []  = error "No canonical program for empty path."
canonProg tj tk tk_s [t_index]
  | t_index > length (canonProgStep tj tk tk_s) - 1 = error $ "canonProg: This node has no child " ++ show t_index ++ ":\n\n" ++ ppTabStr tk_s
  | otherwise = fst $ canonProgStep tj tk tk_s !! t_index
canonProg tj tk tk_s (i:rest)
  | i > length (canonProgStep tj tk tk_s) - 1 = error $ "canonProg: This node has no child " ++ show i ++ ":\n" ++ ppTabStr tk_s
  | otherwise =
    let (prog, next) = canonProgStep tj tk tk_s !! i
    in prog :- canonProg tj tk next rest

-- Definition 32: canonical programs
-- One step programs, from given node si in TK to all immediate successors sj in TK.
-- Assumption: we already have canonical programs for all nodes below sj.
canonProgStep :: TableauxIP -> TableauxIP -> TableauxIP -> [(Prog, TableauxIP)]
canonProgStep _  _  (Node _      _ Nothing      _ _ _) = error "Need type for canonProgStep."
canonProgStep tj tk (Node si_wfs _ (Just itype) si_rule si_actives tks) =
  [ (progTo t, t) | t <- tks ] where
  progTo (Node _ _ Nothing _ _ _) = error "Need type for progTo."
  progTo sj@(Node sj_wfs _ (Just jtype) _ _ _) = case (itype, jtype) of
    -- distinguish three cases:
    (Two, Three) -> Test $ Neg $ iOf tj y where y = rightsOf sj_wfs -- NOTE: iOf (Def 30) needs tj
    (One, Two)   -> if null prs then Test top else Star $ multicup prs where
      -- NOTE: Borzechowski writes "all the successors of s^i", but here we use the successors of s^j,
      -- because per Definition 31 (One->Two case) s^i only has one immediate successor, namely s^j.
      prs = [ canonProg tj tk sj sj_to_tl -- FIXME ???
            | (sj_to_tl , Node tl_wfs _ (Just One) _ _ _) <- allSuccsOf sj
            , tl_wfs == si_wfs ]
    (Three, One) ->
      if si_rule == "At"
      -- NOTE: But what if there are multiple rules in one step?
      -- No worries, (At) will not be merged, see condition 3.
        then let [(Neg (Box (Ap x) _), _)] = map collapse si_actives
             in Ap x -- Get program from active formula.
        else Test top
    ij -> error $ "Impossible transition in TK: " ++ show ij

-- Definition 33: Interpolants for T^K nodes
ipFor :: TableauxIP -> TableauxIP -> Path -> Form
-- end nodes of T^K:
ipFor tj tk pth
  | null s1_sn && not (any (\(Node otherWfs _ _ _ _ _) -> t_wfs == otherWfs) (historyTo tk pth)) =
      iOf tk (rightsOf t_wfs) -- end node with no same-pair predecessor, use I(t) := I(Y).
  | null s1_sn = top -- all other end nodes get I(t):=1.
  | length s1_sn == 1 && a_prog /= Test top = Box a_prog (ipFor tj tk (pth ++ [0]))
  | otherwise = multicon $ [ ipFor tj tk $ pth ++ [k]
                           | (k,_) <- zip [0,1] (childrenOf (tk `at` pth)) ]
  where
    n@(Node t_wfs _ _ _ _ s1_sn) = tk `at` pth -- NOTE: n≤2
    ((a_prog, _):_) = canonProgStep tj tk n

-- | Annotate TK with canonical programs (instead of rules) and interpolants.
annotateTk :: TableauxIP -> TableauxIP -> TableauxIP
annotateTk tj tk = annotateInside [] where
  annotateInside pth =
    let n = tk `at` pth
    in n { mipOf = Just (ipFor tj tk pth)
         , ruleOf = intercalate " // " $ map (toString . fst) (canonProgStep tj tk n)
         , childrenOf = [ annotateInside (pth ++ [k]) | (k,_) <- zip [0,1] (childrenOf n) ]  }

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
      ipt1@(Node _ mip _ _ _ _) = fillAllIPs ipt0

interpolate :: (Form,Form) -> Maybe Form
interpolate = snd . proveAndInterpolate

isNice :: (Form,Form) -> Bool
isNice (f,g) = provable (f `imp` g)
            && atomsIn f /= [] && atomsIn g /= []
            && atomsIn f /= atomsIn g
            && (not . provable . Neg $ f)
            && (not . provable $ g)
