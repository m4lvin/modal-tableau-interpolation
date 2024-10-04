module Logic.PDL.Interpolation.ProofTree where

import Control.Monad (when)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (isRight)
import Data.GraphViz (shape, toLabel) -- TODO: Shape(PlainText)
import Data.GraphViz.Types.Monadic (edge, node)
import Data.GraphViz.Attributes.Complete hiding (Box, Star)
import qualified Data.GraphViz.Attributes.HTML as GVHTML
import Data.Maybe (listToMaybe, catMaybes, mapMaybe)
import Data.List ((\\), intercalate, isInfixOf, isPrefixOf, sort)
import Data.Text.Lazy (pack)

import Logic.PDL
import Logic.PDL.Prove.Tree hiding (Node,End)
import qualified Logic.PDL.Prove.Tree as T (Tableaux(Node,End))
import Logic.Internal
import Logic.PDL.Interpolation ()

-- | An interpolant might be there, or not.
type Interpolant = Maybe Form

-- * Tableaux with interpolants

-- | A Tableau with interpolants.
data TableauxIP = Node
                  { wfsOf :: [WForm]           -- ^ A list of (left/right) weighted (posisbly marked) formulas.
                  , mipOf :: Interpolant       -- ^ Maybe a formula that is an interpolant for this node.
                  , mtypOf :: Maybe TypeTK     -- ^ Type marker for \(T^K\).
                  , ruleOf :: RuleName         -- ^ Rule that is applied at this node.
                  , activesOf :: [WForm]       -- ^ Active formulas to which the rule is applied here.
                  , childrenOf :: [TableauxIP] -- ^ Child nodes, can be more than 2.
                  }
  deriving (Eq,Ord,Show)

-- | Type markers for \(T^K\) which is annotated with 1,2,3.
data TypeTK = One | Two | Three
  deriving (Eq,Ord,Show)

showTyp :: TypeTK -> String
showTyp One   = "1"
showTyp Two   = "2"
showTyp Three = "3"

isEndNode :: TableauxIP -> Bool
isEndNode (Node _ _ _ _ _ []) = True
isEndNode _ = False

hasIP :: TableauxIP -> Bool
hasIP (Node _ (Just _) _ _ _ _) = True
hasIP (Node _ Nothing  _ _ _ _) = False

ppIP :: Interpolant -> String
ppIP (Just f) = toString f
ppIP Nothing  = "∅"

-- | Pretty-print a list of WForms, optionally with a 1/2/3-type.
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

-- TODO: use colors to highlight loaded formulas in HTML output?
instance DispAble TableauxIP where
  toGraph = toGraph' "" where
    toGraph' pref (Node wfs mip mtyp rule actives ts) = do
      node pref [shape PlainText, Label $ HtmlLabel $ GVHTML.Text
                  [ GVHTML.Str $ pack $ ppWFormsTyp mtyp wfs actives
                  , GVHTML.Format GVHTML.Bold [GVHTML.Str $ pack "  ::  "]
                  , GVHTML.Str $ pack $ ppIP mip] ]
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

-- | Convert a Tableaux to a TableauxIP (with no interpolants yet).
toEmptyTabIP :: Tableaux -> TableauxIP
toEmptyTabIP T.End = error "Cannot convert End nodes to TableauxIP."
toEmptyTabIP (T.Node wfs _ rule actives [T.End]) =
  Node wfs Nothing Nothing rule actives []
toEmptyTabIP (T.Node wfs _ rule actives ts) =
  Node wfs Nothing Nothing rule actives (map toEmptyTabIP ts)

-- | Check three conditions for a formula to be a correct interpolant for the root of a tableau.
checkCorrectIPfor :: Form -> TableauxIP -> (Bool, Bool, Bool)
checkCorrectIPfor f (Node wfs _ _ _ _ _ ) =
  ( atomsIn f ⊆ (atomsIn (leftsOf wfs) ∩ atomsIn (rightsOf wfs))
  , inconsistent (Neg f : leftsOf wfs)
  , inconsistent (f : rightsOf wfs)
  )

-- | Check if a formula is a correct interpolant for the root of a tableau.
isCorrectIPfor :: Form -> TableauxIP -> Bool
isCorrectIPfor f n = vocCon && left && right
  where (vocCon,left,right) = checkCorrectIPfor f n

-- | Get interpolant at the root of a tableau, assuming there is one.
ipOf :: TableauxIP -> Form
ipOf (Node _ (Just f ) _ _ _ _) = f
ipOf n@(Node _ Nothing   _ _ _ _) = error $ "No interpolant here (yet):" ++ ppTabStr n

-- | Get left or right formulas, and ignore markings!
leftsOf, rightsOf :: [WForm] -> [Form]
leftsOf  wfs = [f | (Left  f,_) <- wfs]
rightsOf wfs = [f | (Right f,_) <- wfs]

-- * The easy part

-- | Definition 26: given \(T\), remove n-nodes to obtain \(T^I\).
-- This may result in a non-binary tree!
tiOf :: TableauxIP -> TableauxIP
tiOf t = if null (tiOfRec t)
  then Node [] Nothing Nothing "" [] [] -- nothing left after deleting n-nodes!
  else snd . head . tiOfRec $ t
  where
  -- When node n is deleted the parent of n must append rule of n to its own rule.
  -- Given my child n, what should I add to my rule and what replaces n?
  tiOfRec  :: TableauxIP -> [(RuleName,TableauxIP)]
  tiOfRec n
    | isNormalNode (wfsOf n) = let childs = concatMap tiOfRec (childrenOf n)
                               in [ ("", n { ruleOf = combine (ruleOf n : map fst childs)
                                           , childrenOf = map snd childs } ) ]
    | otherwise = -- delete n itself!
        map (\(childRule, ct) -> (combine [ruleOf n, childRule], ct)) $ concatMap tiOfRec (childrenOf n)
  -- Combine rules without inserting too many commas.
  combine :: [RuleName] -> RuleName
  combine [] = ""
  combine ("":rs) = combine rs
  combine [rule] = rule
  combine (rule:rest) = rule ++ [',' | not . null $ combine rest] ++ combine rest

-- | Given a list of children, combine all previous interpolants
-- with a connective depending on the side that differs.
-- Based on Lemma 15. Note that there may be 1, 2 or more children!
branchIP :: [WForm] -> [TableauxIP] -> Maybe Form
branchIP _   [] = error "No children given!"
branchIP wfs ts = Just $ foldl1 connective (map ipOf ts) where
  connective
    | all (\t -> rightsOf wfs == rightsOf (wfsOf t)) ts = dis -- left side is active, use disjunction
    | all (\t -> leftsOf  wfs == leftsOf  (wfsOf t)) ts = Con -- right side is active, use conjunction
    | otherwise = error $ "Cannot combine interpolants when both sides change:\n" ++ show wfs ++ "\n\n" ++ intercalate "\n" (map show ts)

-- | Fill interpolants for the easy cases, not involving extra conditions.
-- Based on Lemma 14 and Lemma 15.
fillIPs :: TableauxIP -> TableauxIP
-- Ends and already interpolated nodes: nothing to do:
fillIPs t@(Node _ (Just _) _ _ _ _) = t
-- Lemma 14: Closed end nodes: use the active formulas or a constant as interpolant:
fillIPs (Node wfs Nothing mtyp "✘" actives []) = Node wfs mip mtyp "✘" actives [] where -- QUESTION: Why [] and not [End] here?
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
-- If right side is empty, then ⊥ is an interpolant:
  | null (rightsOf wfs) = Node wfs (Just Bot) Nothing rule actives ts
-- Lemma 15: Non-end nodes where children already have IPs: distinguish rules
  | otherwise = let
      newMIP = case (rule,actives,ts) of
        -- critical rule: prefix previous interpolant with diamond or Box, depending on active side
        -- if the other side is empty, use ⊥ or T, because <a>T and T have different voc (page 44)
        ("At",[(Left  (Neg (Box (Ap x) _)),_)],[t]) ->
          Just $ if null $ catMaybes [ projection x g | (Right g, _) <- wfs ] then Bot else dia (Ap x) (ipOf t)
        ("At",[(Right (Neg (Box (Ap x) _)),_)],[t]) ->
          Just $ if null $ catMaybes [ projection x g | (Left g, _) <- wfs ] then top else Box (Ap x) (ipOf t)
        ("At", _, _) -> error $ "Critical rule applied to " ++ ppWForms wfs actives ++ "\n  Unable to interpolate: " ++ show n
        -- end nodes due to extra condition 6:
        ('6':_,_, []) -> Nothing -- end node due to condition 6, deal with it later!
        -- There should not be any empty cases:
        (rl  ,_, []) -> error $ "Rule " ++ rl ++ " applied to " ++ ppWForms wfs actives ++ "\n  Unable to interpolate: " ++ show n
        -- Default case is to use branchIP (Lemma 15):
        (_, _, _) -> branchIP wfs ts
      in Node wfs newMIP Nothing rule actives ts

-- | Use fillIPs as often as possible.
fillAllIPs :: TableauxIP -> TableauxIP
fillAllIPs = fixpoint fillIPs

-- * The hard part: condition 6 end nodes

-- ** Find lowest \(M+\) to get \(T^J\)

-- | Find a lowest \(M+\) application without interpolant.
lowestMplusWithoutIP :: TableauxIP -> Maybe TableauxIP
lowestMplusWithoutIP n@(Node _ Nothing _ rule _ _) | "M+" `isInfixOf` rule =
  case mapMaybe lowestMplusWithoutIP (childrenOf n) of
    [] -> Just n
    _  -> listToMaybe $ mapMaybe lowestMplusWithoutIP (childrenOf n)
lowestMplusWithoutIP n = listToMaybe $ mapMaybe lowestMplusWithoutIP (childrenOf n)

-- | Find a lowest \(M+\) application without interpolant and fill it via \(T^J\) and \(T^K\).
fillLowestMplus :: TableauxIP -> TableauxIP
fillLowestMplus n@(Node _ Nothing _ rule _ _)
  | "M+" `isInfixOf` rule && null (mapMaybe lowestMplusWithoutIP (childrenOf n)) =
      let
        -- NOTE: The remark before Defintiion 27 wlog assumes M+ is applied in Y2 (Right).
        -- If instead it is in Y1 (Left) then we flip the tableau (which also negates all
        -- interpolants already found) ...
        isOnRight = or [ True | (Right _, _) <- activesOf n ]
        ti = if isOnRight then n else flipTab n
        tj = tjOf (head $ childrenOf ti)
        tk = tkOf tj
      in
        -- ... and negate the TK interpolant to get our interpolant for the root of n.
        n { mipOf = Just $ simplify $ (if isOnRight then id else Neg) $ ipFor tj tk [] }
fillLowestMplus n = n { childrenOf = map fillLowestMplus (childrenOf n) }

-- | Swap the left and right components in all nodes and
-- replace interpolants found so far by their (non-)negations.
flipTab :: TableauxIP -> TableauxIP
flipTab (Node wfs mip mtyp rule actives ts) =
  Node (map flipWForm wfs) (flipIP mip) mtyp rule actives (map flipTab ts) where
    flipWForm (Right f, m) = (Left  f, m)
    flipWForm (Left  f, m) = (Right f, m)
    flipIP Nothing        = Nothing
    flipIP (Just (Neg f)) = Just f
    flipIP (Just f)       = Just (Neg f)

-- | Definition 27: sub-tableau \(T^J\)
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

-- ** Definition 28

-- | \(D(T)\): disjunction of conjunctions of each of the given nodes (of \(T^J\))
dOf :: [[WForm]] -> Form
dOf tjNodes = multidis [ multicon (leftsOf wfs) | wfs <- tjNodes ]
-- | \(T(Y)\): all nodes where the right side is Y
tOf :: TableauxIP -> [Form] -> [Path]
tOf tj y = filter (seteq y . rightsOf . wfsOf . at tj) (allPathsIn tj)
-- | \(D(T(Y)\)
dtyOf :: TableauxIP -> [Form] -> Form
dtyOf t y = dOf $ map (wfsOf . at t) $ tOf t y

-- ** Paths and Histories

-- | A path in a tableau, given by the indices to go from start to end.
type Path = [Int]

at :: TableauxIP -> Path -> TableauxIP
at n [] = n
at n@(Node _ _ _ _ _ ts) (i:rest)
  | i > (length ts - 1) = error $ "This node has no child " ++ show i ++ ":\n" ++ ppTabStr n
  | otherwise = (ts !! i) `at` rest

allPathsIn :: TableauxIP -> [Path]
allPathsIn (Node _ _ _ _ _ ts) = [] : [ i:rest | (i,t) <- zip [0..] ts, rest <- allPathsIn t ]

-- | History from root until just before the node given by a path.
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

-- | Definition 15: ◁' which is ◁ plus "loops" (page 21, needed for Def 29)
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

-- ** Definition 29: partition of T(Y)

-- | \(T(Y)^ε\)
tOfEpsilon :: TableauxIP -> [Form] -> [Path]
tOfEpsilon tabTJ y = [ root_to_s | root_to_s <- tOf tabTJ y
                                 , not $ any (trianglePrime tabTJ root_to_s) (tOf tabTJ y) ]
-- | \(T(Y)^I\) — These are nodes where we (should) already have interpolants!
tOfI :: TableauxIP -> [Form] -> [Path]
tOfI tabTJ y = filter (\root_to_s -> not $ any (trianglePrime tabTJ root_to_s) (allPathsIn tabTJ))
                      (tOfEpsilon tabTJ y)
-- | \(T(Y)^◁\)
tOfTriangle :: TableauxIP -> [Form] -> [Path]
tOfTriangle tabTJ y = tOfEpsilon tabTJ y \\ tOfI tabTJ y

-- ** Building \(T^K\)

-- | Definition 30: I(Y)
-- NOTE: different from ipOf
iOf :: TableauxIP -> [Form] -> Form
iOf tj y = case tOfI tj y of
  [] -> Bot
  t1_tn -> multidis [ t_i | (Just t_i) <- map (mipOf . at tj) t1_tn ]

-- | Definition 31: \(T^K\)
-- Idea: Nodes in \(T^K\) correspond to \(Y\)-regions in \(T^J\).
-- Input should be the node Y1/Y2 obtained using M+ (page 35).
tkOf :: TableauxIP -> TableauxIP
tkOf n@(Node _ (Just _) _ _ _ _) = error $ "Already have an interpolant, why bother with T^K?\n" ++ ppTabStr n
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

-- | Successors in \(T^K\), three cases as in Definition 31.
tkSuccessorsAt :: TableauxIP -> TableauxIP -> Path -> [TableauxIP]
tkSuccessorsAt tj tk pth =
  case mtyp of
-- 1 has one or no successors:
  Just One ->
      [ Node
        ((Left (dOf (map (wfsOf . at tj) $ tOf tj y)), Nothing) : yWithMarkings)
        Nothing -- no interpolants in TK??
        (Just Two)
        "" -- anarchy, no rule!?
        [] -- no actives??
        (tkSuccessorsAt tj tk (pth ++ [0]))
      | not $ or [ otherWfs == wfs -- end node if there is a predecessor t with same pair and k(t)=1
                 | (Node otherWfs _ (Just One) _ _ _)  <- historyTo tk pth ] ]
-- 2 has one or no successors:
  Just Two ->
      [ Node
        ((Left (dOf (map (wfsOf . at tj) $ tOfTriangle tj y)), Nothing) : yWithMarkings)
        Nothing -- no interpolants in TK??
        (Just Three)
        (ruleOf witness)
        (activesOf witness) -- needed for Def 32 below
        (tkSuccessorsAt tj tk (pth ++ [0]))
      | not (null (tOfTriangle tj y))  -- end node when T(Y)◁ is empty
      , let witness = at tj $ head $ tOfTriangle tj y ] -- CHOICE! -- should only matter for Three-to-One, why is this here?
-- 3 has n many successors:
  Just Three ->
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
  Nothing -> error $ "No type given in TK" ++ ppTabStr n
  where
    n@(Node wfs _ mtyp _ _ _) = tk `at` pth
    y = rightsOf wfs
    yWithMarkings = filter (isRight . fst) wfs

-- | All successors of a node in a TK tableau, with the paths to them.
-- This is <, transitive closure of ◁.
allSuccsOf :: TableauxIP -> [(Path, TableauxIP)]
allSuccsOf (Node _ _ _ _ _ tks) = nexts ++ laters where
  nexts = zip [[0],[1]] tks
  laters = [ (i:path,suc)
           | ([i],tk) <- nexts
           , (path,suc) <- allSuccsOf tk ]

-- | Canonical program along a path in \(T^K\)
canonProg :: TableauxIP -> TableauxIP -> TableauxIP -> Path -> Prog
canonProg _  _  _    []  = error "No canonical program for empty path."
canonProg tj tk tk_s [t_index]
  | t_index > length (canonProgStep tj tk tk_s) - 1 =
      error $ "This node has no child " ++ show t_index ++ ":\n\n" ++ ppTabStr tk_s
  | otherwise = fst $ canonProgStep tj tk tk_s !! t_index
canonProg tj tk tk_s (i:rest)
  | i > length (canonProgStep tj tk tk_s) - 1 =
      error $ "This node has no child " ++ show i ++ ":\n" ++ ppTabStr tk_s
  | otherwise =
    let (prog, next) = canonProgStep tj tk tk_s !! i
    in prog :- canonProg tj tk next rest

-- | Definition 32: canonical programs.
-- One step from given node \(s^i\) in \(T^K\) to all immediate successors \(s^j\) in \(T^K\).
-- Assumption: we already have canonical programs for all nodes below \(s^j\).
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
      if "At" `isInfixOf` si_rule
      -- NOTE: But what if there are multiple rules in one step?
      -- No worries, multiple (At) steps will never be merged, see condition 3. -- CHECKME
        then case map collapse si_actives of
                [(Neg (Box (Ap x) _), _)] -> Ap x -- Get program from active formula.
                l -> error $ "Could not find program for (At) application):" ++ show l
        else Test top
    ij -> error $ "Impossible transition in TK: " ++ show ij

-- | Definition 33: Interpolants for \(T^K\) nodes
ipFor :: TableauxIP -> TableauxIP -> Path -> Form
-- end nodes of T^K:
ipFor tj tk pth
  | null s1_sn && not (or [ t_wfs == otherWfs && t_mtyp == otherMtyp -- QUESTION: "same pair" here seems to imply same type!?
                          | (Node otherWfs _ otherMtyp _ _ _) <- historyTo tk pth ]) =
      iOf tj (rightsOf t_wfs) -- end node with no same-pair predecessor, use I(t) := I(Y).
  | null s1_sn = top -- all other end nodes get I(t):=1.
  | length s1_sn == 1 && a_prog /= Test top = Box a_prog (ipFor tj tk (pth ++ [0])) -- QUESTION: a_prog might not be in vocab!?
  | otherwise = multicon $ [ ipFor tj tk $ pth ++ [k]
                           | (k,_) <- zip [0,1] (childrenOf (tk `at` pth)) ]
  where
    n@(Node t_wfs _ t_mtyp _ _ s1_sn) = tk `at` pth -- NOTE: n≤2
    (a_prog, _) = head $ canonProgStep tj tk n

-- | Annotate \(T^K\) with canonical programs (as rules) and interpolants.
annotateTk :: TableauxIP -> TableauxIP -> TableauxIP
annotateTk tj tk = annotateInside [] where
  annotateInside pth =
    let n = tk `at` pth
    in n { mipOf = Just (ipFor tj tk pth)
         , ruleOf = intercalate " // " $ map (toString . fst) (canonProgStep tj tk n)
         , childrenOf = [ annotateInside (pth ++ [k]) | (k,_) <- zip [0,1] (childrenOf n) ]  }

-- ** Tools for the interpolant-is-an-interpolant proof

-- | Definition 34: Set \(J(s)\)
jSetOf :: TableauxIP -> TableauxIP -> Path -> [Form]
jSetOf _  _ [] = [] -- J(t_o) := {}
jSetOf tj tk pth_s = sort $ nubOrd $
  [ if pth_s == pth_t' then formulaP else Box prog formulaP
  | pth_t <- allPathsIn tk, let t = tk `at` pth_t
  , pth_t' <- allPathsIn tk, let t' = tk `at` pth_t'
  , wfsOf t == wfsOf t' -- same pair -- FIXME: strict enough? do we have 1/2/3 types here?
  , pth_t `isProperPrefixOf` pth_s && pth_s `isPrefixOf` pth_t'
  , let pth_s_to_t' = drop (length pth_s) pth_t'
  , let prog = canonProg tj tk (tk `at` pth_s) pth_s_to_t'
  , formulaP <- jSetOf tj tk pth_t ++ [ ipOf (tk `at` pth_t) ]
  ]

-- | Definition 34: set \(K(s)\)
kSetOf :: TableauxIP -> TableauxIP -> Path -> [Form]
kSetOf tj tk pth = sort $ nubOrd $
  ipOf (tk `at` pth) : jSetOf tj tk pth ++ rightsOf (wfsOf $ tk `at` pth)

-- * General wrapper functions

-- | Keep iterating the whole procedure to (hopefully) find all interpolants.
keepInterpolating :: TableauxIP -> TableauxIP
keepInterpolating = fixpoint (fillLowestMplus . fillAllIPs)

-- | Try to prove the given formula and annotate the resulting tableau with interpolants.
proveWithInt :: Form -> TableauxIP
proveWithInt = keepInterpolating . tiOf . toEmptyTabIP . prove

-- | Interpolate a given valid implication; return tablau and interpolant.
proveAndInterpolate :: (Form,Form) -> (TableauxIP,Maybe Form)
proveAndInterpolate (ante,cons)
  | not $ provable (ante --> cons) = error $ "This implication is not valid " ++ toString (ante --> cons)
  | otherwise = (ipt1,mip) where
      t1 = prove (ante --> cons)
      ti = tiOf $ toEmptyTabIP t1 :: TableauxIP
      ipt1@(Node _ mip _ _ _ _) = keepInterpolating ti

-- | Interpolate a given valid implication; return only the interpolant.
interpolate :: (Form,Form) -> Maybe Form
interpolate = snd . proveAndInterpolate

-- | Check if a pair of formulas can serve as a nice non-trivial interpolation example.
-- Here \(\phi \to \psi\) is nice when it is provable, the two subformulas have
-- different and non-empty vocabularies, \(\lnot \phi\) is not provable, and
-- \(\psi\) is not provable. For efficiency we check the vocabularies first.
isNice :: (Form,Form) -> Bool
isNice (f,g) = atomsIn f /= [] && atomsIn g /= []
            && atomsIn f /= atomsIn g
            && (not . provable . Neg $ f)
            && (not . provable $ g)
            && provable (f `imp` g)
