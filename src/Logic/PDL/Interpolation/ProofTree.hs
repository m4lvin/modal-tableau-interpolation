module Logic.PDL.Interpolation.ProofTree where

import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.Maybe

import Logic.PDL
import Logic.PDL.Prove.Tree hiding (Node,End)
import qualified Logic.PDL.Prove.Tree as T (Tableaux(Node,End))
import Logic.Internal

type Interpolant = Maybe Form

-- | A Tableau with interpolants.
data TableauxIP = Node
                  [WForm]
                  Interpolant -- ^ Maybe a formula that is an interpolant for this node.
                  History
                  RuleName
                  [WForm]
                  [TableauxIP]
                | End
  deriving (Eq,Ord,Show)

ppIP :: Interpolant -> String
ppIP (Just f) = toString f
ppIP Nothing  = "∅"

instance DispAble TableauxIP where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "."]
    toGraph' pref (Node wfs ip _ rule actives ts) = do
      node pref [shape PlainText, toLabel $ ppWForms wfs actives ++ "  ::  " ++ ppIP ip]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

toEmptyTabIP :: Tableaux -> TableauxIP
toEmptyTabIP T.End = End
toEmptyTabIP (T.Node wfs history rule actives ts) =
  Node wfs Nothing history rule actives (map toEmptyTabIP ts)

forgetIPs :: TableauxIP -> Tableaux
forgetIPs End = T.End
forgetIPs (Node wfs _ history rule actives ts) =
  T.Node wfs history rule actives (map forgetIPs ts)

hasIP :: TableauxIP -> Bool
hasIP End = False
hasIP (Node _ (Just _) _ _ _ _) = True
hasIP (Node _ Nothing  _ _ _ _) = False

ipOf :: TableauxIP -> Form
ipOf End = error "End nodes do not have interpolants."
ipOf (Node _ (Just f ) _ _ _ _) = f
ipOf (Node _ Nothing   _ _ _ _) = error "No interpolant here."

-- Get left or right formulas, and ignore markings!
leftsOf, rightsOf :: [WForm] -> [Form]
leftsOf  wfs = [f | (Left  f,_) <- wfs]
rightsOf wfs = [f | (Right f,_) <- wfs]

interpolateNode :: [WForm] -> [Form]
interpolateNode wfs = filter evil (leftsOf wfs) where
  evil (Neg f) = f `elem` rightsOf wfs || Neg (Neg f) `elem` rightsOf wfs
  evil f       = Neg f `elem` rightsOf wfs


-- For any branching rule we combine the two previous interpolants
-- with a connective depending on the side of the active formula (see page ??)
branchIP :: ([TableauxIP] -> [(Either Form Form, Maybe Form)] -> Maybe Form)
branchIP [t1,t2] actives  = Just $ connective (ipOf t1) (ipOf t2) where
  connective = case actives of
    [(Left  _, _)] -> dis -- left side is active, use disjunction
    [(Right _, _)] -> Con -- right side is active, use conjunction
    _              -> error $ "Could not find the active side: " ++ show actives
branchIP _ _ = undefined

fillIPs :: TableauxIP -> TableauxIP
-- Ends and already interpolated nodes: nothing to do:
fillIPs End = End
fillIPs t@(Node _ (Just _) _ _ _ _) = t
-- Closed end nodes: use the active formulas or a constant as interpolant:
fillIPs (Node wfs Nothing history "✘" actives [End]) = Node wfs mip history "✘" actives [End] where
  candidates = map fst actives -- NOTE: ignore markings
  mip = listToMaybe $ lrIp candidates
  lrIp fs = [ Bot | Left  Bot `elem` fs ]
         ++ [ top | Right Bot `elem` fs ]
         ++ [     f | Left  f <- fs, Right (Neg f) `elem` fs ]
         ++ [ Neg f | Right f <- fs, Left  (Neg f) `elem` fs ]
         ++ [ Bot   | Left  f <- fs, Left  (Neg f) `elem` fs ] -- inconsistency implies bot
         ++ [ top   | Right f <- fs, Right (Neg f) `elem` fs ] -- top implies Neg inconsistency
fillIPs n@(Node wfs Nothing history rule actives ts)
-- Non-end nodes where children are missing IPs: recurse
  | not (all hasIP ts) = Node wfs Nothing history rule actives (map fillIPs ts)
-- If left side is empty, then T is an interpolant:
  | null (leftsOf wfs) = Node wfs (Just top) history rule actives ts
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
        (rl  ,_) -> error $ "Rule " ++ rl ++ " applied to " ++ ppWForms wfs actives ++ " Unable to interpolate!:\n" ++ show n
      in Node wfs newMIP history rule actives ts

fillAllIPs :: TableauxIP -> TableauxIP
fillAllIPs = fixpoint fillIPs -- TODO is this necessary?

-- Definitions to deal with condition 6 end nodes

wfsOf :: TableauxIP -> [WForm]
wfsOf (Node wfs _ _ _ _ _) = wfs
wfsOf End = []

-- Definition 27: sub-tableau T^J
tj :: TableauxIP -> TableauxIP
tj (Node wfs ip history rule actives ts) =
  Node wfs ip history rule actives (if stop then [] else map tj ts) where
  stop = or
    [ False -- TODO: stop at M- rule
    , (not . isLoadedNode) wfs -- Stop at free nodes.
    , length ts == 1 && null (leftsOf (wfsOf (head ts))) -- Stop when first component of (unique!?) successor is empty.
    , wfs `elem` map fst history -- Stop when there is a predecessor with same pair. -- FIXME? History might go too far up?
    ]
tj End = End

-- helper for Def 28
allWfsOf :: TableauxIP -> [[WForm]]
allWfsOf (Node wfs _ _ _ _ ts) = wfs : concatMap allWfsOf ts
allWfsOf End = []

-- Definition 28
-- D(T): disjunction of conjunctions of all formulas in all nodes of T^J
dt :: TableauxIP -> Form
dt tj = multidis [ multicon [ f
                            | (Left f, _) <- wfs ] -- QUESTION: ignoring marking is okay?
                 | wfs <- allWfsOf tj ]
-- T(Y): all nodes where the right side is Y
nodesWithThisLeftPart :: TableauxIP -> [Form] -> [[WForm]]
nodesWithThisLeftPart t y = filter (seteq y . rightsOf) (allWfsOf t)

-- Definition 29:
-- T(Y)^ε
tOfEpsilon :: TableauxIP -> [Form] -> [TableauxIP]
tOfEpsilon t y = undefined -- TODO!
-- T(Y)^I
tOfI :: TableauxIP -> [Form] -> [TableauxIP] -- nodes where we (should) already have interpolants!
tOfI t y = undefined -- TODO!
-- T(Y)^◁
tOfTriangle :: TableauxIP -> [Form] -> [TableauxIP]
tOfTriangle t y = undefined -- TODO!

-- Definition 30: I(Y)
iOf :: TableauxIP -> [Form] -> Form
iOf t y = case tOfI t y of
  [] -> Bot
  ts -> multidis (map ipOf ts)

-- Alternative kind of tableau for T^K. No rules, no actives, but annotated with 1,2,3.
data TypeTK = One | Two | Three
  deriving (Eq,Ord,Show)

data TK = NodeTK
          [WForm]
          TypeTK
          Interpolant -- ^ Maybe a formula that is an interpolant for this node.
          -- History -- TODO: do we need it here?
          [TK]
        | EndTK
  deriving (Eq,Ord,Show)

-- Definition 31: T^K
-- Idea: Nodes in T^K here correspond to Y-regions in T^J.
tk :: TableauxIP -> TK
tk = undefined

-- Definition 32: canonical programs, from given node to all immediate successors
canonProg :: TK -> [(Prog, TK)]
canonProg = undefined -- TODO: distingusih three cases
-- Two Three
-- One Two
-- Three One

-- Definition 33
-- TODO

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
