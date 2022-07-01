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
-- Non-end nodes where children already have IPs: distinguish rules
  | otherwise = Node wfs newMIP history rule actives ts where
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
        -- for the critical rule, we prefix the previous interpolant with diamond or Box, depending on the active side
        -- TODO: if one of the sides is empty, use Bot or Top as interpolants, because <a>T and T have different vocabulary - see page 44
        ("At",[(Left  (Neg (Box (Ap x) _)),_)]) -> let [t] = ts in Just $ dia (Ap x) $ ipOf t
        ("At",[(Right (Neg (Box (Ap x) _)),_)]) -> let [t] = ts in Just $ Box (Ap x) $ ipOf t
        (rl  ,_) -> error $ "Rule " ++ rl ++ " applied to " ++ ppWForms wfs actives ++ " Unable to interpolate!:\n" ++ show n

fillAllIPs :: TableauxIP -> TableauxIP
fillAllIPs = fixpoint fillIPs -- TODO is this necessary?

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
