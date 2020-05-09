{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Logic.BasicModal.Interpolation.ProofTree where

import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))
import Test.QuickCheck

import Logic.BasicModal
import Logic.BasicModal.Prove.Tree hiding (Node,End)
import qualified Logic.BasicModal.Prove.Tree as T (Tableaux(Node,End))
import Logic.Internal

type Interpolant = Maybe Form

data TableauxIP = Node ([WForm],Interpolant) RuleName [TableauxIP] | End
  deriving (Eq,Ord,Show)

ppIP :: Interpolant -> String
ppIP (Just f) = ppForm f
ppIP Nothing  = "∅"

instance DispAble TableauxIP where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "✘"]
    toGraph' pref (Node (wfs,ip) rule ts) = do
      node pref [shape PlainText, toLabel $ ppWForms wfs ++ "  ::  " ++ ppIP ip]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

toEmptyTabIP :: Tableaux -> TableauxIP
toEmptyTabIP T.End = End
toEmptyTabIP (T.Node wfs rule ts) =
  Node (wfs,Nothing) rule (map toEmptyTabIP ts)

hasIP :: TableauxIP -> Bool
hasIP End = False
hasIP (Node (_,Just _ ) _ _) = True
hasIP (Node (_,Nothing) _ _) = False

ipOf :: TableauxIP -> Form
ipOf End = error "End nodes do not have interpolants."
ipOf (Node (_,Just f ) _ _) = f
ipOf (Node (_,Nothing) _ _) = error "No interpolant here."

interpolateNode :: [WForm] -> [Form]
interpolateNode wfs = filter evil (leftsOf wfs) where
  evil (Neg f) = f `elem` rightsOf wfs || Neg (Neg f) `elem` rightsOf wfs
  evil f       = Neg f `elem` rightsOf wfs

fillIPs :: TableauxIP -> TableauxIP
-- Ends and already interpolated nodes: nothing to do
fillIPs End = End
fillIPs t@(Node (_, Just _) _ _) = t
-- Closed end nodes: use
fillIPs (Node (wfs, Nothing) "✘" [End]) = Node (wfs, Just ip) "✘" [End] where
  ip
    | isClosedNode (leftsOf wfs)  = Bot -- inconsistency implies bot
    | isClosedNode (rightsOf wfs) = Top -- Top implies Neg inconsistency
    | isClosedNode (collapseList wfs) = case filter (`elem` leftsOf wfs) (interpolateNode wfs) of
        []    -> error $ "fillIPs failed, no interpolate found in " ++ ppWForms wfs
        (x:_) -> x
    | otherwise = error $ "This should not be a closed end: " ++ ppWForms wfs
fillIPs n@(Node (wfs,Nothing) rule ts)
-- Non-end nodes where childs are missing IPs: recurse
  | any (not . hasIP) ts = fillIPs $ Node (wfs, Nothing) rule (map fillIPs ts)
-- Non-end nodes where childs already have IPs: distinguish rules
  | otherwise = Node (wfs, Just $ simplify newIP) rule ts where
      newIP = case rule of
        -- single-child rules are easy, the interpolant stays the same:
        "¬¬" -> ipOf t where [t] = ts
        "¬→" -> ipOf t where [t] = ts
        -- for the branching rule we combine two previous interpolants with
        -- a connective depending on the active side / weightOf the active formula:
        "→" -> connective (ipOf t1) (ipOf t2) where
          [t1@(Node (newwfs,_) _ _),t2] = ts
          connective
            | leftsOf  wfs /= leftsOf  newwfs = dis -- left side is active
            | rightsOf wfs /= rightsOf newwfs = con -- right side is active
            | otherwise = error "Could not find the active side."
        -- the critical rule, we diamond or Box the interpolant, depending on the active side
        -- (see Borzechowski page 44)
        "¬☐" -> connective (ipOf t) where
          [t@(Node (newwfs,_) _ _)] = ts
          connective
            | project (leftsOf  wfs) /= leftsOf  newwfs = dia -- left side is active  -- FIXME might need Bot as newIp
            | project (rightsOf wfs) /= rightsOf newwfs = Box -- right side is active -- FIXME might need Top as newIp
            | otherwise = error "Could not find the active side."
        rl -> error $ "Unknown rule " ++ rl ++ " applied. Can not interpolate!:\n" ++ show n

fillAllIPs :: TableauxIP -> TableauxIP
fillAllIPs = fixpoint fillIPs -- TODO is this necessary?

proveAndInterpolate :: (Form,Form) -> (TableauxIP,Form)
proveAndInterpolate (ante,cons)
  | not $ provable (ante --> cons) = error $ "This implication is not valid " ++ ppForm (ante --> cons)
  | otherwise = (ipt1,ip) where
      t1 = prove (ante --> cons)
      ipt0 = toEmptyTabIP t1 :: TableauxIP
      ipt1 = fillAllIPs ipt0
      ip = ipOf ipt1

interpolate :: (Form,Form) -> Form
interpolate = snd . proveAndInterpolate

interpolateShow :: (Form,Form) -> IO Form
interpolateShow pair = do
  let (t,ip) = proveAndInterpolate pair
  disp t
  print $ simplify ip
  return ip

isNice :: (Form,Form) -> Bool
isNice (f,g) = provable (f `Imp` g)
            && atomsIn f /= [] && atomsIn g /= []
            && atomsIn f /= atomsIn g
            && (not . provable . Neg $ f)
            && (not . provable $ g)

makeNiceExample :: IO (Form,Form)
makeNiceExample = do
  f <- generate arbitrary
  g <- generate arbitrary
  if isNice (f,g)
    then return (f,g)
    else makeNiceExample
