{-# LANGUAGE FlexibleInstances #-}

module Logic.BasicModal.Interpolation.ProofTree where

import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))

import Logic.BasicModal
import Logic.BasicModal.Prove.Tree hiding (Node,End)
import qualified Logic.BasicModal.Prove.Tree as T (Tableaux(Node,End))
import Logic.Internal

type Interpolant = Maybe Form

data TableauxIP = Node ([WForm],Interpolant) RuleName [WForm] [TableauxIP] | End
  deriving (Eq,Ord,Show)

ppIP :: Interpolant -> String
ppIP (Just f) = toString f
ppIP Nothing  = "∅"

instance DispAble TableauxIP where
  toGraph = toGraph' "" where
    toGraph' pref End =
      node pref [shape PlainText, toLabel "✘"]
    toGraph' pref (Node (wfs,ip) rule actives ts) = do
      node pref [shape PlainText, toLabel $ ppWForms wfs actives ++ "  ::  " ++ ppIP ip]
      mapM_ (\(t,y') -> do
        toGraph' (pref ++ show y' ++ ":") t
        edge pref (pref ++ show y' ++ ":") [toLabel rule]
        ) (zip ts [(0::Integer)..])

toEmptyTabIP :: Tableaux -> TableauxIP
toEmptyTabIP T.End = End
toEmptyTabIP (T.Node wfs rule actives ts) =
  Node (wfs,Nothing) rule actives (map toEmptyTabIP ts)

hasIP :: TableauxIP -> Bool
hasIP End = False
hasIP (Node (_,Just _ ) _ _ _) = True
hasIP (Node (_,Nothing) _ _ _) = False

ipOf :: TableauxIP -> Form
ipOf End = error "End nodes do not have interpolants."
ipOf (Node (_,Just f ) _ _ _) = f
ipOf (Node (_,Nothing) _ _ _) = error "No interpolant here."

interpolateNode :: [WForm] -> [Form]
interpolateNode wfs = filter evil (leftsOf wfs) where
  evil (Neg f) = f `elem` rightsOf wfs || Neg (Neg f) `elem` rightsOf wfs
  evil f       = Neg f `elem` rightsOf wfs

fillIPs :: TableauxIP -> TableauxIP
-- Ends and already interpolated nodes: nothing to do:
fillIPs End = End
fillIPs t@(Node (_, Just _) _ _ _) = t
-- Closed end nodes: use the active formulas or a constant as interpolant:
fillIPs (Node (wfs, Nothing) "✘" actives [End]) = Node (wfs, Just ip) "✘" actives [End] where
  ip = case actives of
    [Left  Bot]        -> Bot
    [Right Bot]        -> top
    [Left  f, Right _] -> f
    [Right _, Left  f] -> f
    [Left  _, Left  _] -> Bot -- inconsistency implies bot
    [Right _, Right _] -> top -- top implies Neg inconsistency
    _                  -> error $ "End node, but wrong actives: " ++ show actives
fillIPs n@(Node (wfs,Nothing) rule actives ts)
-- Non-end nodes where children are missing IPs: recurse
  | not (all hasIP ts) = fillIPs $ Node (wfs, Nothing) rule actives (map fillIPs ts)
-- Non-end nodes where children already have IPs: distinguish rules
  | otherwise = Node (wfs, Just newIP) rule actives ts where
      newIP = case (rule,actives) of
        -- single-child rules are easy, the interpolant stays the same:
        ("¬",_) -> ipOf t where [t] = ts
        ("∧",_) -> ipOf t where [t] = ts
        -- for the branching rule we combine the two previous interpolants
        -- with a connective depending on the side of the active formula:
        ("¬∧",_) -> connective (ipOf t1) (ipOf t2) where
          [t1,t2] = ts
          connective = case actives of
            [Left  _] -> dis -- left side is active
            [Right _] -> Con -- right side is active
            _         -> error "Could not find the active side."
        -- for the critical rule, we prefix the previous interpolant with diamond or Box, depending on the active side
        -- moroever, if one of the sides is empty we should use Bot or Top as interpolants, but for basic modal logic we do not need that
        -- (it will matter for PDL, because <a>T and T have different vocabulary!)
        -- (see Borzechowski page 44)
        ("¬☐",[Left  _]) -> let [t] = ts in dia (ipOf t)
        ("¬☐",[Right _]) -> let [t] = ts in Box (ipOf t)
        (rl,_) -> error $ "Rule " ++ rl ++ " applied to " ++ ppWForms wfs actives ++ " Unable to interpolate!:\n" ++ show n

fillAllIPs :: TableauxIP -> TableauxIP
fillAllIPs = fixpoint fillIPs -- TODO is this necessary?

proveAndInterpolate :: (Form,Form) -> (TableauxIP,Form)
proveAndInterpolate (ante,cons)
  | not $ provable (ante --> cons) = error $ "This implication is not valid " ++ toString (ante --> cons)
  | otherwise = (ipt1,ip) where
      t1 = prove (ante --> cons)
      ipt0 = toEmptyTabIP t1 :: TableauxIP
      ipt1 = fillAllIPs ipt0
      ip = ipOf ipt1

interpolate :: (Form,Form) -> Form
interpolate = snd . proveAndInterpolate

interpolateShow :: (Form,Form) -> IO ()
interpolateShow pair = do
  let (t,ip) = proveAndInterpolate pair
  putStrLn "Showing tableau with GraphViz ..."
  disp t
  -- dot t
  putStrLn $ "Interpolant: " ++ toString ip
  putStrLn $ "Simplified interpolant: " ++ toString (simplify ip)

isNice :: (Form,Form) -> Bool
isNice (f,g) = provable (f `imp` g)
            && atomsIn f /= [] && atomsIn g /= []
            && atomsIn f /= atomsIn g
            && (not . provable . Neg $ f)
            && (not . provable $ g)
