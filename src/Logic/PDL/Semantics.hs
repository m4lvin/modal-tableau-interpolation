module Logic.PDL.Semantics where

import Data.List
import Data.GraphViz hiding (Star)
import Data.GraphViz.Types.Monadic hiding ((-->))

import Logic.PDL
import Logic.Internal

type Valuation a = a -> [Atom]

type Relations a = Atom -> a -> [a]

data Model a = KrM { worlds :: [a]
                   , val :: Valuation a
                   , progs :: [Atom]
                   , rel :: Relations a
                   }

instance Show a => Show (Model a) where
  show m = "KrM " ++ show (worlds m) ++ " undefined " ++ show (progs m) ++ " undefined "  -- TODO

instance Show a => DispAble (Model a) where
  toGraph m = mapM_ (\w -> do
                        node (show w) [shape Circle, toLabel $ show w ++ ":" ++ ppAts (val m w)]
                        mapM_(\ap -> mapM_ (\w' -> edge (show w) (show w') [ toLabel ap ]) (rel m ap w)) (progs m)
                    ) (worlds m)

-- | Evaluate formula on a pointed model
eval :: Eq a => (Model a, a) -> Form -> Bool
eval (_,_) Bot       = False
eval (m,w) (At at)   = at `elem` val m w
eval (m,w) (Neg f)   = not $ eval (m,w) f
eval (m,w) (Con f g) = eval (m,w) f && eval (m,w) g
eval (m,w) (Box pr f) = all (\w' -> eval (m,w') f) (relval m pr w)

-- | Evaluate a program on a model
relval :: Eq a => Model a -> Prog -> a -> [a]
relval m (Ap ap)     = rel m ap
relval m (Cup p1 p2) = \w -> nub (relval m p1 w ++ relval m p2 w)
relval m (p1 :- p2)  = concatMap (relval m p2) . relval m p1
relval m (Test f)    = \w -> [ w | eval (m,w) f ]
relval m (Star pr)   = \w -> lfp (concatMap (relval m pr)) [w]
relval m (NStar pr)  = relval m (Star pr)

-- | Least fixpoint.
lfp :: Eq a => (a -> a) -> a -> a
lfp f x = if f x == x then x else lfp f (f x)

globeval :: Eq a => Model a -> Form -> Bool
globeval m f = all (\w -> eval (m,w) f) (worlds m)
