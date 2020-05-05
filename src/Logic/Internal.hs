module Logic.Internal where

import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))

(⊆) :: Eq a => [a] -> [a] -> Bool
(⊆) xs ys = all (`elem` ys) xs

(∩) :: Eq a => [a] -> [a] -> [a]
(∩) xs ys = filter (`elem` ys) xs

implies :: Bool -> Bool -> Bool
implies a b = not a || b

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = concat [ [x:rest, rest] | rest <- powerset xs ]

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x | f x == x  = x
             | otherwise = fixpoint f (f x)

-- | Displayable things, using graphviz.
class DispAble t where
  toGraph :: t -> DotM String ()
  disp :: t -> IO ()
  disp x = runGraphvizCanvas Dot (digraph' $ toGraph x) Xlib
