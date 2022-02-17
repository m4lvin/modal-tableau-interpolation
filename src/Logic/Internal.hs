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

-- | Pick one element of each list to form new lists.
-- Example: pickOneOfEach [[1,2],[3,4,5]] == [[1,3],[1,4],[1,5],[2,3],[2,4],[2,5]]
pickOneOfEach :: [[a]] -> [[a]]
pickOneOfEach [] = [[]]
pickOneOfEach (l:ls) = [ x:xs | x <- l, xs <- pickOneOfEach ls ]

-- | If any element has this property, only return that one,
-- If there are none, keep the whole list.
filterOneIfAny :: (a -> Bool) -> [a] -> [a]
filterOneIfAny p ts = if any p ts then take 1 (filter p ts) else ts
