{-# LANGUAGE FlexibleInstances #-}

module Logic.Internal where

import qualified Data.ByteString as SB
import Data.Containers.ListUtils (nubOrd)
import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))
import Data.List (intercalate, sort)
import GHC.IO.Handle
import System.IO
import System.IO.Temp
import System.IO.Unsafe

(⊆) :: Eq a => [a] -> [a] -> Bool
(⊆) xs ys = all (`elem` ys) xs

(∩) :: Eq a => [a] -> [a] -> [a]
(∩) xs ys = filter (`elem` ys) xs

implies :: Bool -> Bool -> Bool
implies a b = not a || b

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = concat [ [x:rest, rest] | rest <- powerset xs ]

seteq :: Ord a => [a] -> [a] -> Bool
seteq xs ys = sort (nubOrd xs) == sort (nubOrd ys)

subseteq :: Eq a => [a] -> [a] -> Bool
subseteq xs ys = all (`elem` ys) xs

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x | f x == x  = x
             | otherwise = fixpoint f (f x)

-- | Pretty-printable things.
class Stringable a where
  toString :: a -> String
  toStrings :: [a] -> String
  toStrings xs = intercalate ", " $ map toString xs
  pp :: a -> IO ()
  pp = putStrLn . toString

instance (Stringable a, Stringable b) => Stringable (a, Maybe b) where
  toString (x, Just  y) = toString x ++ " ^ " ++ toString y
  toString (x, Nothing) = toString x

-- | Displayable things, using graphviz.
class DispAble t where
  toGraph :: t -> DotM String ()
  disp :: t -> IO ()
  disp x = runGraphvizCanvas Dot (digraph' $ toGraph x) Xlib
  dot :: t -> IO ()
  dot x = graphvizWithHandle Dot (digraph' $ toGraph x) Canon $ \h -> do
    hSetEncoding h utf8
    SB.hGetContents h >>= SB.putStr
  svg :: t -> String
  svg x = unsafePerformIO $ withSystemTempDirectory "tapdleau" $ \tmpdir -> do
    _ <- runGraphvizCommand Dot (digraph' $ toGraph x) Svg (tmpdir ++ "/temp.svg")
    readFile (tmpdir ++ "/temp.svg")

-- | Pick one element of each list to form new lists.
-- Example: pickOneOfEach [[1,2],[3,4,5]] == [[1,3],[1,4],[1,5],[2,3],[2,4],[2,5]]
pickOneOfEach :: [[a]] -> [[a]]
pickOneOfEach [] = [[]]
pickOneOfEach (l:ls) = [ x:xs | x <- l, xs <- pickOneOfEach ls ]

-- | If any element has this property, only return that one,
-- If there are none, keep the whole list.
filterOneIfAny :: (a -> Bool) -> [a] -> [a]
filterOneIfAny p ts = if any p ts then take 1 (filter p ts) else ts

-- | Add spaces to `str` to make if of length n.
pad :: Int -> String -> String
pad n str = str ++ replicate (n - length str) ' '
