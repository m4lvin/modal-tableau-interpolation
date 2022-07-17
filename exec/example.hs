module Main where

import Data.String( IsString(..) )

import Logic.PDL
import Logic.Internal
import Logic.PDL.Parse ()
import Logic.PDL.Prove.Tree
import Logic.PDL.Interpolation.ProofTree

main :: IO ()
main = do
  let
    pdlF = fromString "[(a u b)*](p ^ q) -> [b*]q" :: Logic.PDL.Form
    -- pdlF = fromString "[a*]p -> [a**]p" :: Logic.PDL.Form
    t = prove pdlF
    closed = isClosedTab t
    tWithInt = fillAllIPs $ toEmptyTabIP t

  putStrLn $ "Formula: " ++ toString pdlF
  putStrLn $ if closed then "PROVED." else "NOT proved."

  putStrLn "\nAfter filling in easy interpolants:"
  ppTab tWithInt

  -- T^I
  putStrLn "\nT^I, after removing all n-nodes (Def 26):"
  let ti = tiOf tWithInt
  ppTab ti

  putStrLn "\nLowest M+ rule without interpolant:" -- TODO: actually, get the last/lowest!
  let Just mstart = lowestMplusWithoutIP ti
  ppTab mstart

  -- T^J
  putStrLn "\nT^J (Def 27):"
  let tj = tjOf $ head $ childrenOf mstart
  ppTab tj

  -- T^K
  putStrLn "\nT^K (Def 27):"
  let tk = tkOf $ tj
  ppTab tk

  -- interpolant
  -- TODO putStrLn "\nInterpolant for the root of T^K:"
  -- TODO print $ ipFor tk tk
