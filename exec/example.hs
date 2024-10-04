module Main where

import Data.List
import Data.Maybe (fromJust)
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

  putStrLn "\nLowest M+ rule without interpolant:"
  let mstart = fromJust $ lowestMplusWithoutIP ti
  ppTab mstart

  -- T^J
  putStrLn "\nT^J (Def 27):"
  let tj = tjOf $ head $ childrenOf mstart
  ppTab tj

  putStrLn "\nCompute T(Y) for all right components Y:"
  putStrLn "List of all nodes:"
  mapM_ (\pth -> do
            putStr $ show pth ++ "\t\t"
            putStrLn $ ppWFormsTyp Nothing (wfsOf (tj `at` pth)) []
            )  $ allPathsIn tj
  putStrLn "◁' relation (Def 15):"
  mapM_ (\pth -> do
            putStr $ pad 16 $ show pth
            print $ filter (trianglePrime tj pth) (allPathsIn tj)
            )  $ allPathsIn tj
  putStrLn "T(Y) sets (Def 29):"
  putStrLn "Y \t\tT(Y) \t\tT(Y)^ε \t\tT(Y)^I \t\tT(Y)^◁"
  let rightComponents = nub $ map (\pth -> rightsOf (wfsOf (tj `at` pth)) ) (allPathsIn tj)
  mapM_ (\y -> do
            putStr $ pad 16 $ toStrings y
            putStr $ pad 16 $ show (tOf tj y)
            putStr $ pad 16 $ show (tOfEpsilon tj y)
            putStr $ pad 16 $ show (tOfI tj y)
            print (tOfTriangle tj y)
           ) rightComponents

  -- T^K
  putStrLn "\nT^K (Def 31):"
  let tk = tkOf tj
  ppTab tk

  -- interpolant
  putStrLn "\nInterpolant for the root of T^K:"
  print $ ipFor tj tk []
  putStrLn "Simplified:"
  print $ simplify $ ipFor tj tk []
