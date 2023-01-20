module Main where

import Data.String(fromString)
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Logic.Internal
import Logic.PDL
import Logic.PDL.Examples
import Logic.PDL.Parse()
import Logic.PDL.Prove.Tree

import Logic.PDL.Interpolation
import Logic.PDL.Interpolation.ProofTree

main :: IO ()
main = hspec $ do
  describe "simplify" $
    prop "preserves provability"
      (\f -> provable f === provable (simplify f))
  describe "someValidities" $
    mapM_ proveTest someValidities
  describe "someValidImplications" $
    mapM_ proveTest someValidImplications
  describe "someNonValidities" $
    mapM_ disproveTest someNonValidities
  describe "segerbergFor p q a b" $
    mapM_ proveTest $ segerbergFor p q a b
  describe "parsing" $ do
    it "parse 'p1'" $
      fromString "p1" `shouldBe` At "p1"
    it "parse '[a]p <-> [b]q'" $
      fromString "[a]p <-> [b]q" `shouldBe` ( Box (Ap "a") (At "p") <--> Box (Ap "b") (At "q") )
  describe "prove negation of the first three formulas in data/formulae_exp_unsat.txt" $ do
    fileLines <- runIO $ readFile "data/formulae_exp_unsat.txt"
    mapM_
      (\l -> it (myExcerpt l) $ (provable . Neg) (fromString l))
      (take 3 $ filter (not . null) (lines fileLines))
  describe "do NOT prove negation of first three formulas in data/formulae_exp_sat.txt" $ do
    fileLines <- runIO $ readFile "data/formulae_exp_sat.txt"
    mapM_
      (\l -> it (myExcerpt l) $ (not . provable . Neg) (fromString l))
      (take 3 $ filter (not . null) (lines fileLines))
  describe "inconsistent" $ do
    it "{ [a]p, ¬[a](p ∨ r), ¬[a](q ∨ r) }" $
      inconsistent [ Box a p, Neg (Box a (p `dis` r)), Neg (Box a (q `dis` r)) ]
    it "{ [a]p, ¬[a](q ∨ r), ¬[a](p ∨ r) }" $
      inconsistent [ Box a p, Neg (Box a (q `dis` r)), Neg (Box a (p `dis` r)) ]
    it "Borzechowski Example 2:  { r ∧ ~□p, r --> □(p ∧ q) }" $
      inconsistent [ r `Con` Neg (Box a p), r --> Box a (p `Con` q) ]
  describe "borzechowski" $
    proveTest borzechowski
  describe "random formulas" $ do
    prop "provable f `elem` [True,False] -- but no error"
      (\f -> provable f `elem` [True,False])
    -- describe "segerbergFor random formulas" $
    --   mapM_ (\ k -> do
    --            prop (show k)
    --              (\ f1 f2 p1 p2 -> provable (segerbergFor f1 f2 p1 p2 !! k) )
    --         ) [0..(length (segerbergFor p q a b) - 1)]
  describe "interpolate" $ modifyMaxDiscardRatio (const 1000) $ do
    describe "someValidImplications" $
      mapM_ (\(Neg (Con f (Neg g))) ->
        it (toString f ++ " -> " ++ toString g) $ testIPgen interpolate (f,g)) someValidImplications
    prop "random examples"
      (\(f,g) -> provable (f `imp` g) ==> testIPgen interpolate (f,g))
    prop "random nice examples"
      (\(f,g) -> isNice (f,g) ==> testIPgen interpolate (f,g))

proveTest :: Form -> SpecWith ()
proveTest f = it (toString f) $ provable f `shouldBe` True

disproveTest :: Form -> SpecWith ()
disproveTest f = it (toString f) $ provable f `shouldBe` False

myExcerpt :: String -> String
myExcerpt l =
  if length l < 60 then l else take 29 l ++ " ... " ++ (reverse . take 29 . reverse) l
