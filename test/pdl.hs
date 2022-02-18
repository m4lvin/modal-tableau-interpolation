module Main where

import Logic.PDL
import Logic.PDL.Examples
import Logic.PDL.Lex (alexScanTokens)
import Logic.PDL.Parse (parse)
import Logic.PDL.Prove.Tree

import Test.Hspec
import Test.Hspec.QuickCheck

main :: IO ()
main = hspec $ do
  describe "somValidities" $
    mapM_ proveTest someValidities
  describe "someNonValidities" $
    mapM_ disproveTest someNonValidities
  describe "segeberg" $
    mapM_ proveTest segerberg
  describe "parsing" $
    it "parse 'p1'" $
      (parse . alexScanTokens) "p1" `shouldBe` At "p1"
  describe "parse and prove negation of each line in data/formulae_exp_unsat.txt" $ do
    fileLines <- runIO $ readFile "data/formulae_exp_unsat.txt"
    mapM_
      (\l -> it (myShow l) $ (provable . Neg) ((parse . alexScanTokens) l))
      (filter (not . null) (lines fileLines))
  describe "inconsistent" $ do
    it "{ [a]p, ¬[a](p ∨ r), ¬[a](q ∨ r) }" $
      inconsistent [ Box a p, Neg (Box a (p `dis` r)), Neg (Box a (q `dis` r)) ]
    it "{ [a]p, ¬[a](q ∨ r), ¬[a](p ∨ r) }" $
      inconsistent [ Box a p, Neg (Box a (q `dis` r)), Neg (Box a (p `dis` r)) ]
    it "Borzechowski Example 2:  { r ⋀ ~□p, r ↣ □(p ⋀ q) }" $
      inconsistent [ r `Con` Neg (Box a p), r --> Box a (p `Con` q) ]
  describe "borzechowski" $
    proveTest borzechowski -- FIXME this is currently failing!
  describe "random formulas" $ do
    prop "provable f `elem` [True,False] -- but no error"
      (\f -> provable f `elem` [True,False])

proveTest :: Form -> SpecWith ()
proveTest f = it (toString f) $ provable f `shouldBe` True

disproveTest :: Form -> SpecWith ()
disproveTest f = it (toString f) $ provable f `shouldBe` False

myShow :: String -> String
myShow l =
  if length l < 60 then l else take 29 l ++ " ... " ++ (reverse . take 29 . reverse) l
