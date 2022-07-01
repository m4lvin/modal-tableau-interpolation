module Main where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Logic.Internal
import Logic.PDL
import Logic.PDL.Examples
import Logic.PDL.Parse
import Logic.PDL.Prove.Tree

import Logic.PDL.Interpolation
import Logic.PDL.Interpolation.ProofTree

main :: IO ()
main = hspec $ do
  describe "somValidities" $
    mapM_ proveTest someValidities
  describe "someNonValidities" $
    mapM_ disproveTest someNonValidities
  describe "segerbergFor p q a b" $
    mapM_ proveTest $ segerbergFor p q a b
  describe "parsing" $
    it "parse 'p1'" $
      fromString "p1" `shouldBe` At "p1"
  describe "prove negation of each line of data/formulae_exp_unsat.txt" $ do
    fileLines <- runIO $ readFile "data/formulae_exp_unsat.txt"
    mapM_
      (\l -> it (myExcerpt l) $ (provable . Neg) (fromString l))
      (filter (not . null) (lines fileLines))
  let str = "~p & [a*](<a>True & ((~p & [a]p) | (p & [a]~p)))"
   in it ("negation of " ++ str ++ " from sat file is not provable") $ -- failing, due to unsound condition 6 maybe?
        not. provable . Neg $ fromString str
  -- describe "do not prove negation of each line of data/formulae_exp_sat.txt" $ do
  --   fileLines <- runIO $ readFile "data/formulae_exp_sat.txt"
  --   mapM_
  --     (\l -> it (myExcerpt l) $ (not . provable . Neg) (fromString l))
  --     (filter (not . null) (lines fileLines))
  describe "inconsistent" $ do
    it "{ [a]p, ¬[a](p ∨ r), ¬[a](q ∨ r) }" $
      inconsistent [ Box a p, Neg (Box a (p `dis` r)), Neg (Box a (q `dis` r)) ]
    it "{ [a]p, ¬[a](q ∨ r), ¬[a](p ∨ r) }" $
      inconsistent [ Box a p, Neg (Box a (q `dis` r)), Neg (Box a (p `dis` r)) ]
    it "Borzechowski Example 2:  { r ∧ ~□p, r --> □(p ∧ q) }" $
      inconsistent [ r `Con` Neg (Box a p), r --> Box a (p `Con` q) ]
  describe "borzechowski" $
    proveTest borzechowski -- FIXME this is currently failing!
  describe "random formulas" $ do
    prop "provable f `elem` [True,False] -- but no error"
      (\f -> provable f `elem` [True,False])
    -- describe "segerbergFor" $
    --   mapM_ (\ k -> do
    --            prop (show k)
    --              (\ f1 f2 p1 p2 -> provable (segerbergFor f1 f2 p1 p2 !! k) )
    --         ) [0..(length (segerbergFor p q a b) - 1)]
  describe "interpolate" $ do
    prop "interpolate randomly generated examples"
      (\(f,g) -> provable (f `imp` g) ==> testIPgen interpolate (f,g))
    -- modifyMaxDiscardRatio (const 1000) $
    --   prop "interpolate randomly generated nice examples"
    --     (\(f,g) -> isNice (f,g) ==> testIPgen interpolate (f,g))


proveTest :: Form -> SpecWith ()
proveTest f = it (toString f) $ provable f `shouldBe` True

disproveTest :: Form -> SpecWith ()
disproveTest f = it (toString f) $ provable f `shouldBe` False

myExcerpt :: String -> String
myExcerpt l =
  if length l < 60 then l else take 29 l ++ " ... " ++ (reverse . take 29 . reverse) l
