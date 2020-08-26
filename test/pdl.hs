module Main where

import Logic.PDL
import Logic.PDL.Examples
import Logic.PDL.Lex (alexScanTokens)
import Logic.PDL.Parse (parse)
import Logic.PDL.Prove.Tree
import Logic.PDL.Tools

import Test.Hspec

main :: IO ()
main = hspec $
  describe "Logic.PDL" $ do
    proveTest top
    proveTest (Neg Bot)
    proveTest (Box (Cup a b) p --> Box a p)
    proveTest (dia a p -->  dia (Cup a b) p)
    describe "somValidities" $
      mapM_ proveTest someValidities
    describe "someNonValidities" $
      mapM_ disproveTest someNonValidities
    describe "segeberg" $
      mapM_ proveTest segerberg
    it "parse 'p1'" $
      (parse . alexScanTokens) "p1" `shouldBe` At "p1"
    it "example from file is provable" $
      parseNprove "~(~p0 & [a0*]( <a0>True & ( ~p0 & [a0]p0 | p0 & [a0]~p0) & ~p0))" `shouldBe` True
    it "prove negations of all lines in data/formulae_exp_unsat.txt" $ do
      fs <- exampleData
      let results = map (provable . Neg) fs
      return results `shouldReturn` replicate (length fs) True
    describe "borzechowski" $
      proveTest borzechowski -- FIXME this is currently failing!

proveTest :: Form -> SpecWith ()
proveTest f = it (toString f) $ provable f `shouldBe` True

disproveTest :: Form -> SpecWith ()
disproveTest f = it (toString f) $ provable f `shouldBe` False

exampleData :: IO [Form]
exampleData = do
  fileLines <- lines <$> readFile "data/formulae_exp_unsat.txt"
  return $ map (parse . alexScanTokens) (filter (not . null) fileLines)
