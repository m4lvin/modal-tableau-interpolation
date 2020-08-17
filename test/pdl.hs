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
    it "prove: top" $
      provable top `shouldBe` True
    it "prove: Neg Bot" $
      provable (Neg Bot) `shouldBe` True
    it "prove: ([(a ∪ b)](p) → [a](p))" $
      provable (Box (Cup a b) p --> Box a p) `shouldBe` True
    it "prove: (<a>(p) → <(a ∪ b)>(p))" $
      provable (dia a p -->  dia (Cup a b) p) `shouldBe` True
    it "prove somValidities" $
      map provable someValidities `shouldSatisfy` and
    it "prove segeberg" $
      map provable segerberg `shouldNotContain` [False]
    it "parse 'p1'" $
      (parse . alexScanTokens) "p1" `shouldBe` At "p1"
    it "example from file is provable" $
      parseNprove "~(~p0 & [a0*]( <a0>True & ( ~p0 & [a0]p0 | p0 & [a0]~p0) & ~p0))" `shouldBe` True
    it "prove negations of all lines in data/formulae_exp_unsat.txt" $ do
      fs <- exampleData
      let results = map (provable . Neg) fs
      return results `shouldReturn` replicate (length fs) True
    it "prove borzechowski" $
      provable borzechowski -- FIXME this is currently failing!

exampleData :: IO [Form]
exampleData = do
  fileLines <- lines <$> readFile "data/formulae_exp_unsat.txt"
  return $ map (parse . alexScanTokens) (filter (not . null) fileLines)
