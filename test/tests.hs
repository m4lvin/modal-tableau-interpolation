module Main where

import Logic.PDL
import Logic.PDL.Prove.Tree

import Logic.PDL.Examples
import Logic.PDL.Lex (alexScanTokens)
import Logic.PDL.Parse (parse)
import Logic.PDL.Tools

import Test.Hspec

main :: IO ()
main = hspec $ do
  it "prove: ([(a ∪ b)](p) → [a](p))" $
    provable (Box (Cup a b) p --> Box a p) `shouldBe` True
  it "prove: (<a>(p) → <(a ∪ b)>(p))" $
    provable (Dia a p -->  Dia (Cup a b) p) `shouldBe` True
  it "prove segeberg" $
    map provable segerberg `shouldNotContain` [False]
  it "parse 'p1'" $
    (parse . alexScanTokens) "p1" `shouldBe` At "p1"
  it "example from file is provable" $
    parseNprove "~(~p0 & [*a0]( <a0>True & ( ~p0 & [a0]p0 | p0 & [a0]~p0) & ~p0))" `shouldBe` True
  it "prove everything in data/formulae_exp_unsat.txt" $ do
    fs <- exampleData
    let results = map (provable . Neg) fs
    return results `shouldReturn` replicate (length fs) True

exampleData :: IO [Form]
exampleData = do
  fileLines <- lines <$> readFile "data/formulae_exp_unsat.txt"
  return $ map (parse . alexScanTokens) (filter (not . null) fileLines)
