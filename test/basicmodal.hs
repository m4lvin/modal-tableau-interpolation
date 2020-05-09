module Main where

import Logic.BasicModal
import Logic.BasicModal.Prove.Tree
import Logic.BasicModal.Examples

import Test.Hspec

main :: IO ()
main = hspec $
  describe "Logic.PDL" $ do
    it "prove: Top" $
      provable Top `shouldBe` True
    it "prove: Neg Bot" $
      provable (Neg Bot) `shouldBe` True
    it "prove someValidities" $
      map provable someValidities `shouldSatisfy` and
    it "do not prove someNonValidities" $ do
      map provable someNonValidities `shouldSatisfy` (and . map not)
