module Main where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Logic.BasicModal
import Logic.BasicModal.Prove.Tree
import Logic.BasicModal.Interpolation
import Logic.BasicModal.Interpolation.ProofTree

main :: IO ()
main = hspec $ do
  describe "provable:" $ do
    it "Top" $
      provable Top
    it "prove: Neg Bot" $
      provable (Neg Bot)
    it "p --> p"  $
      provable $ p --> p
    it "Box (con p q) --> Box p"  $
      provable $ Box (con p q) --> Box p
    it "Box (p --> q) --> (Box p --> Box q)"  $
      provable $ Box (p --> q) --> (Box p --> Box q)
    it "dia (con p q) --> dia p"  $
      provable $ dia (con p q) --> dia p
    it "con (Box (p --> q)) (dia p) --> dia q"  $
      provable $ con (Box (p --> q)) (dia p) --> dia q
  describe "not . provable" $ do
    it "p --> q" $
      not . provable $ p --> q
    it "Box p --> p" $
      not . provable $ Box p --> p
    it "dia (dia p) --> dia p" $
      not . provable $ dia (dia p) --> dia p
    it "Box (dis p q) --> Box p" $
      not . provable $ Box (dis p q) --> Box p
    it "(Box p --> Box q) --> Box (p --> q)"  $
      not. provable $ (Box p --> Box q) --> Box (p --> q)

  modifyMaxDiscardRatio (const 100) $ do
    describe "interpolate nice examples" $ do
      prop "" $ (\(f,g) -> isNice (f,g) ==> testIPgen interpolate (f,g))
