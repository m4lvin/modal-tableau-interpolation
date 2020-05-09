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
      provable top
    it "Neg Bot" $
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
    it "Bot" $
      not. provable $ Bot
    it "Neg Top" $
      not . provable $ Neg top
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
  describe "interpolate" $ do
    it "(Box (At 'r'),Box (Imp (At 's') (At 'r')))" $
      testIPgen interpolate $ (Box (At 'r'),Box (Imp (At 's') (At 'r')))
    it "(Box (Neg (Box (Neg (Box (At 's'))))),Box (Imp (Imp (Neg (At 'q')) (Box (At 'r'))) (Neg (Box Bot))))" $
        testIPgen interpolate $ (Box (Neg (Box (Neg (Box (At 's'))))),Box (Imp (Imp (Neg (At 'q')) (Box (At 'r'))) (Neg (Box Bot))))
    it "(Neg (Imp (Neg (Box (Imp (At 's') (At 'q')))) (Neg (Box (At 'p')))),Neg (Box (Imp (At 'p') (At 'q'))))" $
      testIPgen interpolate $ (Neg (Imp (Neg (Box (Imp (At 's') (At 'q')))) (Neg (Box (At 'p')))),Neg (Box (Imp (At 'p') (At 'q'))))
  modifyMaxDiscardRatio (const 1000) $ do
    describe "interpolate randomly generated nice examples" $ do
      prop "" $ (\(f,g) -> isNice (f,g) ==> testIPgen interpolate (f,g))
