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
  describe "provable" $ do
    it "Top" $
      provable top
    it "Neg Bot" $
      provable (Neg Bot)
    it "p --> p"  $
      provable $ p --> p
    it "Box (Con p q) --> Box p"  $
      provable $ Box (Con p q) --> Box p
    it "Box (p --> q) --> (Box p --> Box q)"  $
      provable $ Box (p --> q) --> (Box p --> Box q)
    it "dia (Con p q) --> dia p"  $
      provable $ dia (Con p q) --> dia p
    it "Con (Box (p --> q)) (dia p) --> dia q"  $
      provable $ Con (Box (p --> q)) (dia p) --> dia q
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
  describe "inconsistent" $ do
    it "{ □p, ¬□(p ∨ r), ¬□(q ∨ r) }" $
      inconsistent [ Box p, Neg (Box (p `dis` r)), Neg (Box (q `dis` r)) ]
    it "{ □p, ¬□(q ∨ r), ¬□(p ∨ r) }" $
      inconsistent [ Box p, Neg (Box (q `dis` r)), Neg (Box (p `dis` r)) ]
    it "Borzechowski Example 2:  { r ⋀ ~□p, r ↣ □(p ⋀ q) }" $
      inconsistent [ r `Con` Neg (Box p), r --> Box (p `Con` q) ]
  describe "interpolate" $ do
    it "(Box (At 'r'),Box (imp (At 's') (At 'r')))" $
      testIPgen interpolate (Box (At 'r'),Box (imp (At 's') (At 'r')))
    it "(Box (Neg (Box (Neg (Box (At 's'))))),Box (imp (imp (Neg (At 'q')) (Box (At 'r'))) (Neg (Box Bot))))" $
        testIPgen interpolate (Box (Neg (Box (Neg (Box (At 's'))))),Box (imp (imp (Neg (At 'q')) (Box (At 'r'))) (Neg (Box Bot))))
    it "(Neg (imp (Neg (Box (imp (At 's') (At 'q')))) (Neg (Box (At 'p')))),Neg (Box (imp (At 'p') (At 'q'))))" $
      testIPgen interpolate (Neg (imp (Neg (Box (imp (At 's') (At 'q')))) (Neg (Box (At 'p')))),Neg (Box (imp (At 'p') (At 'q'))))

    prop "interpolate randomly generated examples"
      (\(f,g) -> provable (f `imp` g) ==> testIPgen interpolate (f,g))
    modifyMaxDiscardRatio (const 1000) $
      prop "interpolate randomly generated nice examples" $
        (\(f,g) -> isNice (f,g) ==> testIPgen interpolate (f,g))
