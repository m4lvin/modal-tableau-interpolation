module Main where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Logic.Propositional
import Logic.Propositional.Examples
import qualified Logic.Propositional.Prove.List as List
import qualified Logic.Propositional.Prove.Tree as Tree
import Logic.Propositional.Interpolation
import qualified Logic.Propositional.Interpolation.Naive as Naive
import qualified Logic.Propositional.Interpolation.ProofTree as ProofTree

main :: IO ()
main = hspec $ do
  describe "Prove.List.isProvable" $ do
    it "Top" $ List.isProvable $ Top
    it "dis p (Neg p)" $ List.isProvable $ dis p (Neg p)
    it "Neg $ Con p (Neg p)" $ List.isProvable $ Neg $ Con p (Neg p)
    it "Neg (Imp p q) --> Con p (Neg q)" $ List.isProvable $ Neg (Imp p q) --> Con p (Neg q)
  describe "not . Prove.List.isProvable" $ do
    it "Bot" $ not . List.isProvable $ bot
    it "Con p (Neg p)" $ not . List.isProvable $ Con p (Neg p)
    it "Con r (dis p (Neg p))" $ not . List.isProvable $ Con r (dis p (Neg p))
  describe "Prove.Tree.isProvable" $ do
    it "dis p (Neg p)" $ Tree.provable $ dis p (Neg p)
    it "Neg $ Con p (Neg p)" $ Tree.provable $ Neg $ Con p (Neg p)
    it "weirdform" $ Tree.provable weirdform
  describe "not . Prove.Tree.isProvable" $ do
    it "Bot" $ not . Tree.provable $ bot
    it "Con p (Neg p)" $ not . Tree.provable $ Con p (Neg p)
    it "Con r (dis p (Neg p))" $ not . Tree.provable $ Con r (dis p (Neg p))
  describe "Interpolation.Naive" $ do
    it "(Con p q, dis q r)" $
      testIPgen Naive.interpolate (Con p q, dis q r)
  describe "Interpolation.ProofTree" $ do
    it "(Con p q, dis q r)" $
      testIPgen Naive.interpolate (Con p q, dis q r)
  modifyMaxDiscardRatio (const 100) $ do
    describe "check nice examples with Naive" $ do
      prop "" $ (\(f,g) -> ProofTree.isNice (f,g) ==> testIPgen Naive.interpolate (f,g))
    describe "check nice examples with ProofTree" $ do
      prop "" $ (\(f,g) -> ProofTree.isNice (f,g) ==> testIPgen ProofTree.interpolate (f,g))
