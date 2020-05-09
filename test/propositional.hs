module Main where

import Test.Hspec

import Logic.Propositional
import Logic.Propositional.Examples
import qualified Logic.Propositional.Prove.List as List
import qualified Logic.Propositional.Prove.Tree as Tree
import Logic.Propositional.Interpolation
import qualified Logic.Propositional.Interpolation.Naive as Naive
import qualified Logic.Propositional.Interpolation.ProofTree as ProofTree

main :: IO ()
main = hspec $ do
  describe "Logic.Propositional.Prove.List" $ do
    it "isProvable tautology" $ List.isProvable tautology
    it "isProvable" $ List.isProvable tautNegCon
    it "noot (isProvable openNegCon)" $ not (List.isProvable openNegCon)
    it "not (isProvable partOpen)" $ not (List.isProvable partOpen)
  describe "Logic.Propositional.Prove.Tree" $ do
    it "T.isProvable tautology" $ Tree.provable tautology
    it "T.isProvable" $ Tree.provable tautNegCon
    it "not (T.isProvable openNegCon)" $ not (Tree.provable openNegCon)
    it "not (T.isProvable partOpen)" $ not (Tree.provable partOpen)
    it "T.provable weirdform" $ Tree.provable weirdform
  describe "Logic.Propositional.Interpolation.Naive" $ do
    it "interpolate (Con p q, dis q r)" $
      let
        f = Con p q
        g = dis   q r
        i = Naive.interpolate (f,g)
      in i `isInterpolantFor` (f,g)
  describe "Logic.Propositional.Interpolation.ProofTree" $ do
    it "interpolate (Con p q, dis q r)" $
      let
        f = Con p q
        g = dis   q r
        i = ProofTree.interpolate (f,g)
      in i `isInterpolantFor` (f,g)
