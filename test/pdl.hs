module Main where

import Data.String(fromString)
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Logic.Internal
import Logic.PDL
import Logic.PDL.Examples
import Logic.PDL.Parse()
import Logic.PDL.Prove.Tree

import Logic.PDL.Interpolation
import Logic.PDL.Interpolation.ProofTree

main :: IO ()
main = hspec $ do
  describe "someValidities" $
    mapM_ proveTest someValidities
  describe "someValidImplications" $
    mapM_ proveTest someValidImplications
  describe "do not prove negations of someValidities" $
    mapM_ (disproveTest . Neg) someValidities
  describe "do not prove negations of someValidImplications" $
    mapM_ (disproveTest . Neg) someValidImplications
  describe "someNonValidities" $
    mapM_ disproveTest someNonValidities
  describe "segerbergFor p q a b" $
    mapM_ proveTest $ segerbergFor p q a b
  describe "parsing" $ do
    it "parse 'p1'" $
      fromString "p1" `shouldBe` At "p1"
    it "parse '[a]p <-> [b]q'" $
      fromString "[a]p <-> [b]q" `shouldBe` ( Box (Ap "a") (At "p") <--> Box (Ap "b") (At "q") )
  describe "prove negation of the first two formulas in data/formulae_exp_unsat.txt" $ do
    fileLines <- runIO $ readFile "data/formulae_exp_unsat.txt"
    mapM_
      (\l -> it (myExcerpt l) $ (provable . Neg) (fromString l))
      (take 2 $ filter (not . null) (lines fileLines))
  describe "do NOT prove negation of first two formulas in data/formulae_exp_sat.txt" $ do
    fileLines <- runIO $ readFile "data/formulae_exp_sat.txt"
    mapM_
      (\l -> it (myExcerpt l) $ (not . provable . Neg) (fromString l))
      (take 2 $ filter (not . null) (lines fileLines))
  describe "inconsistent" $ do
    it "{ [a]p, ¬[a](p ∨ r), ¬[a](q ∨ r) }" $
      inconsistent [ Box a p, Neg (Box a (p `dis` r)), Neg (Box a (q `dis` r)) ]
    it "{ [a]p, ¬[a](q ∨ r), ¬[a](p ∨ r) }" $
      inconsistent [ Box a p, Neg (Box a (q `dis` r)), Neg (Box a (p `dis` r)) ]
    it "Borzechowski Example 2:  { r ∧ ~□p, r --> □(p ∧ q) }" $
      inconsistent [ r `Con` Neg (Box a p), r --> Box a (p `Con` q) ]
  describe "borzechowski" $
    proveTest borzechowski
  describe "random examples" $ modifyMaxDiscardRatio (const 1000) $ do
    prop "provable f `elem` [True,False] -- but no error"
      (fTest $ \f -> provable f `elem` [True,False])
    prop "provable f iff provable ~~f"
      (fTest $ \f -> provable f === provable (Neg (Neg f)))
    prop "if (provable f or provable g) then provable (f v g)"
      (fgTest $ \f g -> (provable f || provable g) ==> provable (dis f g))
    prop "if (provable f and provable g) then provable (f ∧ g)"
      (fgTest $ \f g -> (provable f && provable g) ==> provable (Con f g))
    prop "provable (f -> g) iff provable (¬g -> ¬f)"
      (fgTest $ \f g -> provable (f --> g) === provable (Neg g --> Neg f))
    prop "simplify preserves provability"
      (fTest $ \ f -> provable f === provable (simplify f))

  describe "semantics" $ do
    prop "exampleLoop falsifies some formula" $
      expectFailure (fTest $ \ f -> (exampleLoop,1) |= f)
    prop "exampleLoop falsifies some <a> formula" $
      expectFailure (fTest $ \ f -> (exampleLoop,1) |= dia (Ap "a") f)
    prop "formulas get evaluated quickly on random models" $
      \ (SF f) m -> counterexample (toString f ++ "\n" ++ show m) . within 10000000 $
        ((m :: Model Int, 0) |= f) `elem` [True,False]
    prop "a formula false in a model must not be provable" $
      \ (SF f) m -> counterexample (toString f ++ "\n" ++ show m) . within 10000000 $
        not ((m :: Model Int, 0) |= f) ==> not (provable f)

  describe "interpolate" $ modifyMaxDiscardRatio (const 1000) $ do
    describe "someValidImplications" $
      mapM_ (\(Neg (Con f (Neg g))) ->
        it (toString f ++ " -> " ++ toString g) $ testIPgen interpolate (f,g)) someValidImplications
    prop "random implications"
      (fgTest $ \f g -> provable (f `imp` g) ==> testIPgen interpolate (f,g))
    prop "random nice implications"
      (fgTest $ \f g -> isNice (f,g) ==> testIPgen interpolate (f,g))

fTest :: Testable prop => (Form -> prop) -> (SimpleForm -> Property)
fTest testfun (SF f) = counterexample (toString f) . within 10000000 $ testfun f -- ten seconds

fgTest :: Testable prop => (Form -> Form -> prop) -> (SimpleForm -> SimpleForm -> Property)
fgTest testfun (SF f) (SF g) = counterexample (toString f ++ " -> " ++ toString g) . within 10000000 $ testfun f g -- ten seconds

proveTest :: Form -> SpecWith ()
proveTest f = it (toString f) $ provable f `shouldBe` True

disproveTest :: Form -> SpecWith ()
disproveTest f = it (toString f) $ provable f `shouldBe` False

myExcerpt :: String -> String
myExcerpt l =
  if length l < 60 then l else take 29 l ++ " ... " ++ (reverse . take 29 . reverse) l
