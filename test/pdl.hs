module Main where

import Data.Containers.ListUtils (nubOrd)
import Data.List
import Data.Maybe
import Data.String (fromString)
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Logic.Internal
import Logic.PDL
import Logic.PDL.Consistent
import Logic.PDL.Examples
import Logic.PDL.Interpolation
import Logic.PDL.Interpolation.ProofTree
import Logic.PDL.Parse ()
import Logic.PDL.Prove.Tree

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
    prop "simplify gives <= measure [+ distribution]"
      (fTest $ \ f -> withMaxSuccess 50000 $ label ("measure " ++ show (measure f)) $
        measure (simplify f) <= measure f)

  describe "semantics" $ do
    prop "exampleLoop falsifies some formula" $
      expectFailure (fTest $ \ f -> (exampleLoop,1) |= f)
    prop "exampleLoop falsifies some <a> formula" $
      expectFailure (fTest $ \ f -> (exampleLoop,1) |= dia (Ap "a") f)
    prop "formulas get evaluated quickly on random models" $
      \ (SF f) m -> counterexample (toString f ++ "\n" ++ show m) . within timeLimit $
        ((m :: Model Int, 0) |= f) `elem` [True,False]
    prop "a formula false in a model must not be provable" $
      \ (SF f) m -> counterexample (toString f ++ "\n" ++ show m) . within timeLimit $
        not ((m :: Model Int, 0) |= f) ==> not (provable f)
    describe "ring" $ do
      let fs = "<(a;a)*>p49 & ~<(a;a)*>p48" in
        it ("(ring 50, 1) |= " ++ fs) $ (ring 50, 1) |= fromString fs

  describe "tabToMod" $ modifyMaxSuccess (const 1000) $ do
    describe "find counter models for someNonValidities" $
      mapM_ (\f -> it (toString f) $ isJust (tabToMod (prove f))) someNonValidities
    describe "find correct counter models for someNonValidities" $
      mapM_ (\f -> it (toString f) $ fromJust (tabToMod (prove f)) `eval` Neg f) someNonValidities
    describe "do not find counter models to someValidities" $
      mapM_ (\f -> it (toString f) $ isNothing (tabToMod (prove f))) someValidities
    prop "randomized: if consistent, then tabToMod provides a model" $
      fTest (\ f -> consistent [f] ==> isJust (tabToMod (tableauFor [f])))
    prop "randomized: if f is consistent, then tabToMod provides a model of f" $
      fTest (\ f -> consistent [f] ==> fromJust (tabToMod (tableauFor [f])) `eval` f)
    prop "randomized: if f is consistent, then (toIndModel . tabToMod) satisfies f" $
      fTest (\ f -> consistent [f] ==> toIntModel (fromJust (tabToMod (tableauFor [f]))) `eval` f)
    prop "randomized: if inconsistent, then tabToMod provides no model" $
      fTest (\ f -> inconsistent [f] ==> isNothing (tabToMod (tableauFor [f])))
    it "testModelConstruction" $
      ioProperty $ testModelConstruction (fromString "[(a ∪ b) ∪ d*][c*]¬r")

  describe "interpolate" $ modifyMaxDiscardRatio (const 1000) $ do
    describe "someValidImplications" $
      mapM_ (\(Neg (Con f (Neg g))) ->
        it (toString f ++ " -> " ++ toString g) $ testIPgen interpolate (f,g)) someValidImplications
    prop "random implications"
      (fgTest $ \f g -> provable (f `imp` g) ==> testIPgen interpolate (f,g))
    prop "random nice implications"
      (fgTest $ \f g -> isNice (f,g) ==> testIPgen interpolate (f,g))

timeLimit :: Int
timeLimit = 100 * second where
  second = 1000000 -- QuickCheck wants microseconds

fTest :: Testable prop => (Form -> prop) -> (SimplifiedForm -> Property)
fTest testfun (SF f) = counterexample (toString f) . within timeLimit $ testfun f

fgTest :: Testable prop => (Form -> Form -> prop) -> (SimplifiedForm -> SimplifiedForm -> Property)
fgTest testfun (SF f) (SF g) =
  counterexample (toString f ++ " -> " ++ toString g) . within timeLimit $ testfun f g

proveTest :: Form -> SpecWith ()
proveTest f = it (toString f) $ provable f `shouldBe` True

disproveTest :: Form -> SpecWith ()
disproveTest f = it (toString f) $ provable f `shouldBe` False

myExcerpt :: String -> String
myExcerpt l =
  if length l < 60 then l else take 29 l ++ " ... " ++ (reverse . take 29 . reverse) l

testModelConstruction :: Form -> IO Bool
testModelConstruction f = do
  putStrLn $ "Testing counter-model construction for: " ++ toString f
  let t = tableauFor [Neg f]
  -- putStrLn "\n\n M0:\n"
  -- mapM_ print $ m0 t
  putStrLn $ "M0 contains " ++ show (length (m0 t)) ++ " tableaux, of which " ++ show (length (nubOrd (m0 t))) ++ " are unique."
  putStr "The tableaux create this many worlds each: "
  putStrLn $ intercalate "," $ map (show . length . pathSetsOf) (m0 t)
  let Just m = tabToMod t -- unsafe :-/
  {-
  print (tabToMod t)
  putStrLn "\n\n toIntModel:\n"
  print (toIntModel <$> tabToMod t)
  -}
  return $ m |= Neg f
