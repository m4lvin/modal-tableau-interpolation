{-# LANGUAGE DeriveGeneric, FlexibleInstances #-}

module Logic.BasicModal where

import Control.DeepSeq(NFData)
import Data.List
import Data.Maybe
import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))
import GHC.Generics (Generic)
import Test.QuickCheck

import Logic.Internal

---- SYNTAX ----

type Atom = String

data Form = Bot | At Atom | Neg Form | Con Form Form | Box Form
  deriving (Eq,Ord,Show,Generic)
instance NFData Form

instance Stringable Form where
  toString Bot       = "⊥"
  toString (At a)    = a
  toString (Neg f)   = "¬" ++ toString f
  toString (Con f g) = "(" ++ toString f ++ " & " ++ toString g ++ ")"
  toString (Box f)   = "☐" ++ toString f

o,p,q,r,s :: Form
[o,p,q,r,s] = map At ["o","p","q","r","s"]

ppAts :: [Atom] -> String
ppAts []  = [ ]
ppAts [a] = a
ppAts (a:as) = a ++ "," ++ ppAts as

top :: Form
top = Neg Bot

(!) :: Form -> Form
(!) = Neg

(-->) :: Form -> Form -> Form
(-->) = imp

(<-->) :: Form -> Form -> Form
f <--> g = Con (f --> g) (g --> f)

-- | Give me diamonds!
dia :: Form -> Form
dia = Neg . Box . Neg

-- | Atoms occurring in a formula.
atomsIn :: Valuation Form
atomsIn Bot       = []
atomsIn (At a)    = [a]
atomsIn (Neg f)   = atomsIn f
atomsIn (Con f g) = sort . nub $ concatMap atomsIn [f,g]
atomsIn (Box f)   = atomsIn f

imp,dis :: Form -> Form -> Form
imp f g = Neg (    f `Con` Neg g)
dis f g = Neg (Neg f `Con` Neg g)

conSet,disSet :: [Form] -> Form
conSet []     = Bot
conSet [f]    = f
conSet (f:fs) = Con f (conSet fs)
disSet []     = top
disSet [f]    = f
disSet (f:fs) = dis f (disSet fs)

-- | Simplify a formula by removing double negations etc.
simplify :: Form -> Form
simplify = fixpoint simstep where
  simstep Bot           = Bot
  simstep (At a)        = At a
  simstep (Neg (At a))  = Neg (At a)
  simstep (Neg (Neg g)) = simstep g
  simstep (Neg f)       = Neg (simstep f)
  simstep (Con Bot _  ) = Bot
  simstep (Con _   Bot) = Bot
  simstep (Con g h)
    | h == g            = h
    | Neg h == g        = Bot
    | h == Neg g        = Bot
    | otherwise         = Con (simstep g) (simstep h)
  simstep (Box f)       = Box $ simstep f

-- | Complexity of a formula.
complexity :: Form -> Integer
complexity Bot       = 0
complexity (At _)    = 0
complexity (Neg f)   = 1 + complexity f
complexity (Con f g) = 1 + maximum (map complexity [f,g])
complexity (Box f)   = 1 + complexity f

-- | Size of a formula, aka number of subformulas
size :: Form -> Integer
size Bot       = 0
size (At _)    = 0
size (Neg f)   = 1 + size f
size (Con f g) = 2 + sum (map size [f,g]) -- why 2+ and not 1+ here?
size (Box f)   = 1 + size f

-- | Get the immediate subformulas.
immediateSubformulas :: Form -> [Form]
immediateSubformulas Bot       = []
immediateSubformulas (At _)    = []
immediateSubformulas (Neg f)   = [f]
immediateSubformulas (Con f g) = [f,g]
immediateSubformulas (Box f)   = [f]

-- | Substitute g for a in f.
-- Example: substitute (p->q) q (q ^ r) == ((p->q) ^ r)
substitute :: Form -> Atom -> Form -> Form
substitute _ _ Bot       = Bot
substitute g a (At b)    = if a == b then g else At b
substitute g a (Neg f)   = Neg $ substitute g a f
substitute g a (Con f h) = Con (substitute g a f) (substitute g a h)
substitute g a (Box f)   = Box $ substitute g a f


---- SEMANTICS ----

type Valuation w = w -> [Atom]

type Relation w = w -> [w]

data Model w = KrM { worlds :: [w], val :: Valuation w, rel :: Relation w }

exampleModel :: Model Int
exampleModel = KrM [1,2] myval (const [1]) where
  myval 1 = ["p", "q"]
  myval 2 = ["r"]
  myval _ = undefined

instance Show w => Show (Model w) where
  show m  = concat
    [ "KrM "
    , show (worlds m)
    , " (\\w -> concat $ "
    , intercalate " ++ " (map (\w -> "[ " ++ show (val m w) ++ " | w == " ++ show w ++ "] " ) (worlds m)),
    ") "
    , "(\\w -> concat $ "
    , intercalate " ++ " (map (\w -> "[ " ++ show (rel m w) ++ " | w == " ++ show w ++ "]") (worlds m))
    , ")"
    ]

instance Show w => DispAble (Model w) where
  toGraph m =
    mapM_ (\w -> do
      node (show w) [shape Circle, toLabel $ show w ++ ":" ++ ppAts (val m w)]
      mapM_ (\w' -> edge (show w) (show w') []) (rel m w)
      ) (worlds m)

instance (Eq w, Show w) => DispAble (Model w, w) where
  toGraph (m, actual) =
    mapM_ (\w -> do
      node (show w) [ shape (if w == actual then DoubleCircle else Circle)
                    , toLabel $ show w ++ ":" ++ ppAts (val m w)]
      mapM_ (\w' -> edge (show w) (show w') []) (rel m w)
      ) (worlds m)

-- | Evaluate formula on a model at a world
eval :: (Model w, w) -> Form -> Bool
eval (_,_) Bot       = False
eval (m,w) (At a)    = a `elem` val m w
eval (m,w) (Neg f)   = not $ eval (m,w) f
eval (m,w) (Con f g) = eval (m,w) f && eval (m,w) g
eval (m,w) (Box f)   = all (\w' -> eval (m,w') f) (rel m w)

globeval :: Model w -> Form -> Bool
globeval m f = all (\w -> eval (m,w) f) (worlds m)

-- | All possible valuations for a given set of atoms.
-- We have `length (allVals myAts) == 2^(length myAts)`
allVals :: [Atom] -> [[Atom]]
allVals = powerset

-- | All possible Kripke models for a given set of atoms up to given size.
-- There are 2^(length myAts) possible valuations, we have to pick n many
-- and there are (2^n) subsets of [1..n], we need n many for the relation.
-- Hence `length (allModels myAts n) = n^(2^(length myAts)) * n^(2^n)`
allModels :: [Atom] -> Integer -> [Model Integer]
allModels _   0 = error "Empty model!?"
allModels myAts 1 =
    [ KrM [1] (const myValFor1) myRel | myValFor1 <- allVals myAts, myRel <- [ const [], const [1] ] ]
allModels myAts n =
    [ KrM (oldWorlds ++ [n]) newVal newRel
      | KrM oldWorlds oldVal oldRel <- allModels myAts (n-1)
      , newRel <- [ \w -> if w == n then relForN else oldRel w | relForN <- powerset [1..n] ]
      , newVal <- [ \w -> if w == n then valForN else oldVal w | valForN <- allVals myAts ]
    ]

-- | Check semantic validity.
-- Ridiculously expensive and only usable for short formulas with 2 propositions.
-- The finite model property is used as follows.
-- We check allModels for the atomsIn f up to size 2^(size f).
-- First we print the amount of models that will be checked.
isValid :: Form -> IO Bool
isValid f = do
  let myAts = atomsIn f
  let k = 2 ^ size f :: Integer
  let amount = sum [ n ^ ((2::Integer) ^ length myAts) * (n::Integer)^((2::Integer)^n) | n <- [(1::Integer)..k] ]
  putStrLn $ "Checking " ++ show amount ++ " models ..."
  return $ all (`globeval` f) $ concat [ allModels myAts n | n <- [1..k] ]


---- RANDOM GENERATION ----

-- | Generate random formulas.
instance Arbitrary Form where
  arbitrary = simplify <$> sized genForm where
    factor = 3
    genForm 0 = oneof [ pure Bot, At . return <$> choose ('p','q') ]
    genForm 1 = At . return <$> choose ('p','s')
    genForm n = oneof
      [ pure Bot
      , At . return <$> choose ('p','s')
      , Neg <$> genForm (n `div` factor)
      , Con <$> genForm (n `div` factor) <*> genForm (n `div` factor)
      , Box <$> genForm (n `div` factor)
      ]
  shrink = immediateSubformulas

-- | Generate random models.
instance Arbitrary (Model Int) where
  arbitrary = do
    nonActualWorlds <- sublistOf [1..9]
    let myWorlds = 0 : nonActualWorlds
    let totalRel = [(x,y) | x <- myWorlds, y <- myWorlds ]
    myW <- mapM (\w -> do
                    truths <- sublistOf (map return "pqrst")
                    return (w, truths)
                ) myWorlds
    let myVal w = fromJust $ lookup w myW
    myR <- sublistOf totalRel
    let myRel w = map snd $ filter ((==w) . fst) myR
    return $ KrM myWorlds myVal myRel
  -- TODO: shrink
