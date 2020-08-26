module Logic.BasicModal where

import Data.List
import Data.GraphViz
import Data.GraphViz.Types.Monadic hiding ((-->))
import Test.QuickCheck

import Logic.Internal

---- SYNTAX ----

type Atom = Char

data Form = Bot | At Atom | Neg Form | Imp Form Form | Box Form
  deriving (Eq,Ord,Show)

ppForm :: Form -> String
ppForm Bot       = "⊥"
ppForm (At a)    = [a]
ppForm (Neg f)   = "¬" ++ ppForm f
ppForm (Imp f g) = "(" ++ ppForm f ++ " → " ++ ppForm g ++ ")"
ppForm (Box f)   = "☐" ++ ppForm f

o,p,q,r,s :: Form
[o,p,q,r,s] = map At ['o','p','q','r','s']

ppAts :: [Atom] -> String
ppAts []  = [ ]
ppAts [a] = [a]
ppAts (a:as) = a : "," ++ ppAts as

top :: Form
top = Neg Bot

(!) :: Form -> Form
(!) = Neg

(-->) :: Form -> Form -> Form
(-->) = Imp

(<-->) :: Form -> Form -> Form
f <--> g = con (f --> g) (g --> f)

-- | Give me diamonds!
dia :: Form -> Form
dia = Neg . Box . Neg

-- | Atoms occurring in a formula.
atomsIn :: Form -> [Atom]
atomsIn Bot       = []
atomsIn (At a)    = [a]
atomsIn (Neg f)   = atomsIn f
atomsIn (Imp f g) = sort . nub $ concatMap atomsIn [f,g]
atomsIn (Box f)   = atomsIn f

con,dis :: Form -> Form -> Form
con f g = Neg (f --> Neg g)
dis f g = Neg f --> g

conSet,disSet :: [Form] -> Form
conSet []     = Bot
conSet [f]    = f
conSet (f:fs) = con f (conSet fs)
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
  simstep (Imp Bot _  ) = top
  simstep (Imp g   Bot) = simstep (Neg g)
  simstep (Imp g h)
    | h == Neg g        = Neg g
    | otherwise         = Imp (simstep g) (simstep h)
  simstep (Box f)       = Box $ simstep f

-- | Complexity of a formula.
complexity :: Form -> Integer
complexity Bot       = 0
complexity (At _)    = 0
complexity (Neg f)   = 1 + complexity f
complexity (Imp f g) = 1 + maximum (map complexity [f,g])
complexity (Box f)   = 1 + complexity f

-- | Size of a formula, aka number of subformulas
size :: Form -> Integer
size Bot       = 0
size (At _)    = 0
size (Neg f)   = 1 + size f
size (Imp f g) = 2 + sum (map size [f,g])
size (Box f)   = 1 + size f

-- | Get the immediate subformulas.
immediateSubformulas :: Form -> [Form]
immediateSubformulas Bot       = []
immediateSubformulas (At _)    = []
immediateSubformulas (Neg f)   = [f]
immediateSubformulas (Imp f g) = [f,g]
immediateSubformulas (Box f)   = [f]

-- | Substitute g for a in f.
-- Example: substitute (p->q) q (q ^ r) == ((p->q) ^ r)
substitute :: Form -> Atom -> Form -> Form
substitute _ _ Bot       = Bot
substitute g a (At b)    = if a == b then g else At b
substitute g a (Neg f)   = Neg $ substitute g a f
substitute g a (Imp f h) = Imp (substitute g a f) (substitute g a h)
substitute g a (Box f)   = Box $ substitute g a f


---- SEMANTICS ----

type World = Integer

type Valuation = World -> [Atom]

type Relation = World -> [World]

data Model = KrM { worlds :: [World], val :: Valuation, rel :: Relation}

exampleModel :: Model
exampleModel = KrM [1,2] myval (const [1]) where
  myval 1 = "pq"
  myval 2 = "r"
  myval _ = undefined

instance Show Model where
  show m = "KrM " ++ concatMap (\w -> show w ++ ":" ++ ppAts (val m w) ++ ":" ++ show (rel m w) ++ "; ") (worlds m) ++ "\n"

instance DispAble Model where
  toGraph m =
    mapM_ (\w -> do
      node (show w) [shape Circle, toLabel $ show w ++ ":" ++ ppAts (val m w)]
      mapM_ (\w' -> edge (show w) (show w') []) (rel m w)
      ) (worlds m)

-- | Evaluate formula on a model at a world
eval :: (Model,World) -> Form -> Bool
eval (_,_) Bot       = False
eval (m,w) (At a)    = a `elem` val m w
eval (m,w) (Neg f)   = not $ eval (m,w) f
eval (m,w) (Imp f g) = eval (m,w) f `implies` eval (m,w) g
eval (m,w) (Box f)   = all (\w' -> eval (m,w') f) (rel m w)

globeval :: Model -> Form -> Bool
globeval m f = all (\w -> eval (m,w) f) (worlds m)

-- | All possible valuations for a given set of atoms.
-- We have `length (allVals myAts) == 2^(length myAts)`
allVals :: [Atom] -> [[Atom]]
allVals = powerset

-- | All possible Kripke models for a given set of atoms up to given size.
-- There are 2^(length myAts) possible valuations, we have to pick n many
-- and there are (2^n) subsets of [1..n], we need n many for the relation.
-- Hence `length (allModels myAts n) = n^(2^(length myAts)) * n^(2^n)`
allModels :: [Atom] -> Integer -> [Model]
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
    genForm 0 = oneof [ pure Bot, At <$> choose ('p','q') ]
    genForm 1 = At <$> choose ('p','s')
    genForm n = oneof
      [ pure Bot
      , At <$> choose ('p','s')
      , Neg <$> genForm (n `div` factor)
      , Imp <$> genForm (n `div` factor) <*> genForm (n `div` factor)
      , Box <$> genForm (n `div` factor)
      ]
  shrink = immediateSubformulas
