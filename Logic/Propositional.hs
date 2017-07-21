module Logic.Propositional where

import Control.Monad
import Data.List
import Test.QuickCheck
import Logic.Internal

type Atom = Char

data Form = Top | At Atom | Neg Form | Imp Form Form
  deriving (Eq,Ord)

instance (Show Form) where
  show Top       = "⊤"
  show (At a)    = [a]
  show (Neg f)   = "¬" ++ show f
  show (Imp f g) = "(" ++ show f ++ " → " ++ show g ++ ")"

-- TODO: instance (Enum Form) where ...

bot,o,p,q,r,s :: Form
bot = Neg Top
[o,p,q,r,s] = map At ['o','p','q','r','s']

(!) :: Form -> Form
(!) = Neg

(-->) :: Form -> Form -> Form
(-->) = Imp

type Model = Atom -> Bool

-- | Evaluate formula on a model.
eval :: Model -> Form -> Bool
eval _ Top       = True
eval m (At a)    = m a
eval m (Neg f)   = not $ eval m f
eval m (Imp f g) = eval m f <= eval m g

-- | Atoms occurring in a formula.
atomsIn :: Form -> [Atom]
atomsIn Top       = []
atomsIn (At a)    = [a]
atomsIn (Neg f)   = atomsIn f
atomsIn (Imp f g) = sort . nub $ concatMap atomsIn [f,g]

-- | Generate all models for a set of atoms.
allModels :: [Atom] -> [Model]
allModels []     = [ undefined ]
allModels (a:as) = [ \x -> if x==a then bit else m x | m <- allModels as, bit <- [True,False] ]

-- | Check semantic validity.
isValid :: Form -> Bool
isValid f = all (`eval` f) (allModels (atomsIn f))

con,dis :: Form -> Form -> Form
con f g = Neg (f --> Neg g)
dis f g = Neg f --> g

conSet,disSet :: [Form] -> Form
conSet []     = bot
conSet [f]    = f
conSet (f:fs) = con f (conSet fs)
disSet []     = Top
disSet [f]    = f
disSet (f:fs) = dis f (disSet fs)

sat,unsat :: [Form] -> Bool
unsat fs = isValid $ Neg (conSet fs)
sat = not . unsat

-- | Simplify a formula by removing double negations etc.
simplify :: Form -> Form
simplify = fixpoint simstep where
  simstep Top             = Top
  simstep (At a)          = At a
  simstep (Neg Top)       = Neg Top
  simstep (Neg (At a))    = Neg (At a)
  simstep (Neg (Neg g))   = simstep g
  simstep (Neg (Imp g h)) = Neg (simstep $ Imp g h)
  simstep (Imp Top f)     = f
  simstep (Imp _   Top)   = Top
  simstep (Imp g h)
    | g == bot   = Top
    | h == bot   = simstep (Neg g)
    | h == Neg g = Neg g
    | otherwise  = Imp (simstep g) (simstep h)

-- | Complexity of a formula.
complexity :: Form -> Int
complexity Top       = 0
complexity (At _)    = 0
complexity (Neg f)   = 1 + complexity f
complexity (Imp f g) = 1 + maximum (map complexity [f,g])

-- | Size of a formula.
size :: Form -> Int
size Top       = 0
size (At _)    = 1
size (Neg f)   = 1 + size f
size (Imp f g) = 1 + sum (map size [f,g])

-- | Get the immediate subformulas.
immediateSubformulas :: Form -> [Form]
immediateSubformulas Top       = []
immediateSubformulas (At _)    = []
immediateSubformulas (Neg f)   = [f]
immediateSubformulas (Imp f g) = [f,g]

-- | Substitute g for a in f.
-- Example: substitute (p->q) q (q ^ r) == ((p->q) ^ r)
substitute :: Form -> Atom -> Form -> Form
substitute _ _ Top       = Top
substitute g a (At b)    = if a == b then g else At b
substitute g a (Neg f)   = Neg $ substitute g a f
substitute g a (Imp f h) = Imp (substitute g a f) (substitute g a h)

-- | Generate random formulas.
instance Arbitrary Form where
  arbitrary = fmap simplify (sized genForm) where
    factor = 2
    genForm 0 = oneof [ pure Top, At <$> choose ('p','z') ]
    genForm 1 = At <$> choose ('p','z')
    genForm n = oneof
      [ pure Top
      , At <$> choose ('p','z')
      , Neg <$> genForm (n `div` factor)
      , Imp <$> genForm (n `div` factor) <*> genForm (n `div` factor)
      , conSet <$> genForms (n `div` factor)
      , disSet <$> genForms (n `div` factor) ]
    genForms k = do
      n <- choose (1, min k 4)
      replicateM n (genForm k)
  shrink = immediateSubformulas
