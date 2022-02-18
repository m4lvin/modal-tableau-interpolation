{-# LANGUAGE FlexibleInstances #-}

module Logic.PDL where

import Data.List
import Test.QuickCheck

import Logic.Internal

---- SYNTAX ----

type Atom = String

data Form = Bot | At Atom | Neg Form | Con Form Form | Box Prog Form
  deriving (Eq,Ord,Show)

data Prog = Ap Atom | Cup Prog Prog | Prog :- Prog | Star Prog | NStar Prog | Test Form
  deriving (Eq,Ord,Show)

class Stringable a where
  toString :: a -> String
  toStrings :: [a] -> String
  toStrings xs = intercalate ", " $ map toString xs
  pp :: a -> IO ()
  pp = putStrLn . toString

instance (Stringable a, Stringable b) => Stringable (a, Maybe b) where
  toString (x, Just  y) = toString x ++ " ^ " ++ toString y
  toString (x, Nothing) = toString x

instance Stringable Form where
  toString Bot        = "⊥"
  toString (At at)    = at
  toString (Neg f)    = "¬" ++ toString f
  toString (Con f g)  = "(" ++ toString f ++ " & " ++ toString g ++ ")"
  toString (Box pr f) = "[" ++ toString pr ++ "]" ++ toString f ++ ""

instance Stringable Prog where
  toString (Ap ap)     = ap
  toString (Cup p1 p2) = "(" ++ toString p1 ++ " ∪ " ++ toString p2 ++ ")"
  toString (p1 :- p2)  = "(" ++ toString p1 ++ " ; " ++ toString p2 ++ ")"
  toString (Test f)    = "?(" ++ toString f ++ ")"
  toString (Star pr)   = toString pr ++ "*"
  toString (NStar pr)  = toString pr ++ "ⁿ"

class HasAtoms a where
  isAtomic :: a -> Bool

instance HasAtoms Form where
  isAtomic (At _) = True
  isAtomic _      = False

instance HasAtoms Prog where
  isAtomic (Ap _) = True
  isAtomic _      = False

class ContainsNStars a where
  nToStar :: a -> a

instance ContainsNStars Form where
  nToStar Bot           = Bot
  nToStar (At at)       = At at
  nToStar (Neg (At at)) = Neg (At at)
  nToStar (Neg f)       = Neg (nToStar f)
  nToStar (Con f g)     = Con (nToStar f) (nToStar g)
  nToStar (Box pr f)    = Box (nToStar pr) (nToStar f)

instance ContainsNStars Prog where
  nToStar (Ap ap)     = Ap ap
  nToStar (Cup p1 p2) = Cup (nToStar p1) (nToStar p2)
  nToStar (p1 :- p2)  = nToStar p1 :- nToStar p2
  nToStar (Test f)    = Test (nToStar f)
  nToStar (Star pr)   = Star (nToStar pr)
  nToStar (NStar pr)  = Star (nToStar pr)

o,p,q,r,s :: Form
[o,p,q,r,s] = map At ["o", "p", "q", "r", "s"]

a,b,c,d :: Prog
[a,b,c,d] = map Ap ["a", "b", "c", "d"]

ppAts :: [Atom] -> String
ppAts []       = [ ]
ppAts [at]     = at
ppAts (at:ats) = at ++ "," ++ ppAts ats

top :: Form
top = Neg Bot

(!) :: Form -> Form
(!) = Neg

dis :: Form -> Form -> Form
dis f g = Neg (Con (Neg f) (Neg g))

imp :: Form -> Form -> Form
imp f g = Neg (Con f (Neg g))

(-->) :: Form -> Form -> Form
(-->) = imp

(<-->) :: Form -> Form -> Form
f <--> g = Con (f --> g) (g --> f)

dia :: Prog -> Form -> Form
dia pr f = Neg (Box pr (Neg f))

-- | Atoms occurring in a formula or program.
class ContainsAtoms t where
  atomsIn :: t -> [Atom]

instance ContainsAtoms Form where
  atomsIn Bot        = []
  atomsIn (At at)    = [at]
  atomsIn (Neg f)    = atomsIn f
  atomsIn (Con f g)  = sort . nub $ concatMap atomsIn [f,g]
  atomsIn (Box pr f) = sort . nub $ atomsIn pr ++ atomsIn f

instance ContainsAtoms Prog where
  atomsIn (Ap at)     = [at]
  atomsIn (Cup p1 p2) = sort . nub $ concatMap atomsIn [p1,p2]
  atomsIn (p1 :- p2)  = sort . nub $ concatMap atomsIn [p1,p2]
  atomsIn (Test f)    = atomsIn f
  atomsIn (Star pr)   = atomsIn pr
  atomsIn (NStar pr)  = atomsIn pr

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
  simstep (At at)       = At at
  simstep (Neg (At at)) = Neg (At at)
  simstep (Neg (Neg g)) = simstep g
  simstep (Neg f)       = Neg (simstep f)
  simstep (Con Bot _)   = Bot
  simstep (Con _ Bot)   = Bot
  simstep (Con f g)     = Con (simstep f) (simstep g)
  simstep (Box pr f)    = Box (simplifyProg pr) $ simstep f

simplifyProg :: Prog -> Prog
simplifyProg = fixpoint simstep where
  simstep (Ap ap)       = Ap ap
  simstep (Cup pr1 pr2) | pr1 == pr2 = pr1
                        | otherwise  = Cup (simstep pr1) (simstep pr2) -- TODO: merge sub-Cups
  simstep (pr1 :- pr2)  = simstep pr1 :- simstep pr2
  simstep (Star  pr)    = Star (simstep pr)
  simstep (NStar pr)    = NStar (simstep pr)
  simstep (Test   f)    = Test (simplify f)

immediateSubFormulas :: Form -> [Form]
immediateSubFormulas Bot       = []
immediateSubFormulas (At _)    = []
immediateSubFormulas (Neg f)   = [f]
immediateSubFormulas (Con f g) = [f,g]
immediateSubFormulas (Box _ f)   = [f]
-- FIXME: subformulas from Star?

immediateSubPrograms :: Prog -> [Prog]
immediateSubPrograms (Ap _) = []
immediateSubPrograms (Cup p1 p2) = [p1, p2]
immediateSubPrograms (p1 :- p2) =  [p1, p2]
immediateSubPrograms (Star p1) = [p1]
immediateSubPrograms (NStar p1) = [p1]
immediateSubPrograms (Test f) = map Test $ immediateSubFormulas f

---- SEMANTICS ----

-- TODO


---- RANDOM GENERATION ----

-- TODO
-- | Generate random formulas.
instance Arbitrary Form where
  arbitrary = simplify <$> sized genForm where
    factor = 3
    genForm 0 = elements [ Bot, top, o, p, q, r, s ]
    genForm 1 = elements [ Bot, top, o, p, q, r, s ]
    genForm n = oneof
      [ elements [ Bot, top, o, p, q, r, s ]
      , Neg <$> genForm (n `div` factor)
      , Con <$> genForm (n `div` factor) <*> genForm (n `div` factor)
      , Box <$> arbitrary <*> genForm (n `div` factor)
      ]
  shrink = immediateSubFormulas

instance Arbitrary Prog where
  arbitrary = simplifyProg <$> sized genProg where
    factor = 3
    genProg 0 = elements [ Test top, Test Bot, a, b, c, d ]
    genProg 1 = elements [ Test top, Test Bot, a, b, c, d ]
    genProg n = oneof
      [ elements [ Test top, Test Bot, a, b, c, d ]
      , Cup <$> genProg (n `div` factor) <*> genProg (n `div` factor)
      , (:-) <$> genProg (n `div` factor) <*> genProg (n `div` factor)
      , Star <$> genProg (n `div` factor)
      -- TODO: also generate NStar formulas??
      , Test <$> arbitrary
      ]
  shrink = immediateSubPrograms
