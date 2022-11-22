{-# LANGUAGE FlexibleInstances, DeriveGeneric #-}

module Logic.PDL where

import Control.DeepSeq(NFData)
import Data.List
import Data.GraphViz hiding (Star)
import Data.GraphViz.Types.Monadic hiding ((-->))
import GHC.Generics (Generic)
import Test.QuickCheck

import Logic.Internal

---- SYNTAX ----

type Atom = String

data Form = Bot | At Atom | Neg Form | Con Form Form | Box Prog Form
  deriving (Eq,Ord,Show,Generic)
instance NFData Form

data Prog = Ap Atom | Cup Prog Prog | Prog :- Prog | Star Prog | NStar Prog | Test Form
  deriving (Eq,Ord,Show,Generic)
instance NFData Prog

instance Stringable Form where
  toString Bot        = "⊥"
  toString (At at)    = at
  toString (Neg Bot)  = "⊤"
  toString (Neg (Con (Neg f) (Neg g)))  = "(" ++ toString f ++ " ∨ " ++ toString g ++ ")"
  toString (Neg f)    = "¬" ++ toString f
  toString (Con f g)  = "(" ++ toString f ++ " ∧ " ++ toString g ++ ")"
  toString (Box (Cup p1 p2) f) = "[" ++ toString p1 ++ " ∪ " ++ toString p2 ++ "]" ++ toString f ++ ""
  toString (Box (p1 :- p2) f)  = "[" ++ toString p1 ++ " ; " ++ toString p2 ++ "]" ++ toString f ++ ""
  toString (Box pr f) = "[" ++ toString pr ++ "]" ++ toString f ++ ""

instance Stringable Prog where
  toString (Ap ap)     = ap
  toString (Cup p1 p2) = "(" ++ toString p1 ++ " ∪ " ++ toString p2 ++ ")"
  toString (p1 :- p2)  = "(" ++ toString p1 ++ " ; " ++ toString p2 ++ ")"
  toString (Test (At at))   = "?" ++ at
  toString (Test Bot)       = "?⊥"
  toString (Test (Neg Bot)) = "?⊤"
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
  isNormal :: a -> Bool

instance ContainsNStars Form where
  nToStar Bot           = Bot
  nToStar (At at)       = At at
  nToStar (Neg (At at)) = Neg (At at)
  nToStar (Neg f)       = Neg (nToStar f)
  nToStar (Con f g)     = Con (nToStar f) (nToStar g)
  nToStar (Box pr f)    = Box (nToStar pr) (nToStar f)
  isNormal Bot           = True
  isNormal (At _)        = True
  isNormal (Neg f)       = isNormal f
  isNormal (Con f g)     = isNormal f && isNormal g
  isNormal (Box pr f)    = isNormal pr && isNormal f

instance ContainsNStars Prog where
  nToStar (Ap ap)     = Ap ap
  nToStar (Cup p1 p2) = Cup (nToStar p1) (nToStar p2)
  nToStar (p1 :- p2)  = nToStar p1 :- nToStar p2
  nToStar (Test f)    = Test (nToStar f)
  nToStar (Star pr)   = Star (nToStar pr)
  nToStar (NStar pr)  = Star (nToStar pr)
  isNormal (Ap _)     = True
  isNormal (Cup p1 p2) = isNormal p1 && isNormal p2
  isNormal (p1 :- p2)  = isNormal p1 && isNormal p2
  isNormal (Test f)    = isNormal f
  isNormal (Star pr)   = isNormal pr
  isNormal (NStar _)   = False

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

-- | n-ary conjunction and disjunction.
multicon, multidis :: [Form] -> Form
multicon [] = top
multicon fs = foldl1 Con fs
multidis [] = Bot
multidis fs = foldl1 dis fs

-- | n-ary union of programs - unsafe, will error on [].
multicup :: [Prog] -> Prog
multicup = foldl1 Cup

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

instance ContainsAtoms a => ContainsAtoms [a] where
  atomsIn xs = sort $ nub $ concatMap atomsIn xs

conSet,disSet :: [Form] -> Form
conSet []     = Bot
conSet [f]    = f
conSet (f:fs) = Con f (conSet fs)
disSet []     = top
disSet [f]    = f
disSet (f:fs) = dis f (disSet fs)

-- | Measure of a formula or a program (Lemma 2, page 20)
class HasMeasure a where
  measure :: a -> Integer

instance HasMeasure Prog where
  measure (Ap _)    = 0
  measure (NStar _) = 0
  measure (Test f)   = maximum [measure f, measure (Neg f)] + 1
  measure (p1 :- p2) = measure p1 + measure p2 + 1
  measure (Cup p1 p2) = measure p1 + measure p2 + 1
  measure (Star pr)  = 1 + measure pr

instance HasMeasure Form where
  measure Bot              = 0
  measure (Neg Bot)        = 0 -- NOTE: Borzechowski omits this case, see page 20
  measure (At _)           = 0
  measure (Neg (At _))     = 0
  measure (Neg (Neg f))    = 1 + measure f
  measure (Con f g)        = 1 + measure f + measure g
  measure (Neg (Con f g))  = 1 + measure (Neg f) + measure (Neg g)
  measure (Box pr f)       = 1 + measure pr + measure f
  measure (Neg (Box pr f)) = 1 + measure pr + measure f

instance HasMeasure a => HasMeasure [a] where
  measure = sum . map measure

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
  simstep (Con (Neg Bot) f) = simstep f
  simstep (Con f (Neg Bot)) = simstep f
  simstep (Con f g)     = Con (simstep f) (simstep g)
  simstep (Box (Test (Neg Bot)) f) = simstep f
  simstep (Box pr f)    = Box (simplifyProg pr) $ simstep f

simplifyProg :: Prog -> Prog
simplifyProg = fixpoint simstep where
  simstep (Ap ap)       = Ap ap
  simstep (Cup pr1 pr2) | pr1 == pr2 = pr1
                        | otherwise  = Cup (simstep pr1) (simstep pr2) -- TODO: merge sub-Cups
  simstep (Test (Neg Bot) :- pr2)  = simstep pr2
  simstep (pr1 :- Test (Neg Bot))  = simstep pr1
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

immediateSubPrograms :: Prog -> [Prog]
immediateSubPrograms (Ap _) = []
immediateSubPrograms (Cup p1 p2) = [p1, p2]
immediateSubPrograms (p1 :- p2) =  [p1, p2]
immediateSubPrograms (Star p1) = [p1]
immediateSubPrograms (NStar p1) = [p1]
immediateSubPrograms (Test f) = map Test $ immediateSubFormulas f

---- SEMANTICS ----

type Valuation a = a -> [Atom]

type Relations a = Atom -> a -> [a]

data Model a = KrM { worlds :: [a]
                   , val :: Valuation a
                   , progs :: [Atom]
                   , rel :: Relations a
                   }

instance Show a => Show (Model a) where
  show m = "KrM " ++ show (worlds m) ++ " undefined " ++ show (progs m) ++ " undefined "  -- TODO

instance Show a => DispAble (Model a) where
  toGraph m = mapM_ (\w -> do
                        node (show w) [shape Circle, toLabel $ show w ++ ":" ++ ppAts (val m w)]
                        mapM_(\ap -> mapM_ (\w' -> edge (show w) (show w') [ toLabel ap ]) (rel m ap w)) (progs m)
                    ) (worlds m)

-- | Evaluate formula on a pointed model
eval :: Eq a => (Model a, a) -> Form -> Bool
eval (_,_) Bot       = False
eval (m,w) (At at)   = at `elem` val m w
eval (m,w) (Neg f)   = not $ eval (m,w) f
eval (m,w) (Con f g) = eval (m,w) f && eval (m,w) g
eval (m,w) (Box pr f) = all (\w' -> eval (m,w') f) (relval m pr w)

-- | Evaluate a program on a model
relval :: Eq a => Model a -> Prog -> a -> [a]
relval m (Ap ap)     = rel m ap
relval m (Cup p1 p2) = \w -> nub (relval m p1 w ++ relval m p2 w)
relval m (p1 :- p2)  = concatMap (relval m p2) . relval m p1
relval m (Test f)    = \w -> [ w | eval (m,w) f ]
relval m (Star pr)   = \w -> lfp (concatMap (relval m pr)) [w]
relval m (NStar pr)  = relval m (Star pr)

-- | Least fixpoint.
lfp :: Eq a => (a -> a) -> a -> a
lfp f x = if f x == x then x else lfp f (f x)

globeval :: Eq a => Model a -> Form -> Bool
globeval m f = all (\w -> eval (m,w) f) (worlds m)

---- RANDOM GENERATION ----

-- | Generate random formulas.
instance Arbitrary Form where
  arbitrary = simplify <$> sized genForm where
    factor = 4
    genForm 0 = elements [ Bot, top, o, p, q, r, s ]
    genForm 1 = elements [ Bot, top, o, p, q, r, s ]
    genForm n = oneof
      [ elements [ Bot, top, o, p, q, r, s ]
      , Neg <$> genForm (n `div` factor)
      , Con <$> genForm (n `div` factor) <*> genForm (n `div` factor)
      , Box <$> arbitrary <*> genForm (n `div` factor)
      ]
  shrink f = immediateSubFormulas f ++ [ simplify f | simplify f /= f]

instance Arbitrary Prog where
  arbitrary = simplifyProg <$> sized genProg where
    factor = 4
    genProg 0 = elements [ Test top, Test Bot, a, b, c, d ]
    genProg 1 = elements [ Test top, Test Bot, a, b, c, d ]
    genProg n = oneof
      [ elements [ Test top, Test Bot, a, b, c, d ]
      , Cup <$> genProg (n `div` factor) <*> genProg (n `div` factor)
      , (:-) <$> genProg (n `div` factor) <*> genProg (n `div` factor)
      , Star <$> genProg (n `div` factor)
      , Test <$> arbitrary
      ]
  shrink x = immediateSubPrograms x ++ [ simplifyProg x | simplifyProg x /= x ]
