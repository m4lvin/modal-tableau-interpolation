module Logic.PDL where

import Data.List

import Logic.Internal

---- SYNTAX ----

type Atom = String

data Form = Top | Bot | At Atom | Neg Form | Imp Form Form | Con Form Form | Dis Form Form | Box Prog Form | Dia Prog Form
  deriving (Eq,Ord,Show)

data Prog = Ap Atom | Cup Prog Prog | Prog :- Prog | Star Prog | NStar Prog | Test Form
  deriving (Eq,Ord,Show)

class Stringable a where
  toString :: a -> String
  toStrings :: [a] -> String
  toStrings xs = intercalate ", " $ map toString xs
  pp :: a -> IO ()
  pp = putStrLn . toString

instance Stringable Form where
  toString Top        = "⊤"
  toString Bot        = "⊥"
  toString (At at)    = at
  toString (Neg f)    = "¬" ++ toString f
  toString (Imp f g)  = "(" ++ toString f ++ " → " ++ toString g ++ ")"
  toString (Con f g)  = "(" ++ toString f ++ " & " ++ toString g ++ ")"
  toString (Dis f g)  = "(" ++ toString f ++ " | " ++ toString g ++ ")"
  toString (Box pr f) = "[" ++ toString pr ++ "]" ++ toString f ++ ""
  toString (Dia pr f) = "<" ++ toString pr ++ ">" ++ toString f ++ ""

instance Stringable Prog where
  toString (Ap ap)     = ap
  toString (Cup p1 p2) = "(" ++ toString p1 ++ " ∪ " ++ toString p2 ++ ")"
  toString (p1 :- p2)  = "(" ++ toString p1 ++ " ; " ++ toString p2 ++ ")"
  toString (Test f)    = "?(" ++ toString f ++ ")"
  toString (Star pr)   = toString pr ++ "*"
  toString (NStar pr)  = "(" ++ toString pr ++ ")ⁿ"

-- | Reduce to Form = Top | At Atom | Neg Form | Imp Form Form | Box Prog Form
minLang :: Form -> Form
minLang Top = Top
minLang Bot = Neg Top
minLang (At at)   = At at
minLang (Neg f  ) = Neg (minLang f)
minLang (Con f g) = Neg (Imp (minLang f) (Neg (minLang g)))
minLang (Dis f g) = Imp (Neg (minLang f)) (minLang g)
minLang (Imp f g) = Imp (minLang f) (minLang g)
minLang (Box pr f) = Box pr (minLang f)
minLang (Dia pr f) = Neg $ Box pr (Neg $ minLang f)

o,p,q,r,s :: Form
[o,p,q,r,s] = map At ["o", "p", "q", "r", "s"]

a,b,c,d :: Prog
[a,b,c,d] = map Ap ["a", "b", "c", "d"]

ppAts :: [Atom] -> String
ppAts []       = [ ]
ppAts [at]     = at
ppAts (at:ats) = at ++ "," ++ ppAts ats

(!) :: Form -> Form
(!) = Neg

(-->) :: Form -> Form -> Form
(-->) = Imp

(<-->) :: Form -> Form -> Form
f <--> g = Con (f --> g) (g --> f)

-- | Atoms occurring in a formula or program.
class ContainsAtoms t where
  atomsIn :: t -> [Atom]

instance ContainsAtoms Form where
  atomsIn Bot        = []
  atomsIn Top        = []
  atomsIn (At at)    = [at]
  atomsIn (Neg f)    = atomsIn f
  atomsIn (Imp f g)  = sort . nub $ concatMap atomsIn [f,g]
  atomsIn (Con f g)  = sort . nub $ concatMap atomsIn [f,g]
  atomsIn (Dis f g)  = sort . nub $ concatMap atomsIn [f,g]
  atomsIn (Box pr f) = sort . nub $ atomsIn pr ++ atomsIn f
  atomsIn (Dia pr f) = sort . nub $ atomsIn pr ++ atomsIn f

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
disSet []     = Top
disSet [f]    = f
disSet (f:fs) = Dis f (disSet fs)

-- | Simplify a formula by removing double negations etc.
simplify :: Form -> Form
simplify = fixpoint simstep where
  simstep Top           = Top
  simstep Bot           = Bot
  simstep (At at)       = At at
  simstep (Neg Top)     = Bot
  simstep (Neg Bot)     = Top
  simstep (Neg (At at)) = Neg (At at)
  simstep (Neg (Neg g)) = simstep g
  simstep (Neg f)       = Neg (simstep f)
  simstep (Imp Top f)   = f
  simstep (Imp _   Top) = Top
  simstep (Imp Bot _)   = Top
  simstep (Imp g   Bot) = simstep (Neg g)
  simstep (Imp g   h)   | h == Neg g = Neg g
                        | otherwise  = Imp (simstep g) (simstep h)
  simstep (Con Bot _)   = Bot
  simstep (Con _ Bot)   = Bot
  simstep (Con Top g)   = simstep g
  simstep (Con f Top)   = simstep f
  simstep (Con f g)     = Con (simstep f) (simstep g)
  simstep (Dis Top _)   = Top
  simstep (Dis _ Top)   = Top
  simstep (Dis Bot g)   = simstep g
  simstep (Dis f Bot)   = simstep f
  simstep (Dis f g)     = Dis (simstep f) (simstep g)
  simstep (Box pr f)    = Box (simplifyProg pr) $ simstep f
  simstep (Dia pr f)    = Dia (simplifyProg pr) $ simstep f

simplifyProg :: Prog -> Prog
simplifyProg = fixpoint simstep where
  simstep (Ap ap)       = Ap ap
  simstep (Cup pr1 pr2) | pr1 == pr2 = pr1
                        | otherwise  = Cup (simstep pr1) (simstep pr2) -- TODO: merge sub-Cups
  simstep (pr1 :- pr2)  = simstep pr1 :- simstep pr2
  simstep (Star  pr)    = Star (simstep pr)
  simstep (NStar pr)    = NStar (simstep pr)
  simstep (Test   f)    = Test (simplify f)

-- | Get the immediate subformulas.
immediateSubformulas :: Form -> [Form]
immediateSubformulas Bot       = []
immediateSubformulas Top       = []
immediateSubformulas (At _)    = []
immediateSubformulas (Neg f)   = [f]
immediateSubformulas (Imp f g) = [f,g]
immediateSubformulas (Con f g) = [f,g]
immediateSubformulas (Dis f g) = [f,g]
immediateSubformulas (Box _ f)   = [f]
immediateSubformulas (Dia _ f)   = [f]
-- FIXME: subformulas from Star?


---- SEMANTICS ----

-- TODO


---- RANDOM GENERATION ----

-- TODO
