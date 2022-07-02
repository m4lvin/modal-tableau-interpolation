module Logic.PDL.Examples where

import Logic.PDL
import Logic.PDL.Parse

-- | Formulas that should be provable.
someValidities :: [Form]
someValidities =
  [ top
  , Neg Bot
  , Box (Cup a b) p --> Box a p
  , dia a p -->  dia (Cup a b) p
  , Box (Cup a b) p --> Box a p
  , dia (Cup a b) p --> dis (dia a p) (dia b p)
  , Box (Star a) p --> Box a (Box a (Box a p))
  , Box (Star b) p --> Box (Star (b :- b)) p
  , Box (Star (Cup a b)) (Con p q) --> Box (b :- b) (dis q (Box c r))
  , Box (Star (Cup a b)) (Con p q) --> Box (Star (b :- b)) (dis q (Box c r))
  , Con (Box a p) (Box b (Con p q)) --> Box (Cup a b) p
  , Con (Box (Star a) p) (Box b (Con p q)) --> Box (Cup (Star a) b) p
  , Box (Star a) p --> dia (Star a) p
  , Box (Star a) p --> Box (Star (Star a)) p
  , Box (Star (Star a)) p --> Box (Star a) p
  , dia (Star a) p --> dia (Star (Star a)) p
  , dia (Star (Star a)) p --> dia (Star a) p
  , fromString "[a* u ?p]q -> [a u ?r]q"
  , fromString "q -> [c]~F"
  ]

-- | Formulas that should *not* be provable.
someNonValidities :: [Form]
someNonValidities =
  [ Neg top
  , dia (Cup a b) p --> dia a p
  , Box (a :- Star a) p --> dia (a :- Star a) p
  , Con (Box a p) (Box b q) --> Box (Cup a b) (Con p q)
  , Box (Star (Test p)) p
  , Box (Star a) (dia a p) -- problematic with condition 6
  , Neg $ Box (Star a) (dia a p) -- problematic with condition 6
  , Box (Star a) (dia a top)
  , Neg $ Box (Star a) (dia a top) -- proven by unsound version of extra condition 6:
  ]

-- | Instances of the Segerberg axioms.
segerbergFor :: Form -> Form -> Prog -> Prog -> [Form]
segerbergFor f g x y =
  [ Box x top
  , Box x (Con f g) <--> Con (Box x f) (Box x g)
  , Box (x :- y)  f <--> Box x (Box y f)
  , Box (Cup x y) f <--> Con (Box x f) (Box y f)
  , Box (Star x)  f <--> Con f (Box (x :- Star x) f)
  , Box (Test f) g  <--> (f --> g)
  ]

-- | Example from Borzechowski page 55
borzechowski :: Form
borzechowski = x1 --> x2 where
  x1 = Box (Star (a :- a)) (p `Con` Box (a :- (b `Cup` c)) Bot)
  x2 = Box (Star a) (p `dis` Box c q)

-- | Example model with two worlds
exampleLoop :: Model Int
exampleLoop = KrM [1,2] myVal ["a"] myRel where
  myVal 1 = ["p", "q"]
  myVal 2 = ["r"]
  myVal _ = undefined
  myRel "a" 1 = [2]
  myRel "b" 2 = [1]
  myRel _   _ = []
