module Logic.PDL.Examples where

import Logic.PDL

someValidities :: [Form]
someValidities =
  [ Box (Cup a b) p --> Box a p
  , dia (Cup a b) p --> dis (dia a p) (dia b p)
  , Box (Star a) p --> Box a (Box a (Box a p))
  , Box (Star b) p --> Box (Star (b :- b)) p
  -- TODO: add more
  ]

segerbergFor :: Form -> Form -> Prog -> Prog -> [Form]
segerbergFor f g x y =
  [ Box x top
  , Box x (Con f g) <--> Con (Box x f) (Box x g)
  , Box (x :- y)  f <--> Box x (Box y f)
  , Box (Cup x y) f <--> Con (Box x f) (Box y f)
  , Box (Star x)  f <--> Con f (Box (x :- Star x) f)
  , Box (Test f) g  <--> (f --> g)
  ]

-- ([*a]p → (p & [(a ; *a)]p))

segerberg :: [Form]
segerberg = segerbergFor p q a b

-- | Example from Borzechowski page 55
borzechowski :: Form
borzechowski = x1 --> x2 where
  x1 = Box (Star (a :- a)) (p `Con` Box (a :- (b `Cup` c)) Bot)
  x2 = (Box (Star a) (p `dis` Box c q))
