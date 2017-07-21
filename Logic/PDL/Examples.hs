module Logic.PDL.Examples where

import Logic.PDL

someValidities :: [Form]
someValidities =
  [ Box (Cup a b) p --> Box a p
  , Dia (Cup a b) p --> Dis (Dia a p) (Dia b p)
  , Box (Star a) p --> Box a (Box a (Box a p))
  -- TODO: add more
  ]

segerbergFor :: Form -> Form -> Prog -> Prog -> [Form]
segerbergFor f g x y =
  [ Box x Top
  , Box x (Con f g) <--> Con (Box x f) (Box x g)
  , Box (x :- y)  f <--> Box x (Box y f)
  , Box (Cup x y) f <--> Con (Box x f) (Box y f)
  , Box (Star x)  f <--> Con f (Box (x :- Star x) f)
  -- , Box (Test f) g  <--> (f --> g)
  ]

-- ([*a]p → (p & [(a ; *a)]p))

segerberg :: [Form]
segerberg = segerbergFor p q a b

borzechowski :: (Form,Form)
borzechowski = (x1,x2) where
  x1 = Box (Star (a :- a)) (p `Con` Box (a :- (b `Cup` c)) Bot)
  x2 = Neg (Box (Star a) (p `Dis` Box c q))
