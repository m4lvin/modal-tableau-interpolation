{-# LANGUAGE OverloadedStrings #-}
module Logic.PDL.Examples where

import Logic.PDL
import Logic.PDL.Parse ()

-- | Formulas that should be provable.
someValidities :: [Form]
someValidities =
  [ top
  , Neg Bot
  , "p | ¬p"
  , "[a]¬p | <a>p"
  , "[a*]p <-> [a**]p"
  , "¬(¬[(?q ; a)*]⊤ ∧ ¬[(a ∪ ?p)*]q)"
  , "¬¬¬(¬[(?q ; a)*]⊤ ∧ ¬[(a ∪ ?p)*]q)"
  , "[c**]⊤ ∧ [?⊥]r"
  , "[c]p v ([c]⊤ ∧ [?⊥]r)"
  , "[c]p v ([c*]⊤ ∧ [?⊥]r)"
  , "[a*]T v [a*]p"
  , "[a*]p v [a*]T"
  , "[?p*]⊤"
  , "[(?q u b)*]p <-> [b*]p"
  , "[(b u ?q)*]p <-> [b*]p"
  ]

someValidImplications :: [Form]
someValidImplications =
  [ "⊥ -> T"
  , "[a ∪ b]p -> [a]p"
  , "<a>p ->  <a u b> p"
  , "[a ∪ b]p -> [a]p"
  , "[a ∪ b]p -> [b]p"
  , "<a ∪ b>p -> <a>p ∨ <b>p"
  , "[a*]p -> [a][a][a]p"
  , "[b*]p -> [(b ; b)*]p"
  , "[(a ∪ b)*](p ∧ q) -> [b ; b](q ∨ [c]r)"
  , "[(a ∪ b)*](p ∧ q) -> [(b ; b)*](q ∨ [c]r)"
  , "([a]p ∧ [b](p ∧ q)) -> [a ∪ b]p"
  , "([a*]p ∧ [b](p ∧ q)) -> [a* ∪ b]p"
  , "[a*]p -> <a*>p"
  , "[a* ∪ ?p]q -> [a ∪ ?r]q"
  , "q -> [a]T"
  , "[?p u ?¬p](r & ¬r) -> q"
  , "[?p u ?¬p]F -> q"
  , "T -> [c]T"
  , "[a*]p -> [a**]p"
  , "[a**]p -> [a*]p"
  , "¬[a*]p -> ¬[a**]p"
  , "¬[a**]p -> ¬[a*]p"
  , "[a* u ?p]q -> [a u ?r]q"
  , "q -> [c]¬F"
  , "(q ∧ ¬[?([?⊤*]s)*]⊤) -> q"
  , "(q ∧ ¬[?([?⊤*]s)*]⊤) -> (q ^ q)"
  , "[?⊤]s -> [?([(?⊥)*]⊤)]s"
  , "[(a u b)*]p -> [a*]p"
  , "[(a u b)*]p -> [b*]p"
  , "[(a u b)*]p -> [a**]p"
  , "[(a u b)*]p -> [b**]p"
  , "[(a u b)*]p -> [a***]p"
  , "[(a u b)*]p -> [b***]p"
  , "[(a u b)*]p -> [a****]p"
  , "[(a u b)*]p -> [b****]p"
  , "[(a u b)*]p -> [a*****]p"
  , "[(a u b)*]p -> [b*****]p"
  , "¬[c][(c ; d)**]⊤ -> p"
  , "s -> [?(¬q)*]⊤"
  , "q -> <(?p;a)*>q"
  , "[(b*;c)*]r -> [c]r" -- relevant for unraveling
  , "[(b**;c)*]r -> [c]r"
  , "[a*](p v [a*]p) -> [a*]p" -- to get a proper I(Y)
  -- to trigger wrong interpolant bug:
  , "[a*; (a u b*)]p -> [a][a*][b*]p"
  -- to trigger wrong interpolant problem:
  , "[(a u b)*]p -> [(a u b*)*]p"
  , "[(a u b)*]p -> [(a* u b)*]p"
  , "p & [a][(a ∪ b)*]p & [b][(a ∪ b)*]p -> [b][b*][(a ∪ b*)*]p"
  , "(p ∧ [a][a*](p ∨ [a*]p)) -> [a][a*]p" -- non-trivial test in interpolant
  ]

-- | Formulas that should *not* be provable.
someNonValidities :: [Form]
someNonValidities =
  [ Neg top
  , dia (Cup a b) p --> dia a p
  , Box (a :- Star a) p --> dia (a :- Star a) p
  , Con (Box a p) (Box b q) --> Box (Cup a b) (Con p q)
  , Box (Star a) (dia a p) -- depends on reading of MB condition 6
  , Neg $ Box (Star a) (dia a p) -- depends on reading of MB condition 6
  , Box (Star a) (dia a top)
  , Neg $ Box (Star a) (dia a top) -- depends on reading of MB condition 6
  , "<(?p;a)*>q -> q" -- matters for unraveling
  , "<(?p;a)*>q -> (p -> q)"
  , "q -> [(?p;a)*]q"
  , "[(?T;?T)*]p -> q"
  , "[(?q u a)*]p"
  , "[(?q)*]p"
  , "[(?p)*]p"
  , "[a*]p"
  , "[a]~p v [b]~q"  -- needs multi-diamond counter model
  , "~(~p ^ ~[a]~p ^ ~[b]~q)"
  , "p & [a][a]p -> [a*]p" -- broken while writing unfoldDiamondLoaded
  , "[a*]¬[a]¬p -> p"
  , "[(?⊥ ∪ ?⊤) ; (d ; c)]r" -- broken counter model
  , "~[(?⊥ ∪ ?⊤) ; (d ; c)]r"
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

-- | Example model with two worlds.
-- Program a has loops at both worlds.
-- Program b goes from world 1 to 2 and back.
exampleLoop :: Model Int
exampleLoop = KrM
  [ (1, ["p", "q"])
  , (2, ["r"]) ]
  [ ("a", [(1,1),(2,2)])
  , ("b", [(2,1),(1,2)]) ]

-- | Example model conisting of a binary tree.
binaryTree :: Int -> Model Int
binaryTree k = KrM
  [ (w, ['p':show w]) | w <- [1..k] ]
  [ ("a", [(x,x*2  ) | x <- [1..k], x*2   <= k ])
  , ("b", [(x,x*2+1) | x <- [1..k], x*2+1 <= k ]) ]

-- | Example model conisting of a ring.
ring :: Int -> Model Int
ring k = KrM
  [ (w, ['p':show w]) | w <- [1..k] ]
  [ ("a", (k,1) : [(x, x+1) | x <- [1..(k-1)] ]) ]
