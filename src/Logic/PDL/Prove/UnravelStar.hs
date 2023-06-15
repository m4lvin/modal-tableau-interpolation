module Logic.PDL.Prove.UnravelStar where

import Logic.PDL

-- | Prefix a formula with multiple boxes. -- TODO move to Logic.PDL
boxes :: [Prog] -> Form -> Form
boxes []        f1 = f1
boxes (pr:rest) f1 = Box pr (boxes rest f1)

-- | Unravel a program under a star in a diamond.
f :: Prog -> [[[Prog]]]
f (Ap ap)     = [[[Ap ap]]]
f (Cup p1 p2) = f p1 ++ f p2
f (pa :- pb)  = [ [ra ++ [pb] | ra <- ga ] | ga <- f pa ]
f (Test _)    = [ ]
f (Star pr)   = f (pr :- Star pr)
f (NStar _)   = error "NStar will be removed."

-- | Unravel a program under a star in a box.
-- Given the program under the star, how can
-- Note three levels of lists for: multiple branches, multiple formulas, multiple boxes.
g :: Prog -> [[[Prog]]]
g (Ap ap)     = [[[Ap ap]]]
g (Cup p1 p2) = [ l1 ++ l2  | l1 <- g p1, l2 <- g p2 ]
g (pa :- pb)  = [ [ra ++ [pb] | ra <- ga ] | ga <- g pa ]
g (Test _)    = [ ]
g (Star pr)   = g (pr :- Star pr)
g (NStar _)   = error "NStar will be removed."
