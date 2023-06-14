module Logic.PDL.Prove.UnravelStar where

import Logic.PDL

pref ::  [Prog] -> Either [Prog] Form -> Either [Prog] Form
pref _   (Right f1) = Right f1
pref ps1 (Left ps2) = Left (ps1 ++ ps2)

-- | Unravel a program under a star in a box.
-- Given the program under the star, how can
-- Note three levels of lists for: multiple branches, multiple formulas, multiple boxes.
g :: Prog -> [[Either [Prog] Form]]
g (Ap ap)     = [[Left [Ap ap]]]
g (Cup p1 p2) = [ l1 ++ l2  | l1 <- g p1, l2 <- g p2 ]
g (p1 :- p2)  = [ [pref [p2] pf | pf <- l1 ] | l1 <- g p1 ]
g (Test f1)   = [ [Right (Neg f1)], [] ]
g (Star pr)   = g (pr :- Star pr) -- TODO ?
g (NStar _)   = error "NStar will be removed."

-- | Unravel a program under a star in a diamond.
f :: Prog -> [[Either [Prog] Form]]
f (Ap ap)     = undefined -- TODO
f (Cup p1 p2) = concat [ [l1, l2] | l1 <- g p1, l2 <- g p2 ]
f (p1 :- p2)  = [ [pref [p2] pf | pf <- l1 ] | l1 <- g p1 ]
f (Test f1)   = [ ] -- TODO ?
f (Star pr)   = g (pr :- Star pr) -- TODO ?
f (NStar _)   = error "NStar will be removed."
