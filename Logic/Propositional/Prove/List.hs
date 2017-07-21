-- 1. A naive try at tableaux with lists of lists.

module Logic.Propositional.Prove.List where

import Data.List
import Logic.Propositional

type Tableaux = [ ([Form],[Form]) ]

prove :: Form -> IO ()
prove f = loop start where
  start = [ ([],[Neg f]) ]
  step = extend . purge
  loop t = do
    mapM_ (\row -> putStr $ show row ++ [ 'x' | isClosed row ] ++ "\n") t
    if step t == t
      then putStrLn $ if null t then "Q.E.D." else "Not provable."
      else do
        putStrLn "---"
        loop (step t)

isProvable :: Form -> Bool
isProvable f = loop start where
  start = [ ([],[Neg f]) ]
  step = extend . purge
  loop t =
    if step t == t
      then null t
      else loop (step t)

isClosed :: ( [Form],[Form] ) -> Bool
isClosed (fs,gs) = bot `elem` fgs || any (\f -> Neg f `elem` fgs) fgs where
  fgs = fs ++ gs

childrenOf :: Form -> [ [Form] ]
childrenOf Top             = [ ]
childrenOf (At _)          = [ [ ] ]
childrenOf (Imp f g)       = [ [Neg f], [g] ]
childrenOf (Neg Top)       = [ ]
childrenOf (Neg (At _))    = [ [ ] ]
childrenOf (Neg (Neg f))   = [ [f] ]
childrenOf (Neg (Imp f g)) = [ [f, Neg g] ]

extend :: Tableaux -> Tableaux
extend = concatMap extendCase where
  extendCase (old,[ ]) = [ (old,[ ]) ]
  extendCase (old,new) =
    [ (nub $ old ++ [f], nub $ (new \\ [f]) ++ g) | f <- new, g <- childrenOf f ]

purge :: Tableaux -> Tableaux
purge = filter (not . isClosed)
