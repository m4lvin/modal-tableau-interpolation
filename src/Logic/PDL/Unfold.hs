{-# LANGUAGE TupleSections #-}

module Logic.PDL.Unfold where

import Data.List

import Logic.PDL hiding (a,b,c)
import Logic.PDL.Loaded

-- * Unfolding Boxes

-- | Test profiles
type TP = [Form]

allTP :: Prog -> [TP]
allTP alpha = subsequences $ testsOfProgram alpha

unfoldF :: TP -> Prog -> [Form]
unfoldF _ (Ap _) = []
unfoldF l (Test tf) = [Neg tf | tf `notElem` l]
unfoldF l (Cup pa pb) = nub $ unfoldF l pa ++ unfoldF l pb
unfoldF l (pa :- pb) = nub $ unfoldF l pa ++ unfoldF l pb
unfoldF l (Star pa) = unfoldF l pa

unfoldP :: TP -> Prog -> [[Prog]]
unfoldP _ (Ap a) = [ [Ap a] ]
unfoldP l (Test tf) = [ [] | tf `elem` l ]
unfoldP l (Cup pa pb) = nub $ unfoldP l pa ++ unfoldP l pb
unfoldP l (pa :- pb) = nub $
                       [ as ++ [pb] | as <- unfoldP l pa, not (null as) ]
                       ++
                       [bs | [] `elem` unfoldP l pa, bs <- unfoldP l pb]
unfoldP l (Star pa) = [] : [ as ++ [Star pa] | as <- unfoldP l pa, not (null as) ]


unfoldXset :: TP -> Prog -> Form -> [Form]
unfoldXset l pa phi = nub $ unfoldF l pa ++ [ boxes as phi | as <- unfoldP l pa ]

-- | unfold_□(α,ψ)
unfoldBox :: Prog -> Form -> [[Form]]
unfoldBox pa phi = nub $ [ unfoldXset l pa phi | l <- allTP pa ]

-- * Unfolding Diamonds

unfoldH :: Prog -> [ ([Form], [Prog]) ]
unfoldH (Ap at) = [ ([], [Ap at]) ]
unfoldH (Test tf) = [ ([tf], []) ]
unfoldH (Cup pa pb) = nub $ unfoldH pa ++ unfoldH pb
unfoldH (pa :- pb) = nub $
  [ (x, delta ++ [pb])
  | (x, delta) <- unfoldH pa
  , not (null delta) ]
  ++
  [ (x ++ y, delta)
  | (x, []) <- unfoldH pa
  , (y, delta) <- unfoldH pb ]
unfoldH (Star pa) = nub $
  ([], []) :
  [ (x, delta ++ [Star pa])
  | (x, delta) <- unfoldH pa
  , not (null delta) ]

unfoldDiamond :: Prog -> Form -> [[Form]]
unfoldDiamond alpha phi = nub $ [ Neg (boxes delta phi) : f | (f,delta) <- unfoldH alpha ]

-- * Unfolding Loaded Diamonds

loadMulti :: [Prog] -> Form -> Marked Form
loadMulti as phi = (Neg phi, as)


unfoldDiamondLoaded :: Prog -> Marked Form -> [[Marked Form]]
unfoldDiamondLoaded alpha (Neg f, rest) = nub $ [ (Neg f, delta ++ rest) : map (, []) x | (x, delta) <- unfoldH alpha ]
unfoldDiamondLoaded _     (_, _) = error "bad Marked Form"
