{-# LANGUAGE FlexibleInstances, DeriveGeneric #-}

module Logic.PDL where

import Control.DeepSeq(NFData)
import Data.List
import Data.GraphViz hiding (Star)
import Data.GraphViz.Types.Monadic hiding ((-->))
import GHC.Generics (Generic)
import Test.QuickCheck

import Logic.Internal

-- * SYNTAX

type Atom = String

data Form = Bot | At Atom | Neg Form | Con Form Form | Box Prog Form
  deriving (Eq,Ord,Show,Generic)
instance NFData Form

data Prog = Ap Atom | Cup Prog Prog | Prog :- Prog | Star Prog | Test Form
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

class HasAtoms a where
  isAtomic :: a -> Bool

instance HasAtoms Form where
  isAtomic (At _) = True
  isAtomic _      = False

instance HasAtoms Prog where
  isAtomic (Ap _) = True
  isAtomic _      = False

o,p,q,r,s :: Form
[o,p,q,r,s] = map At ["o", "p", "q", "r", "s"]

a,b,c,d :: Prog
[a,b,c,d] = map Ap ["a", "b", "c", "d"]

ppAts :: [Atom] -> String
ppAts []       = [ ]
ppAts [at]     = at
ppAts (at:ats) = at ++ "," ++ ppAts ats

-- | Top
top :: Form
top = Neg Bot

-- | Disjunction
dis :: Form -> Form -> Form
dis f g = Neg (Con (Neg f) (Neg g))

-- | Implication
imp :: Form -> Form -> Form
imp f g = Neg (Con f (Neg g))

-- | Nice implication
(-->) :: Form -> Form -> Form
(-->) = imp

-- | Biimplication
(<-->) :: Form -> Form -> Form
f <--> g = Con (f --> g) (g --> f)

-- | Diamond operator, the dual of Box.
dia :: Prog -> Form -> Form
dia pr f = Neg (Box pr (Neg f))

-- | Prefix a formula with multiple boxes.
boxes :: [Prog] -> Form -> Form
boxes progs f1 = foldr Box f1 progs

-- | n-ary conjunction and disjunction.
multicon, multidis :: [Form] -> Form
multicon [] = top
multicon fs = foldl1 Con fs
multidis [] = Bot
multidis fs = foldl1 dis fs

-- | n-ary union of programs - unsafe, will error on [].
multicup :: [Prog] -> Prog
multicup = foldl1 Cup

-- | While-loop as a PDL program.
while :: Form -> Prog -> Prog
while f prg = Star (Test f :- prg) :- Test (Neg f)

-- | If-then-else as a PDL program.
ite :: Form -> Prog -> Prog -> Prog
ite f p1 p2 = (Test f :- p1) `Cup` (Test (Neg f) :- p2)

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

instance ContainsAtoms a => ContainsAtoms [a] where
  atomsIn xs = sort $ nub $ concatMap atomsIn xs

conSet,disSet :: [Form] -> Form
conSet []     = top
conSet [f]    = f
conSet (f:fs) = Con f (conSet fs)
disSet []     = Bot
disSet [f]    = f
disSet (f:fs) = dis f (disSet fs)

-- | Measure of a formula or a program (Lemma 2, page 20)
class HasMeasure a where
  measure :: a -> Integer

instance HasMeasure Prog where
  measure (Ap _)    = 0
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

-- * Simple and Simplified Formulas

-- | Def 9: closed sets for fomulas.
isClosed :: [Form] -> Bool
isClosed fs = Bot `elem` fs || any (\f -> Neg f `elem` fs) fs

class CanBeSimple a where
  isSimple :: a -> Bool

instance CanBeSimple a => CanBeSimple [a] where
  isSimple = all isSimple

-- | Def 9: simple sets for fomulas.
instance CanBeSimple Form where
  isSimple (At _) = True
  isSimple (Neg (At _)) = True
  isSimple (Box _ _) = True
  isSimple (Neg (Box _ _)) = True
  isSimple _ = False

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
  simstep (Con f g) | f == g = simstep f
  simstep (Con f g)     = Con (simstep f) (simstep g)
  simstep (Box (Test (Neg Bot)) f) = simstep f
  simstep (Box pr f)    = Box (simplifyProg pr) $ simstep f

simplifyProg :: Prog -> Prog
simplifyProg = fixpoint simstep where
  simstep (Ap ap)       = Ap ap
  simstep (Cup pr1 pr2) | pr1 == pr2 = pr1
                        | otherwise  = Cup (simstep pr1) (simstep pr2)
  simstep (Test (Neg Bot) :- pr2)  = simstep pr2
  simstep (pr1 :- Test (Neg Bot))  = simstep pr1
  simstep (pr1 :- pr2)  = simstep pr1 :- simstep pr2
  simstep (Star (Star pr)) = Star(simstep pr)
  simstep (Star  pr)    = Star (simstep pr)
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
immediateSubPrograms (Test f) = map Test $ immediateSubFormulas f

dropPartFormulas :: Form -> [Form]
dropPartFormulas Bot       = []
dropPartFormulas (At _)    = []
dropPartFormulas (Neg f)   = [f]
dropPartFormulas (Con f g) = [f,g] ++ [Con f' g | f' <- dropPartFormulas f] ++ [Con f g' | g' <- dropPartFormulas g]
dropPartFormulas (Box x f) = [f] ++ [Box x' f | x' <- dropPartPrograms x] ++ [Box x f' | f' <- dropPartFormulas f]

dropPartPrograms :: Prog -> [Prog]
dropPartPrograms (Ap _) = []
dropPartPrograms (Cup p1 p2) = [p1,p2] ++ [Cup p1' p2  | p1' <- dropPartPrograms p1] ++ [Cup p1  p2' | p2' <- dropPartPrograms p2]
dropPartPrograms (p1 :- p2)  = [p1,p2] ++ [p1' :- p2  | p1' <- dropPartPrograms p1] ++ [p1  :- p2' | p2' <- dropPartPrograms p2]
dropPartPrograms (Star p1)   = map Star $ dropPartPrograms p1
dropPartPrograms (Test f)    = map Test $ dropPartFormulas f

-- * SEMANTICS

-- | Kripke models with worlds of some arbitrary type.
data Model a = KrM { worldsOf :: [(a, [Atom])]
                   , progsOf  :: [(Atom,[(a,a)])]
                   } deriving (Eq,Show)

val :: (Show a, Eq a) => Model a -> a -> [Atom]
val m w = case lookup w (worldsOf m) of
  Just truths -> truths
  Nothing     -> error $ "Could not find world " ++ show w ++ " in this model:\n" ++ show m

rel :: (Show a, Eq a) => Model a -> Atom -> a -> [a]
rel m pr w = case lookup pr (progsOf m) of
  Just rl -> map snd $ filter ((== w) . fst ) rl
  Nothing -> [] -- assume that non-mentioned program has an empty relation!

instance (Eq a, Ord a, Show a) => DispAble (Model a) where
  toGraph m =
    mapM_ (\(w,props) -> do
                        node (show w) [shape Circle, toLabel $ show w ++ ":" ++ ppAts props]
                        mapM_ (\(ap,_) -> mapM_ (\w' -> if w `elem` rel m ap w'
                                                      then do when (w < w') (edge (show w) (show w') [ edgeEnds Both, toLabel ap ])
                                                              when (w == w') (edge (show w) (show w') [ toLabel ap ])
                                                      else edge (show w) (show w') [ toLabel ap ] )
                                        (rel m ap w)) (progsOf m)
          ) (worldsOf m)

instance (Eq a, Ord a, Show a) => DispAble (Model a, a) where
  toGraph (m, actual) =
    mapM_ (\(w,props) -> do
                        node (show w) [shape $ if w == actual then DoubleCircle else Circle
                                      , toLabel $ show w ++ ":" ++ ppAts props]
                        mapM_ (\(ap,_) -> mapM_ (\w' -> if w `elem` rel m ap w'
                                                      then do when (w < w') (edge (show w) (show w') [ edgeEnds Both, toLabel ap ])
                                                              when (w == w') (edge (show w) (show w') [ toLabel ap ])
                                                      else edge (show w) (show w') [ toLabel ap ] )
                                        (rel m ap w)) (progsOf m)          ) (worldsOf m)

-- | Evaluate formula on a pointed model
eval :: (Show a, Eq a) => (Model a, a) -> Form -> Bool
eval (_,_) Bot       = False
eval (m,w) (At at)   = at `elem` val m w
eval (m,w) (Neg f)   = not $ eval (m,w) f
eval (m,w) (Con f g) = eval (m,w) f && eval (m,w) g
eval (m,w) (Box pr f) = all (\w' -> eval (m,w') f) (relval m pr w)

-- | \(\vDash\)
(|=) :: (Show a, Eq a) => (Model a, a) -> Form -> Bool
(|=) = eval

-- | Evaluate a program on a model
relval :: (Show a, Eq a) => Model a -> Prog -> a -> [a]
relval m (Ap ap)     = rel m ap
relval m (Cup p1 p2) = \w -> nub (relval m p1 w ++ relval m p2 w)
relval m (p1 :- p2)  = concatMap (relval m p2) . relval m p1
relval m (Test f)    = \w -> [ w | eval (m,w) f ]
relval m (Star pr)   = \w -> lfpList (relval m pr) [w]

-- | Least fixpoint.
lfp :: Eq a => (a -> a) -> a -> a
lfp f x = if f x == x then x else lfp f (f x)

-- | Lazy least fixpoint for lists.
lfpList :: Eq a => (a -> [a]) -> [a] -> [a]
lfpList _ []  = []
lfpList f set = set ++ rest where
  rest | all (`elem` set) (concatMap f set) = set
       | otherwise = lfpList f (set ++ (concatMap f set \\ set))

globeval :: (Show a, Eq a) => Model a -> Form -> Bool
globeval m f = all (\(w,_) -> eval (m,w) f) (worldsOf m)

-- * Random generation

-- | Generate random formulas.
instance Arbitrary Form where
  arbitrary = sized genForm where
    factor = 10
    genForm 0 = elements [ Bot, top, o, p, q, r, s ]
    genForm 1 = elements [ Bot, top, o, p, q, r, s ]
    genForm n = oneof
      [ elements [ Bot, top, o, p, q, r, s ]
      , Neg <$> genForm (n `div` factor)
      , Con <$> genForm (n `div` factor) <*> genForm (n `div` factor)
      , Box <$> arbitrary <*> genForm (n `div` factor)
      ]
  shrink f = dropPartFormulas f ++ immediateSubFormulas f ++ [ simplify f | simplify f /= f]

instance Arbitrary Prog where
  arbitrary = sized genProg where
    factor = 10
    genProg 0 = elements [ Test top, Test Bot, a, b, c, d ]
    genProg 1 = elements [ Test top, Test Bot, a, b, c, d ]
    genProg n = oneof
      [ elements [ Test top, Test Bot, a, b, c, d ]
      , Cup <$> genProg (n `div` factor) <*> genProg (n `div` factor)
      , (:-) <$> genProg (n `div` factor) <*> genProg (n `div` factor)
      , Star <$> genProg (n `div` factor)
      , Test <$> arbitrary
      ]
  shrink x = dropPartPrograms x ++ immediateSubPrograms x ++ [ simplifyProg x | simplifyProg x /= x ]

newtype SimplifiedForm = SF Form deriving (Eq,Ord,Show)

-- | Generate random simplified formulas.
instance Arbitrary SimplifiedForm where
  arbitrary = SF . simplify <$> arbitrary
  shrink (SF g) = map SF $ shrink g

-- | Generate random models.
instance Arbitrary (Model Int) where
  arbitrary = do
    nonActualWorlds <- sublistOf [1..9]
    let myWorlds = 0 : nonActualWorlds
    let totalRel = [(x,y) | x <- myWorlds, y <- myWorlds ]
    myW <- mapM (\w -> do
                    truths <- sublistOf (map return "pqrst")
                    return (w, truths)
                ) myWorlds
    myR <- mapM ((\prg -> do
                    links <- sublistOf totalRel
                    return (prg, links)
                 ) . return ) "abcd"
    return $ KrM myW myR
  -- TODO: shrink
