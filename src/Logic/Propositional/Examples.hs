module Logic.Propositional.Examples where

import Logic.Propositional
import Logic.Propositional.Interpolation
import Logic.Propositional.Interpolation.Naive as Naive

-- | A valid formula too complicated for the List prover.
weirdform :: Form
weirdform = disSet
  [ Neg (At 'r')
  , conSet [At 'r',Neg (conSet [disSet [At 'r']])]
  , Neg (At 'r')
  , Neg (conSet [disSet [disSet [At 'p']],Neg (At 'p')])
  , Neg (Neg (conSet [Neg (At 'q')]))
  ]

interpolateNaive :: IO ()
interpolateNaive = do
  let f = Con p q
  let g = dis   q r
  let i = simplify $ Naive.interpolate (f,g)
  mapM_ print [f,g,i]
  print $ i `isInterpolantFor` (f,g)
