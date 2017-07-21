module Logic.Propositional.Interpolation.Naive where

import Data.List

import Logic.Internal
import Logic.Propositional

interpolate :: (Form,Form) -> Form
interpolate (f, g)
  | not (isValid (f --> g)) = error $ "Not valid: " ++ show f ++ " --> " ++ show g
  | atomsIn f ⊆ atomsIn g   = f
  | otherwise               = interpolate (newf, g) where
      newf = dis (substitute Top at f) (substitute bot at f)
      at   = head (atomsIn f \\ atomsIn g)
