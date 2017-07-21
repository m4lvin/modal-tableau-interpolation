module Logic.Propositional.Interpolation where

import Logic.Internal
import Logic.Propositional

isInterpolantFor :: Form -> (Form,Form) -> Bool
isInterpolantFor i (f,g) =
     isValid (f --> i)
  && isValid (i --> g)
  && atomsIn i ⊆ (atomsIn f  ∩  atomsIn g)

testIPgen :: ((Form,Form) -> Form) -> (Form,Form) -> Bool
testIPgen intfct (f,g) = intfct (f,g) `isInterpolantFor` (f,g)
