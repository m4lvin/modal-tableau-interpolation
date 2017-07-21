module Logic.BasicModal.Interpolation where

import Logic.Internal
import Logic.BasicModal
import Logic.BasicModal.Prove.Tree

isInterpolantFor :: Form -> (Form,Form) -> Bool
isInterpolantFor i (f,g) =
     provable (f --> i)
  && provable (i --> g)
  && atomsIn i ⊆ (atomsIn f ∩ atomsIn g)

testIPgen :: ((Form,Form) -> Form) -> (Form,Form) -> Bool
testIPgen intfct (f,g) = intfct (f,g) `isInterpolantFor` (f,g)
