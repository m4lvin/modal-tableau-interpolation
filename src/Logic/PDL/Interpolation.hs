module Logic.PDL.Interpolation where

import Logic.Internal
import Logic.PDL
import Logic.PDL.Prove.Tree

isInterpolantFor :: Form -> (Form,Form) -> Bool
isInterpolantFor i (f,g) =
     provable (f --> i)
  && provable (i --> g)
  && atomsIn i ⊆ (atomsIn f ∩ atomsIn g)

testIPgen :: ((Form,Form) -> Maybe Form) -> (Form,Form) -> Bool
testIPgen intfct (f,g) = case intfct (f,g) of
  Just h -> h `isInterpolantFor` (f,g)
  Nothing -> False
