# Logic

Implementation of propositional and some modal logic, for educational purposes.
The big goal is a tableaux prover for PDL.

## Examples

    λ> import Logic.BasicModal.Prove.Tree
    λ> provable (Box (p --> q) --> (Box p --> Box q))
    True
    
    λ> import Logic.BasicModal.Interpolation.ProofTree
    λ> interpolateShow ( Box (Imp (At 'p') (At 'q')) , Imp (Neg (Box (Imp (At 's') (At 'q')))) (Neg (Box (At 'p'))) )
    ... (showing graphviz window) ...
    Box (Imp (At 'p') (At 'q'))

# TODO

## Basic Modal Logic

- [X] mark active formula in tableaus

- [X] remove Top as primitive, use top

## PDL Todo

- [X] restricted language with Con, not Imp as primitive, as Borzechowski does

- all the basic modal changes

extra conditions:
1. [-] when reaching an atomic Box or NegBox, go back from n to *
2. [ ] instead of X;[a^n]P reach X
3. [ ] apply rules to n-formula whenever possible / prioritise them!
4. [X] Never apply a rule to a ¬[a^n] node
5. [ ] directly after M+ do not apply M-
6. [ ] ...
7. [ ] ...

- [ ] find test cases that fail due to empty side edge cases for interpolant defs

- fix empty side edge cases

## BONUS STUFf

- use Graphviz HTML labels to format nicely, with active formula in bold etc.

- enumeration of formulas??

- check out Kuznets' work: https://sites.google.com/site/kuznets/interpol_hyper_v2.pdf
