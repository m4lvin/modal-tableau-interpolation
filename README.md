# Logic

Implementation of propositional and some modal logic, for educational purposes.
The big goal is a tableaux prover for PDL.

## Usage and Test Examples

    λ> import Logic.BasicModal.Prove.Tree
    λ> import Logic.BasicModal.Examples
    λ> import Test.QuickCheck
    λ> map provable someValidities
    [True,True,True,True]
    λ> map provable someNonValidities
    [False,False,False,False]

## TODO

- enumeration of formulas

- modal logic

- check out Kuznets' work: https://sites.google.com/site/kuznets/interpol_hyper_v2.pdf
