# Modal Tableau with Interpolation

Goal: a tableau prover for propositional logic, the basic modal logic K and propositional dynamic logic (PDL).
The prover should also find interpolants, following the method described by Manfred Borzechowski in 1988.
See <https://malv.in/2020/borzechowski-pdl/> for the original German text and an English translation.

## Notes and Examples

### Propositional Logic

There are two different provers: one based on lists and one a proper tableau.
See [src/Logic/Propositional/Prove](src/Logic/Propositional/Prove).

Interpolation is also implemented twice:
- [Logic.Propositional.Interpolation.Naive](src/Logic/Propositional/Interpolation/Naive.hs) replaces atoms by constants as described in [Wikipedia: Craig interpolation](https://en.wikipedia.org/wiki/Craig_interpolation#Proof_of_Craig's_interpolation_theorem).
- [Logic.Propositional.Interpolation.ProofTree](src/Logic/Propositional/Interpolation/ProofTree.hs) uses Tableaux.

### Basic modal logic K

    stack ghci src/Logic/BasicModal/Prove/Tree.hs
    λ> provable (Box (p --> q) --> (Box p --> Box q))
    True
    λ> provable (p --> Box p)
    False
    
    stack ghci src/Logic/BasicModal/Interpolation/ProofTree.hs
    λ> let (f,g) = ( Box (Imp (At 'p') (At 'q')) , Imp (Neg (Box (Imp (At 's') (At 'q')))) (Neg (Box (At 'p'))) )
    λ> mapM_ (putStrLn .ppForm) [f, g]
    ☐(p → q)
    (¬☐(s → q) → ¬☐p)
    λ> interpolateShow (f,g)
    Showing tableau with GraphViz ...
    Interpolant: ☐(¬¬p → q)
    Simplified interpolant: ☐(p → q)

The last command will also show this tableau:

![](docu/BasicModal-example.png)

### PDL

Work in progress, only the star-free fragment works at the moment.

There is no interpolation implemented here yet.

## Automated Tests

Use `stack test` to run all [tests](tests/).

For PDL we also use the file [formulae_exp_unsat.txt](data/formulae_exp_unsat.txt) from <http://users.cecs.anu.edu.au/~rpg/PDLComparisonBenchmarks/>.

# TODO list

## Basic Modal Logic

- [X] mark active formula in tableaux
- [X] remove Top as primitive, use top

## PDL

- [X] restricted language with Con, not Imp as primitive, as Borzechowski does
- [ ] all the basic modal changes
    - [X] proper search: extend -> extensions
    - [ ] mark/highlight active formula
    - FIXME what else actually?
- [ ] Find test cases that fail due to the empty-side edge cases for (At)-interpolants?
- [ ] Correct definition of (At)-interpolants in the empty-side edge cases.
- [ ] Implement all extra conditions from Borzechowski:
    1. [ ] when reaching an atomic Box or NegBox, go back from n to *
    2. [ ] instead of X;[a^n]P reach X
    3. [ ] apply rules to n-formula whenever possible / prioritise them!
    4. [X] Never apply a rule to a ¬[a^n] node – FIXME and mark as end node!?
    5. [ ] directly after M+ do not apply M-
    6. [ ] close normal nodes with critical predecessors when the whole path is loaded
    7. [ ] ...

Nice to have:

- web interface

- use Graphviz HTML labels for better readability, e.g. highlight the active formula.

## Open Questions

- May other rules like (¬), (^) etc. be applied to marked formulas?

- Can (At) only be applied to marked formulas? (page 24 suggest that!) (otherwise, why not do (At)_C directly on page 56, without (M+) first?)

- What *are* the nodes in the tableau? Concretely: lists, multisets or sets? Finite?
  This matters for the claim that "complexity goes down" / termination.

## Related work

- Rajeev Goré and Florian Widmann (2009): An Optimal On-the-Fly Tableau-Based Decision Procedure for PDL-Satisfiability.
  <https://doi.org/10.1007/978-3-642-02959-2_32>

- Roman Kuznets (2015): Craig Interpolation via Hypersequents.
  <https://sites.google.com/site/kuznets/interpol_hyper_v2.pdf>

- TODO: compare to other PDL and tableaux provers mentioned at <http://www.cs.man.ac.uk/~schmidt/tools/>.
