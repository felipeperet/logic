# logic library

This is an attempt at formalizing different logics and deductive systems.

## Agda

Agda is a dependently typed functional language developed by Norell at the Chalmers University of Technology as his Ph.D. Thesis. It also works as an interactive proof assistant, because of the Curry-Howard correspondence.

The current library release works with Agda-2.6.2 and stdlib-1.5.

## Content

Up to now, he have:

### in Intuitionistic Propositional Logic:
  * Formalized inference rules for the systems [NJ](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Natural/NJ.agda), [LJ](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Sequent/LJ.agda) and [LJT](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Sequent/LJT.agda).
  * Formalized inference rules for [Bi-directional Natural Deduction](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Natural/Bidirectional.agda).
  * Proved [soundness](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Natural/Properties/Soundness.agda) and [completeness](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Natural/Properties/Completeness.agda) properties for Bi-directional Natural Deduction.
  * Proved properties of Sequent Calculus such as [weakening](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Sequent/Properties/Weakening.agda), [contraction](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Sequent/Properties/Contraction.agda) and [cut](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Sequent/Properties/Cut.agda).
  * Proved Natural Deduction's [consistency](https://github.com/felipeperet/logic/blob/master/Propositional/Systems/Natural/Properties/Consistency.agda).


