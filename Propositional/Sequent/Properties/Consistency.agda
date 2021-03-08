module Propositional.Sequent.Properties.Consistency where

open import Propositional.Syntax
open import Propositional.Sequent.LJ

open import Relation.Nullary

-- Proving that LJ is consistent.
⇒-consis : ¬ (∅ ⇒ ⊥')
⇒-consis = λ ()
