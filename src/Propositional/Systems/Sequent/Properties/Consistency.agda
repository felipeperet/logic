module Propositional.Systems.Sequent.Properties.Consistency where

open import Propositional.Syntax
open import Propositional.Systems.Sequent.LJ

open import Relation.Nullary

-- Proving that LJ is consistent.
⇒-consis : ¬ (∅ ⇒ ⊥')
⇒-consis = λ ()
