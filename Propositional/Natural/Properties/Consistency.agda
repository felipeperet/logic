module Propositional.Natural.Properties.Consistency where

open import Propositional.Syntax
open import Propositional.Natural.NJ
open import Propositional.Sequent.LJ
open import Propositional.Translation
open import Propositional.Sequent.Properties.Consistency

open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Relation.Nullary

-- Proving the consistency property for Natural Deduction.
⊢-consistency : ℕ → Maybe (¬ (∅ ⊢ ⊥'))
⊢-consistency zero = nothing
⊢-consistency (suc n) = just λ p → let
                                        p1 : Maybe (∅ ⇒ ⊥')
                                        p1 = ⊢-transl (suc n) p
                                   in maybe ⇒-consis impossible p1
                             where
                               postulate impossible : Data.Empty.⊥
