module Propositional.Systems.Natural.Properties.Consistency where

open import Propositional.Syntax
open import Propositional.Systems.Natural.NJ
open import Propositional.Systems.Sequent.LJ
open import Propositional.Translation.NaturalToSequent
open import Propositional.Systems.Sequent.Properties.Consistency

open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Relation.Nullary

-- Proving the consistency property for Natural Deduction.
⊢-consis : ℕ → Maybe (¬ (∅ ⊢ ⊥'))
⊢-consis zero    = nothing
⊢-consis (suc n)
  = just λ p → let
                         p₁ : Maybe (∅ ⇒ ⊥')
                         p₁ = ⊢-transl (suc n) p
                     in maybe ⇒-consis impossible p₁
              where
                     postulate impossible : Data.Empty.⊥
