module Propositional.System.Sequent.Properties.Exchange where

open import Basics.Bijection
open import Basics.Membership
open import Basics.SetEquality
open import Data.List
open import Propositional.Syntax
open import Propositional.System.Sequent.SequentCalculus


exchange : ∀ {Γ Γ' C} → Γ ≈ Γ' → Γ ⇒ C → Γ' ⇒ C
exchange Γ≈Γ' (init x) = init (_⇔_.to (Γ≈Γ' _) x)
exchange Γ≈Γ' (∧R p p₁) = ∧R (exchange Γ≈Γ' p) (exchange Γ≈Γ' p₁)
exchange Γ≈Γ' (∧L₁ x p) = ∧L₁ (≈-∈ Γ≈Γ' x) (exchange (≈-∷ Γ≈Γ') p)
exchange Γ≈Γ' (∧L₂ x p) = ∧L₂ (≈-∈ Γ≈Γ' x) (exchange (≈-∷ Γ≈Γ') p)
exchange Γ≈Γ' (⇒R p) = ⇒R (exchange (≈-∷ Γ≈Γ') p)
exchange Γ≈Γ' (⇒L x p p₁) = ⇒L (≈-∈ Γ≈Γ' x) (exchange Γ≈Γ' p) (exchange (≈-∷ Γ≈Γ') p₁)
exchange Γ≈Γ' (∨R₁ p) = ∨R₁ (exchange Γ≈Γ' p)
exchange Γ≈Γ' (∨R₂ p) = ∨R₂ (exchange Γ≈Γ' p)
exchange Γ≈Γ' (∨L x p p₁) = ∨L (≈-∈ Γ≈Γ' x) (exchange (≈-∷ Γ≈Γ') p) (exchange (≈-∷ Γ≈Γ') p₁)
exchange Γ≈Γ' ⊤R = ⊤R
exchange Γ≈Γ' (⊥L x) = ⊥L (≈-∈ Γ≈Γ' x)
exchange Γ≈Γ' (structural x p) = exchange (≈-trans x Γ≈Γ') p
