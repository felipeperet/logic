module Propositional.Translation.NaturalToSequent where

open import Propositional.Syntax
open import Propositional.Systems.Sequent.LJ
open import Propositional.Systems.Sequent.Properties.Cut
open import Propositional.Systems.Sequent.Properties.Weakening
open import Propositional.Systems.Natural.NJ

open import Data.Nat
open import Data.Maybe

-- Translating Natural Deduction to Sequent Calculus derivations.
⊢-transl : ∀ {Γ C}
  → ℕ
  → Γ ⊢ C
  → Maybe (Γ ⇒ C)
⊢-transl zero _        = nothing
⊢-transl (suc n) (` x) = ⊢-transl n (` x)
⊢-transl (suc n) (ƛ D) = ⊢-transl n D >>= λ x → just (⊃R x)
⊢-transl (suc n) (D ∙ D₁) = ⊢-transl n D >>= λ x
  → ⊢-transl n D₁ >>= λ x₁ → ⇒-cut n x (⊃L (⇒-wk x₁) ax)
⊢-transl (suc n) ⟨ D , D₁ ⟩ = ⊢-transl n D >>= λ x
  → ⊢-transl n D₁ >>= λ x₁ → just (∧R x x₁)
⊢-transl (suc n) (fst D) = ⊢-transl n D >>= λ x → ⇒-cut n x ((∧L₁ ax))
⊢-transl (suc n) (snd D) = ⊢-transl n D >>= λ x → ⇒-cut n x (∧L₂ ax)
⊢-transl (suc n) (inl D) = ⊢-transl n D >>= λ x → just (∨R₁ x)
⊢-transl (suc n) (inr D) = ⊢-transl n D >>= λ x → just (∨R₂ x)
⊢-transl (suc n) (case D of D₁ ∣ D₂) = ⊢-transl n D >>= λ x
  → ⊢-transl n D₁ >>= λ x₁
  → ⊢-transl n D₂ >>= λ x₂ → ⇒-cut n x (∨L (xch Swap (⇒-wk x₁)) (xch Swap (⇒-wk x₂)))
⊢-transl (suc n) T-intro = just ⊤R
⊢-transl (suc n) ⊥-elim  = just ⊥L
