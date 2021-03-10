module Propositional.Sequent.Properties.Cut where

open import Propositional.Syntax
open import Propositional.Lemmas
open import Propositional.Sequent.LJ
open import Propositional.Sequent.Properties.Contraction
open import Propositional.Sequent.Properties.Weakening

open import Data.Nat
open import Data.Maybe

-- Proving the admissibility of cut for LJ system.
⇒-cut : ∀ {Γ A C}
  → ℕ
  → Γ     ⇒ A
  → Γ , A ⇒ C
  → Maybe (Γ ⇒ C)
⇒-cut zero _ _        = nothing
⇒-cut (suc n) ax E    = ⇒-contr n E
⇒-cut (suc n) D ax    = just D
⇒-cut (suc n) (∧R D D₁) (∧L₁ E) = ⇒-cut n (⇒-wk D) E >>= λ x
  → ⇒-cut n (∧R D D₁) x
⇒-cut (suc n) (∧R D D₁) (∧L₂ E) = ⇒-cut n (⇒-wk D₁) E >>= λ x
  → ⇒-cut n (∧R D D₁) x
⇒-cut (suc n) (⊃R D) (⊃L E E₁) = ⇒-cut n (⊃R D) E >>= λ x
  → ⇒-cut n x D >>= λ x₁
  → ⇒-cut n (⇒-wk x₁) E₁ >>= λ x₂
  → ⇒-cut n (⊃R D) x₂
⇒-cut (suc n) (∨R₁ D) (∨L E E₁) = ⇒-cut n (⇒-wk D) E >>= λ x
  → ⇒-cut n (∨R₁ D) x
⇒-cut (suc n) (∨R₂ D) (∨L E E₁) = ⇒-cut n (⇒-wk D) E₁ >>= λ x
  → ⇒-cut n (∨R₂ D) x
⇒-cut (suc n) (∧L₁ D) E = ⇒-cut n D (xch Swap (⇒-wk E)) >>= λ x → just (∧L₁ x)
⇒-cut (suc n) (∧L₂ D) E = ⇒-cut n D (xch Swap (⇒-wk E)) >>= λ x → just (∧L₂ x)
⇒-cut (suc n) (⊃L D D₁) E = ⇒-cut n D₁ (xch Swap (⇒-wk E)) >>= λ x → just (⊃L D x)
⇒-cut (suc n) (∨L D D₁) E = ⇒-cut n D (xch Swap (⇒-wk E)) >>= λ x
  → ⇒-cut n D₁ (xch Swap (⇒-wk E)) >>= λ x₁ → just (∨L x x₁)
⇒-cut (suc n) D (∧R E E₁) = ⇒-cut n D E  >>= λ x
  → ⇒-cut n D E₁ >>= λ x₁ → just (∧R x x₁)
⇒-cut (suc n) D (⊃R E)  = ⇒-cut n (⇒-wk D) (xch Swap E) >>= λ x → just (⊃R x)
⇒-cut (suc n) D (∨R₁ E) = ⇒-cut n D E >>= λ x → just (∨R₁ x)
⇒-cut (suc n) D (∨R₂ E) = ⇒-cut n D E >>= λ x → just (∨R₂ x)
⇒-cut (suc n) _ ⊤R = just ⊤R
⇒-cut (suc n) ⊥L _ = just ⊥L
