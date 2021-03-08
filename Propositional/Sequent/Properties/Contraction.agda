module Propositional.Sequent.Properties.Contraction where

open import Propositional.Sequent.LJ
open import Propositional.Syntax
open import Propositional.Lemmas

open import Data.Nat
open import Data.Maybe

-- Proving that LJ system admits contraction.
⇒-contr : ∀ {Γ A C}
  → ℕ
  → Γ , A , A ⇒ C
  → Maybe (Γ , A ⇒ C)
⇒-contr zero _     = nothing
⇒-contr (suc n) ax = just ax
⇒-contr (suc n) (∧R D D₁) = ⇒-contr n D >>= λ x
  → ⇒-contr n D₁ >>= λ x₁ → just (∧R x x₁)
⇒-contr (suc n) (∧L₁ D)   =
  (⇒-contr n (xch (Trans Swap (Skip Swap)) D)) >>= λ x → just (∧L₁ (xch Swap x))
⇒-contr (suc n) (∧L₂ D)   =
  (⇒-contr n (xch (Trans Swap (Skip Swap)) D)) >>= λ x → just (∧L₂ (xch Swap x))
⇒-contr (suc n) (⊃R D)    =
  (⇒-contr n (xch (Trans Swap (Skip Swap)) D)) >>= λ x → just (⊃R (xch Swap x))
⇒-contr (suc n) (⊃L D D₁) = ⇒-contr n D >>= λ x
  → ⇒-contr n (xch (Trans Swap (Skip Swap)) D₁) >>= λ x₁ → just (⊃L x (xch Swap x₁))
⇒-contr (suc n) (∨R₁ D) = (⇒-contr n D) >>= λ x → just (∨R₁ x)
⇒-contr (suc n) (∨R₂ D) = (⇒-contr n D) >>= λ x → just (∨R₂ x)
⇒-contr (suc n) (∨L D D₁) = ⇒-contr n (xch (Trans Swap (Skip Swap)) D) >>= λ x
  → ⇒-contr n (xch (Trans Swap (Skip Swap)) D₁) >>= λ x₁ → just (∨L (xch Swap x) (xch Swap x₁))
⇒-contr (suc n) ⊤R = just ⊤R
⇒-contr (suc n) ⊥L = just ⊥L
