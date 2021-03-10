module Propositional.Sequent.Properties.Weakening where

open import Propositional.Syntax
open import Propositional.Sequent.LJ

-- Proving that LJ system admits weakening.
⇒-wk : ∀ {Γ F C}
  → Γ     ⇒ C
  → Γ , F ⇒ C
⇒-wk ax        = xch Swap ax
⇒-wk (∧R D D₁) = ∧R (⇒-wk D) (⇒-wk D₁)
⇒-wk (∧L₁ D)   = xch Swap (∧L₁ (xch (Trans Swap (Skip Swap))
 (⇒-wk D)))
⇒-wk (∧L₂ D)   = xch Swap (∧L₂ (xch (Trans Swap (Skip Swap))
 (⇒-wk D)))
⇒-wk (⊃R D)    = ⊃R (xch Swap (⇒-wk D))
⇒-wk (⊃L D D₁) = xch Swap (⊃L (xch Swap (⇒-wk D))
  (xch (Trans Swap (Skip Swap)) (⇒-wk D₁)))
⇒-wk (∨R₁ D)   = ∨R₁ (⇒-wk D)
⇒-wk (∨R₂ D)   = ∨R₂ (⇒-wk D)
⇒-wk (∨L D D₁) = xch Swap (∨L (xch (Trans Swap (Skip Swap))
 (⇒-wk D))
  (xch (Trans Swap (Skip Swap)) (⇒-wk D₁)))
⇒-wk ⊤R        = ⊤R
⇒-wk ⊥L        = xch Swap ⊥L
