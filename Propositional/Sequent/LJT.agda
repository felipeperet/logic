module Propositional.Sequent.LJT where

open import Propositional.Syntax
open import Propositional.Lemmas

-- Inference rules for the LJT system
-- (the T stands for Terminating)
data _⇒ₜ_ : Ctx → Form → Set where

  ax : ∀ {Γ A}
    → Γ , A ⇒ₜ A

  ∧R : ∀ {Γ A B}
    → Γ ⇒ₜ A
    → Γ ⇒ₜ B
    → Γ ⇒ₜ A ∧ B

  ∧L₁ : ∀ {Γ A B C}
    → Γ , A ∧ B , A ⇒ₜ C
    → Γ , A ∧ B     ⇒ₜ C

  ∧L₂ : ∀ {Γ A B C}
    → Γ , A ∧ B , B ⇒ₜ C
    → Γ , A ∧ B     ⇒ₜ C

  ⊃R : ∀ {Γ A B}
    → Γ , A ⇒ₜ B
    → Γ     ⇒ₜ A ⊃ B

  ⊃L : ∀ {Γ A B C}
    → Γ , A ⊃ B     ⇒ₜ A
    → Γ , A ⊃ B , B ⇒ₜ C
    → Γ , A ⊃ B     ⇒ₜ C

  ∨R₁ : ∀ {Γ A B}
    → Γ ⇒ₜ A
    → Γ ⇒ₜ A ∨ B

  ∨R₂ : ∀ {Γ A B}
    → Γ ⇒ₜ B
    → Γ ⇒ₜ A ∨ B

  ∨L : ∀ {Γ A B C}
    → Γ , A ∨ B , A ⇒ₜ C
    → Γ , A ∨ B , B ⇒ₜ C
    → Γ , A ∨ B     ⇒ₜ C

  ⊤R : ∀ {Γ}
    → Γ ⇒ₜ ⊤

  ⊥L : ∀ {Γ C}
    → Γ , ⊥' ⇒ₜ C

-- Postulating the exchange structural rule.
postulate
  xch : ∀ {Γ Δ C}
    → Γ ~ Δ
    → Γ ⇒ₜ C
    → Δ ⇒ₜ C

-- Operators precedence.
infix 4 _⇒ₜ_
