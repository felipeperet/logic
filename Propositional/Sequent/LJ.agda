module Propositional.Sequent.LJ where

open import Propositional.Syntax
open import Propositional.Lemmas

-- Inference rules for the LJ system.
data _⇒_ : Ctx → Form → Set where

  ax : ∀ {Γ A}
    → Γ , A ⇒ A

  ∧R : ∀ {Γ A B}
    → Γ ⇒ A
    → Γ ⇒ B
    → Γ ⇒ A ∧ B

  ∧L₁ : ∀ {Γ A B C}
    → Γ , A ∧ B , A ⇒ C
    → Γ , A ∧ B     ⇒ C

  ∧L₂ : ∀ {Γ A B C}
    → Γ , A ∧ B , B ⇒ C
    → Γ , A ∧ B     ⇒ C

  ⊃R : ∀ {Γ A B}
    → Γ , A ⇒ B
    → Γ     ⇒ A ⊃ B

  ⊃L : ∀ {Γ A B C}
    → Γ , A ⊃ B     ⇒ A
    → Γ , A ⊃ B , B ⇒ C
    → Γ , A ⊃ B     ⇒ C

  ∨R₁ : ∀ {Γ A B}
    → Γ ⇒ A
    → Γ ⇒ A ∨ B

  ∨R₂ : ∀ {Γ A B}
    → Γ ⇒ B
    → Γ ⇒ A ∨ B

  ∨L : ∀ {Γ A B C}
    → Γ , A ∨ B , A ⇒ C
    → Γ , A ∨ B , B ⇒ C
    → Γ , A ∨ B     ⇒ C

  ⊤R : ∀ {Γ}
    → Γ ⇒ ⊤

  ⊥L : ∀ {Γ C}
    → Γ , ⊥' ⇒ C

-- Postulating the exchange structural rule.
postulate
  xch : ∀ {Γ Δ C}
    → Γ ~ Δ
    → Γ ⇒ C
    → Δ ⇒ C

-- Operators precedence.
infix 4 _⇒_
