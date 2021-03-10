module Propositional.Sequent.LJT where

open import Propositional.Syntax
open import Propositional.Lemmas

-- Inference rules for the LJT system
-- (the T stands for Terminating)
data _⇒ₜ_ : Ctx → Form → Set where

  ax : ∀ {Γ A}
    → Γ , A ⇒ₜ A

  ∧⇒ₜ : ∀ {Γ A B G}
    → Γ , A , B  ⇒ₜ G
    → Γ , A ∧ B  ⇒ₜ G

  ⇒ₜ∧ : ∀ {Γ A B}
    → Γ ⇒ₜ A
    → Γ ⇒ₜ B
    → Γ ⇒ₜ A ∧ B

  ∨⇒ₜ : ∀ {Γ A B G}
    → Γ , A     ⇒ₜ G
    → Γ , B     ⇒ₜ G
    → Γ , A ∨ B ⇒ₜ G

  ⇒ₜ∨₁ : ∀ {Γ A B}
    → Γ ⇒ₜ A
    → Γ ⇒ₜ A ∨ B

  ⇒ₜ∨₂ : ∀ {Γ A B}
    → Γ ⇒ₜ B
    → Γ ⇒ₜ A ∨ B

  ⊃⇒ₜ¹ : ∀ {Γ A B G}
    → Γ , A , B     ⇒ₜ G
    → Γ , A ⊃ B , A ⇒ₜ G

  ⊃⇒ₜ² : ∀ {Γ B D C G}
    → Γ , C ⊃ (D ⊃ B) ⇒ₜ G
    → Γ , (C ∧ D) ⊃ B ⇒ₜ G

  ⊃⇒ₜ³ : ∀ {Γ B D C G}
    → Γ , C ⊃ B , D ⊃ B ⇒ₜ G
    → Γ , (C ∨ D) ⊃ B   ⇒ₜ G

  ⊃⇒ₜ⁴ : ∀ {Γ B D C G}
    → Γ , B           ⇒ₜ G
    → Γ , D ⊃ B       ⇒ₜ C ⊃ D
    → Γ , (C ⊃ D) ⊃ B ⇒ₜ G

  ⇒ₜ⊃ : ∀ {Γ A B}
    → Γ , A ⇒ₜ B
    → Γ     ⇒ₜ A ⊃ B

  ⇒ₜ⊤ : ∀ {Γ}
    → Γ ⇒ₜ ⊤

  ⊥⇒ₜ : ∀ {Γ G}
    → Γ , ⊥' ⇒ₜ G

-- Postulating the exchange structural rule.
postulate
  xch : ∀ {Γ Δ C}
    → Γ ~ Δ
    → Γ ⇒ₜ C
    → Δ ⇒ₜ C

-- Operators precedence.
infix 4 _⇒ₜ_
