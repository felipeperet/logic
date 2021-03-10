module Propositional.Sequent.LJT where

open import Propositional.Implicational

-- Inference rules for the LJT system
-- (the T stands for Terminating)
data _⇒ₜ_ : Ctx → Form → Set where

  ax : ∀ {Γ A}
    → Γ , A ⇒ₜ A

  ⊃⇒ₜ¹ : ∀ {Γ A B G}
    → Γ , A , B     ⇒ₜ G
    → Γ , A ⊃ B , A ⇒ₜ G

  ⊃⇒ₜ² : ∀ {Γ B D C G}
    → Γ , B           ⇒ₜ G
    → Γ , D ⊃ B       ⇒ₜ C ⊃ D
    → Γ , (C ⊃ D) ⊃ B ⇒ₜ G

  ⇒ₜ⊃ : ∀ {Γ A B}
    → Γ , A ⇒ₜ B
    → Γ     ⇒ₜ A ⊃ B

  ⊥⇒ₜ : ∀ {Γ G}
    → Γ , ⊥' ⇒ₜ G

-- Postulating the exchange
-- structural rule.
postulate
  xch : ∀ {Γ Δ G}
    → Γ ~ Δ
    → Γ ⇒ₜ G
    → Δ ⇒ₜ G

-- Operators precedence.
infix 4 _⇒ₜ_
