module Propositional.Sequent.LJT where

open import Propositional.Implicational

-- Inference rules for the LJT system
-- (the T stands for Terminating)
data _⇒_ : Ctx → Form → Set where

  ax : ∀ {Γ A}
    → Γ , A ⇒ A

  ⊃⇒¹ : ∀ {Γ A B G}
    → Γ , A , B     ⇒ G
    → Γ , A ⊃ B , A ⇒ G

  ⊃⇒² : ∀ {Γ B D C G}
    → Γ , B           ⇒ G
    → Γ , D ⊃ B       ⇒ C ⊃ D
    → Γ , (C ⊃ D) ⊃ B ⇒ G

  ⇒⊃ : ∀ {Γ A B}
    → Γ , A ⇒ B
    → Γ     ⇒ A ⊃ B

  ⊥⇒ : ∀ {Γ G}
    → Γ , ⊥' ⇒ G

-- Postulating the exchange
-- structural rule.
postulate
  xch : ∀ {Γ Δ G}
    → Γ ~ Δ
    → Γ ⇒ G
    → Δ ⇒ G

-- Operators precedence.
infix 4 _⇒_
