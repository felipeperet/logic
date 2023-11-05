module Propositional.Systems.Natural.NJ where

open import Propositional.Syntax

-- Natural Deduction inference rules.
data _⊢_ : Ctx → Form → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⊃ B

  _∙_ : ∀ {Γ A B}
    → Γ ⊢ A ⊃ B
    → Γ ⊢ A
    → Γ ⊢ B

  ⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
    → Γ ⊢ A ∧ B

  fst_ : ∀ {Γ A B}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A

  snd_ : ∀ {Γ A B}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B

  inl_ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ A ∨ B

  inr_ : ∀ {Γ A B}
    → Γ ⊢ B
    → Γ ⊢ A ∨ B

  case_of_∣_ : ∀ {Γ A B C}
    → Γ ⊢ A ∨ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
    → Γ ⊢ C

  T-intro : ∀ {Γ}
    → Γ ⊢ ⊤

  ⊥-elim : ∀ {Γ C}
    → Γ , ⊥' ⊢ C

-- Operators precedence.
infix  4 _⊢_
