module Propositional.Natural.Bidirectional where

open import Propositional.Syntax

-- Normal natural deduction inference rules
-- (bi-directional natural deduction without coercion)
data _⊢_↓ : Ctx → Form → Set
data _⊢_↑ : Ctx → Form → Set

data _⊢_↓ where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A ↓

  _∙_  : ∀ {Γ A B}
    → Γ ⊢ A ⊃ B ↑
    → Γ ⊢ A ↑
    → Γ ⊢ B ↓

  fst_ : ∀ {Γ A B}
    → Γ ⊢ A ∧ B ↓
    → Γ ⊢ A ↓

  snd_ : ∀ {Γ A B}
    → Γ ⊢ A ∧ B ↓
    → Γ ⊢ B ↓

data _⊢_↑ where

  case_of_∣_ : ∀ {Γ A B C}
    → Γ ⊢ A ∨ B ↓
    → Γ , A ⊢ C ↑
    → Γ , B ⊢ C ↑
    → Γ ⊢ C ↑

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B ↑
    → Γ ⊢ A ⊃ B ↑

  ⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A ↑
    → Γ ⊢ B ↑
    → Γ ⊢ A ∧ B ↑

  inl_ : ∀ {Γ A B}
    → Γ ⊢ A ↑
    → Γ ⊢ A ∨ B ↑

  inr_ : ∀ {Γ A B}
    → Γ ⊢ B ↑
    → Γ ⊢ A ∨ B ↑

  ⊤-intro : ∀ {Γ}
    → Γ ⊢ ⊤ ↑

  ⊥-elim : ∀ {Γ C}
    → Γ , ⊥' ⊢ C ↑

  ↓↑ : ∀ {Γ A}
    → Γ ⊢ A ↓
    → Γ ⊢ A ↑

-- Extended bi-directional natural deduction inference rules
-- (bi-directional natural deduction with coercion)
data _⊢⁺_↓ : Ctx → Form → Set
data _⊢⁺_↑ : Ctx → Form → Set

data _⊢⁺_↓ where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢⁺ A ↓

  _∙_  : ∀ {Γ A B}
    → Γ ⊢⁺ A ⊃ B ↓
    → Γ ⊢⁺ A ↑
    → Γ ⊢⁺ B ↓

  fst_ : ∀ {Γ A B}
    → Γ ⊢⁺ A ∧ B ↓
    → Γ ⊢⁺ A ↓

  snd_ : ∀ {Γ A B}
     → Γ ⊢⁺ A ∧ B ↓
     → Γ ⊢⁺ B ↓

  ↑↓ : ∀ {Γ A}
    → Γ ⊢⁺ A ↑
    → Γ ⊢⁺ A ↓

data _⊢⁺_↑ where

  case_of_∣_ : ∀ {Γ A B C}
    → Γ ⊢⁺ A ∨ B ↓
    → Γ , A ⊢⁺ C ↑
    → Γ , B ⊢⁺ C ↑
    → Γ ⊢⁺ C ↑

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢⁺ B ↑
    → Γ ⊢⁺ A ⊃ B ↑

  ⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢⁺ A ↑
    → Γ ⊢⁺ B ↑
    → Γ ⊢⁺ A ∧ B ↑

  inl_ : ∀ {Γ A B}
    → Γ ⊢⁺ A ↑
    → Γ ⊢⁺ A ∨ B ↑

  inr_ : ∀ {Γ A B}
    → Γ ⊢⁺ B ↑
    → Γ ⊢⁺ A ∨ B ↑

  ⊤-intro : ∀ {Γ}
    → Γ ⊢⁺ ⊤ ↑

  ⊥-elim : ∀ {Γ C}
    → Γ , ⊥' ⊢⁺ C ↑

  ↓↑ : ∀ {Γ A}
    → Γ ⊢⁺ A ↓
    → Γ ⊢⁺ A ↑

-- Operators precedence.
infix  4 _⊢_↓
infix  4 _⊢_↑
infix  4 _⊢⁺_↓
infix  4 _⊢⁺_↑
