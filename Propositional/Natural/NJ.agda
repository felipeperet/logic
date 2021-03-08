module Propositional.Natural.NJ where

open import Propositional.Syntax

open import Data.Product hiding (_,_)

-- Natural Deduction inference rules.
data _⊢_ : Ctx → Form → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
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

-- Proving that bi-directional natural deduction without coercion
-- is sound with respect to the original natural deduction system.
mutual
  ⊢↓-sound : ∀ {Γ C}
    → Γ ⊢ C ↓
    → Γ ⊢ C
  ⊢↓-sound (` x)   = ` x
  ⊢↓-sound (D ∙ x) = ⊢↑-sound D ∙ ⊢↑-sound x
  ⊢↓-sound (fst D) = fst ⊢↓-sound D
  ⊢↓-sound (snd D) = snd ⊢↓-sound D

  ⊢↑-sound : ∀ {Γ C}
    → Γ ⊢ C ↑
    → Γ ⊢ C
  ⊢↑-sound (case x of D ∣ D₁) = case ⊢↓-sound x
   of ⊢↑-sound D ∣ ⊢↑-sound D₁
  ⊢↑-sound (ƛ D)              = ƛ ⊢↑-sound D
  ⊢↑-sound ⟨ D , D₁ ⟩         = ⟨ ⊢↑-sound D , ⊢↑-sound D₁ ⟩
  ⊢↑-sound (inl D)            = inl ⊢↑-sound D
  ⊢↑-sound (inr D)            = inr ⊢↑-sound D
  ⊢↑-sound ⊤-intro            = T-intro
  ⊢↑-sound ⊥-elim             = ⊥-elim
  ⊢↑-sound (↓↑ x)             = ⊢↓-sound x

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

-- Proving that bi-directional natural deduction system with coercion
-- is sound with respect to the original natural deduction system.
mutual
  ⊢⁺↓-sound : ∀ {Γ C}
    → Γ ⊢⁺ C ↓
    → Γ ⊢ C
  ⊢⁺↓-sound (` x)   = ` x
  ⊢⁺↓-sound (D ∙ x) = ⊢⁺↓-sound D ∙ ⊢⁺↑-sound x
  ⊢⁺↓-sound (fst D) = fst ⊢⁺↓-sound D
  ⊢⁺↓-sound (snd D) = snd ⊢⁺↓-sound D
  ⊢⁺↓-sound (↑↓ x)  = ⊢⁺↑-sound x

  ⊢⁺↑-sound : ∀ {Γ C}
    → Γ ⊢⁺ C ↑
    → Γ ⊢ C
  ⊢⁺↑-sound (case x of D ∣ D₁)  = case ⊢⁺↓-sound x
   of ⊢⁺↑-sound D ∣ ⊢⁺↑-sound D₁
  ⊢⁺↑-sound (ƛ D)               = ƛ ⊢⁺↑-sound D
  ⊢⁺↑-sound ⟨ D , D₁ ⟩          = ⟨ ⊢⁺↑-sound D , ⊢⁺↑-sound D₁ ⟩
  ⊢⁺↑-sound (inl D)             = inl ⊢⁺↑-sound D
  ⊢⁺↑-sound (inr D)             = inr ⊢⁺↑-sound D
  ⊢⁺↑-sound ⊤-intro             = T-intro
  ⊢⁺↑-sound ⊥-elim              = ⊥-elim
  ⊢⁺↑-sound (↓↑ x)              = ⊢⁺↓-sound x

-- Proving that bi-directional natural deduction with coercion
-- is complete with respect to the original natural deduction system.
⊢⁺-complete : ∀ {Γ A}
  → Γ ⊢ A
  → (Γ ⊢⁺ A ↓) × (Γ ⊢⁺ A ↑)
⊢⁺-complete (` x)    = (` x)
  Data.Product., ↓↑ (` x)
⊢⁺-complete (ƛ D)    = ↑↓ (ƛ ↓↑ (proj₁ (⊢⁺-complete D)))
  Data.Product., (ƛ ↓↑ (proj₁ (⊢⁺-complete D)))
⊢⁺-complete (D ∙ D₁) = (proj₁ (⊢⁺-complete D) ∙ proj₂ (⊢⁺-complete D₁))
  Data.Product., ↓↑ (proj₁ (⊢⁺-complete D) ∙ proj₂ (⊢⁺-complete D₁))
⊢⁺-complete ⟨ D , D₁ ⟩ = ↑↓ ⟨ proj₂ (⊢⁺-complete D) , proj₂ (⊢⁺-complete D₁) ⟩
  Data.Product., ⟨ proj₂ (⊢⁺-complete D) , proj₂ (⊢⁺-complete D₁) ⟩
⊢⁺-complete (fst D)  = (fst proj₁ (⊢⁺-complete D))
  Data.Product., ↓↑ (fst proj₁ (⊢⁺-complete D))
⊢⁺-complete (snd D)  = (snd proj₁ (⊢⁺-complete D))
  Data.Product., ↓↑ (snd proj₁ (⊢⁺-complete D))
⊢⁺-complete (inl D)  = ↑↓ (inl proj₂ (⊢⁺-complete D))
  Data.Product., (inl proj₂ (⊢⁺-complete D))
⊢⁺-complete (inr D)  = ↑↓ (inr proj₂ (⊢⁺-complete D))
  Data.Product., (inr proj₂ (⊢⁺-complete D))
⊢⁺-complete (case D of D₁ ∣ D₂) = ↑↓ (case proj₁ (⊢⁺-complete D) of ↓↑ (proj₁ (⊢⁺-complete D₁)) ∣
                                        ↓↑ (proj₁ (⊢⁺-complete D₂)))
  Data.Product., (case proj₁ (⊢⁺-complete D) of ↓↑ (proj₁ (⊢⁺-complete D₁)) ∣
                    ↓↑ (proj₁ (⊢⁺-complete D₂)))
⊢⁺-complete T-intro  = ↑↓ ⊤-intro Data.Product., ⊤-intro
⊢⁺-complete ⊥-elim   = ↑↓ ⊥-elim Data.Product., ⊥-elim

-- Operators precedence.
infix  4 _⊢_
infix  4 _⊢_↓
infix  4 _⊢_↑
infix  4 _⊢⁺_↓
infix  4 _⊢⁺_↑
