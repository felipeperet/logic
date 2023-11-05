module Propositional.Systems.Natural.Properties.Soundness where

open import Propositional.Systems.Natural.NJ
open import Propositional.Systems.Natural.Bidirectional

open import Data.Product hiding (_,_)

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
