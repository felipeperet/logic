module Propositional.Natural.Properties.Completeness where

open import Propositional.Syntax
open import Propositional.Natural.NJ
open import Propositional.Natural.Bidirectional

open import Data.Product hiding (_,_)

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
