module Propositional.Lemmas where

open import Propositional.Syntax

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (_,_)
open import Function hiding (_∋_)

-- Equality inversion lemmas.
≡-=>-inv : ∀ {t1 t2 t1' t2'} → (t1 ⊃ t2) ≡ (t1' ⊃ t2') → t1 ≡ t1' × t2 ≡ t2'
≡-=>-inv refl = refl Data.Product., refl

≡-∧-inv : ∀ {t1 t2 t1' t2'} → (t1 ∧ t2) ≡ (t1' ∧ t2') → t1 ≡ t1' × t2 ≡ t2'
≡-∧-inv refl = refl Data.Product., refl

≡-∨-inv : ∀ {t1 t2 t1' t2'} → (t1 ∨ t2) ≡ (t1' ∨ t2') → t1 ≡ t1' × t2 ≡ t2'
≡-∨-inv refl = refl Data.Product., refl

-- Equality is decidable for Form.
_≟F_ : ∀ (t t' : Form) → Dec (t ≡ t')
⊤ ≟F ⊤ = yes refl
⊤ ≟F (t' ⊃ t'') = no (λ ())
⊤ ≟F (t' ∧ t'') = no (λ ())
⊤ ≟F (t' ∨ t'') = no (λ ())
⊤ ≟F ⊥' = no (λ ())
(t ⊃ t₁) ≟F ⊤ = no (λ ())
(t ⊃ t₁) ≟F (t' ⊃ t'') with t ≟F t' | t₁ ≟F t''
((t ⊃ t₁) ≟F (t' ⊃ t'')) | no ¬p | q = no (¬p ∘ proj₁ ∘ ≡-=>-inv)
((t ⊃ t₁) ≟F (t' ⊃ t'')) | yes p | no ¬p = no (¬p ∘ proj₂ ∘ ≡-=>-inv)
((t ⊃ t₁) ≟F (t' ⊃ t'')) | yes p | yes p₁ rewrite p | p₁ = yes refl
(t ⊃ t₁) ≟F (t' ∧ t'') = no (λ ())
(t ⊃ t₁) ≟F (t' ∨ t'') = no (λ ())
(t ⊃ t₁) ≟F ⊥' = no (λ ())
(t ∧ t₁) ≟F ⊤ = no (λ ())
(t ∧ t₁) ≟F (t' ⊃ t'') = no (λ ())
(t ∧ t₁) ≟F (t' ∧ t'') with t ≟F t' | t₁ ≟F t''
((t ∧ t₁) ≟F (t' ∧ t'')) | no ¬p | q = no (¬p ∘ proj₁ ∘ ≡-∧-inv)
((t ∧ t₁) ≟F (t' ∧ t'')) | yes p | no ¬p = no (¬p ∘ proj₂ ∘ ≡-∧-inv)
((t ∧ t₁) ≟F (t' ∧ t'')) | yes p | yes p₁ rewrite p | p₁ = yes refl
(t ∧ t₁) ≟F (t' ∨ t'') = no (λ ())
(t ∧ t₁) ≟F ⊥' = no (λ ())
(t ∨ t₁) ≟F ⊤ = no (λ ())
(t ∨ t₁) ≟F (t' ⊃ t'') = no (λ ())
(t ∨ t₁) ≟F (t' ∧ t'') = no (λ ())
(t ∨ t₁) ≟F (t' ∨ t'') with t ≟F t' | t₁ ≟F t''
((t ∨ t₁) ≟F (t' ∨ t'')) | no ¬p | q = no (¬p ∘ proj₁ ∘ ≡-∨-inv)
((t ∨ t₁) ≟F (t' ∨ t'')) | yes p | no ¬p = no (¬p ∘ proj₂ ∘ ≡-∨-inv)
((t ∨ t₁) ≟F (t' ∨ t'')) | yes p | yes p₁ rewrite p | p₁ = yes refl
(t ∨ t₁) ≟F ⊥' = no (λ ())
⊥' ≟F ⊤ = no (λ ())
⊥' ≟F (t' ⊃ t'') = no (λ ())
⊥' ≟F (t' ∧ t'') = no (λ ())
⊥' ≟F (t' ∨ t'') = no (λ ())
⊥' ≟F ⊥' = yes refl

-- Defining permutation.
data _~_ : Ctx → Ctx → Set where
  Done  : ∅ ~ ∅
  Skip  : ∀ {t Γ Γ'} → Γ ~ Γ' → (Γ , t) ~ (Γ' , t)
  Swap  : ∀ {t t' Γ} → (Γ , t , t') ~ (Γ , t' , t)
  Trans : ∀ {Γ Γ₁ Γ'} → Γ ~ Γ₁ → Γ₁ ~ Γ' → Γ ~ Γ'

-- Proving that permutation is an equivalence relation.
~-refl : ∀ {Γ} → Γ ~ Γ
~-refl {∅} = Done
~-refl {Γ , t} = Skip ~-refl

~-sym : ∀ {Γ Γ'} →  Γ ~ Γ' →  Γ' ~ Γ
~-sym Done = Done
~-sym (Skip prf) = Skip (~-sym prf)
~-sym Swap = Swap
~-sym (Trans prf prf₁)
   = Trans (~-sym prf₁) (~-sym prf)

~-trans : ∀ {Γ Γ₁ Γ'} →  Γ ~ Γ₁ →  Γ₁ ~ Γ' → Γ ~ Γ'
~-trans p1 p2 = Trans p1 p2

-- Proving that permutation preserves lookup.
~-lookup : ∀ {Γ Γ' t} → Γ ~ Γ' → Γ ∋ t → Γ' ∋ t
~-lookup (Skip perm) Z = Z
~-lookup (Skip perm) (S pl) = S ~-lookup perm pl
~-lookup Swap Z = S Z
~-lookup (Swap {t} {t'}) (S_ {Γ}{t1}.{t'} pl) with t1 ≟F t
~-lookup (Swap {t} {t'}) (S_ {.(_ , t)} {_} {.t'} Z) | no ¬p = Z
~-lookup (Swap {t} {t'}) (S_ {.(_ , t)} {_} {.t'} (S pl)) | no ¬p = S (S pl)
~-lookup (Swap {t} {t'}) (S_ {.(_ , t)} {_} {.t'} pl) | yes p rewrite p = Z
~-lookup (Trans perm perm₁) pl = ~-lookup perm₁ (~-lookup perm pl)
