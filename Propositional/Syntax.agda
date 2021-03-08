module Propositional.Syntax where

open import Data.Nat

-- Syntax of formulae in Propositional Logic.
data Form : Set where
  ⊤    : Form
  _⊃_  : Form → Form → Form
  _∧_  : Form → Form → Form
  _∨_  : Form → Form → Form
  ⊥'   : Form

-- Defining the size of a formula.
form-size : Form → ℕ
form-size ⊤        = zero
form-size (D ⊃ D₁) = (suc zero) + (form-size D) + (form-size D₁)
form-size (D ∧ D₁) = (suc zero) + (form-size D) + (form-size D₁)
form-size (D ∨ D₁) = (suc zero) + (form-size D) + (form-size D₁)
form-size ⊥'       = zero

-- Defining context as a list of formulae.
data Ctx : Set where
  ∅    : Ctx
  _,_  : Ctx → Form → Ctx

-- Defining the size of a context.
ctx-size : Ctx → ℕ
ctx-size ∅       = zero
ctx-size (G , x) = (ctx-size G) + (form-size x)

-- Ctx membership proofs.
data _∋_ : Ctx → Form → Set where
  Z : ∀ {Γ A}    → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

-- Operators precedence.
infix  4 _∋_
infixl 5 _,_
infixr 6 _⊃_
infixr 7 _∧_
infixr 7 _∨_
