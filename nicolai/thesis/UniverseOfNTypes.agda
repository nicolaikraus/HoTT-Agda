{-# OPTIONS --without-K #-}

{- The type of all types in some universe with a fixed truncation level
   behaves like a universe itself. In this utility module, we develop
   some notation for efficiently working with this pseudo-universe.
   It will lead to considerably briefer and more comprehensible proofs. -}
module UniverseOfNTypes where

open import lib.Basics hiding (_⊔_)
open import lib.NType2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Unit

open import Preliminaries


module _ {n : ℕ₋₂} where
  ⟦_⟧ : ∀ {i} → n -Type i → Type i
  ⟦ (B , _) ⟧ = B

module _ {n : ℕ₋₂} where
  Lift-≤ : ∀ {i j} → n -Type i → n -Type (i ⊔ j)
  Lift-≤ {i} {j} (A , h) = (Lift {j = j} A , equiv-preserves-level (lift-equiv ⁻¹) h)

  raise : ∀ {i} → n -Type i → S n -Type i
  raise (A , h) = (A , raise-level n h)

  raise-≤T : ∀ {i} {m n : ℕ₋₂} → m ≤T n → m -Type i → n -Type i
  raise-≤T p (A , h) = (A , raise-level-≤T p h)

  ⊤-≤ : n -Type lzero
  ⊤-≤ = (⊤ , raise-level-≤T (-2≤T n) Unit-is-contr)

  Π-≤ : ∀ {i j} (A : Type i) → (A → n -Type j) → n -Type (i ⊔ j)
  Π-≤ A B = (Π A (fst ∘ B) , Π-level (snd ∘ B))

  infixr 2 _→-≤_

  _→-≤_ : ∀ {i j} → Type i → n -Type j → n -Type (i ⊔ j)
  A →-≤ B = Π-≤ A (λ _ → B)

  Σ-≤ : ∀ {i j} (A : n -Type i) → (⟦ A ⟧ → n -Type j) → n -Type (i ⊔ j)
  Σ-≤ A B = (Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧) , Σ-level (snd A) (snd ∘ B))

  infixr 4 _×-≤_

  _×-≤_ : ∀ {i j} → n -Type i → n -Type j → n -Type (i ⊔ j)
  A ×-≤ B = Σ-≤ A (λ _ → B)

  Path-< : ∀ {i} (A : S n -Type i) (x y : ⟦ A ⟧) → n -Type i
  Path-< A x y = ((x == y) , snd A _ _)

  Path-≤ : ∀ {i} (A : n -Type i) (x y : ⟦ A ⟧) → n -Type i
  Path-≤ A x y = Path-< (raise A) x y

  _≃-≤_ : ∀ {i j} (A : n -Type i) (B : n -Type j) → n -Type (i ⊔ j)
  A ≃-≤ B = ((⟦ A ⟧ ≃ ⟦ B ⟧) , (≃-level (snd A) (snd B)))

_-Type-≤_ : (n : ℕ₋₂) (i : ULevel) → S n -Type lsucc i
n -Type-≤ i = ((n -Type i) , (n -Type-level i))
