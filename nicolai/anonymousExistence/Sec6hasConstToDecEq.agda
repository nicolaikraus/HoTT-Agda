{-# OPTIONS --without-K #-}

open import library.Basics hiding (Type ; Σ)
open import library.types.Sigma
open import library.types.Bool

open import Sec2preliminaries 
open import Sec4hasConstToSplit

module Sec6hasConstToDecEq where

-- Lemma 6.1
hasConst-family-dec : {X : Type} → (x₁ x₂ : X) → ((x : X) → hasConst ((x₁ == x) + (x₂ == x))) → (x₁ == x₂) + ¬(x₁ == x₂)
hasConst-family-dec {X} x₁ x₂ hasConst-fam = solution where
  f₋ : (x : X) → (x₁ == x) + (x₂ == x) → (x₁ == x) + (x₂ == x)
  f₋ x = fst (hasConst-fam x)

  E₋ : X → Type
  E₋ x = fix (f₋ x)

  E : Type
  E = Σ X λ x → (E₋ x)

  E-fst-determines-eq : (e₁ e₂ : E) → (fst e₁ == fst e₂) → e₁ == e₂
  E-fst-determines-eq e₁ e₂ p = second-comp-triv (λ x → fixed-point (f₋ x) (snd (hasConst-fam x))) _ _ p

  r : Bool → E
  r true = x₁ , to-fix (f₋ x₁) (snd (hasConst-fam x₁)) (inl idp) 
  r false = x₂ , to-fix (f₋ x₂) (snd (hasConst-fam x₂)) (inr idp)

  about-r : (r true == r false) ↔ (x₁ == x₂)
  about-r = (λ p → ap fst p) , (λ p → E-fst-determines-eq _ _ p)

  s : E → Bool
  s (_ , inl _ , _) = true
  s (_ , inr _ , _) = false

  s-section-of-r : (e : E) → r(s e) == e
  s-section-of-r (x , inl p , q) = E-fst-determines-eq _ _ p
  s-section-of-r (x , inr p , q) = E-fst-determines-eq _ _ p

  about-s : (e₁ e₂ : E) → (s e₁ == s e₂) ↔ (e₁ == e₂)
  about-s e₁ e₂ = one , two where
    one : (s e₁ == s e₂) → (e₁ == e₂)
    one p = 
      e₁       =⟨ ! (s-section-of-r e₁) ⟩
      r(s(e₁)) =⟨ ap r p ⟩
      r(s(e₂)) =⟨ s-section-of-r e₂ ⟩
      e₂       ∎
    two : (e₁ == e₂) → (s e₁ == s e₂)
    two p = ap s p

  combine : (s (r true) == s (r false)) ↔ (x₁ == x₂)
  combine = (about-s _ _) ◎ about-r

  check-bool : (s (r true) == s (r false)) + ¬(s (r true) == s (r false))
  check-bool = Bool-has-dec-eq _ _

  solution : (x₁ == x₂) + ¬(x₁ == x₂)
  solution with check-bool 
  solution | inl p = inl (fst combine p)
  solution | inr np = inr (λ p → np (snd combine p))


-- Theorem 6.2
all-hasConst→dec-eq : ((X : Type) → hasConst X) → (X : Type) → has-dec-eq X
all-hasConst→dec-eq all-hasConst X x₁ x₂ = hasConst-family-dec x₁ x₂ (λ x → all-hasConst _)
