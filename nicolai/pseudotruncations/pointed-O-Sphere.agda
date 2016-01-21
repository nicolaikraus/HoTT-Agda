{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.PathGroupoid

open import lib.types.Bool
open import lib.types.IteratedSuspension
open import lib.types.Lift
open import lib.types.LoopSpace
open import lib.types.Nat
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.Suspension
open import lib.types.TLevel
open import lib.types.Unit

open SuspensionRec public using () renaming (f to Susp-rec)

open import nicolai.pseudotruncations.Preliminary-definitions
open import nicolai.pseudotruncations.Liblemmas

module nicolai.pseudotruncations.pointed-O-Sphere where


{- helper file for some technical things -}


module _ {i} where

  bool = fst (⊙Sphere {i} O)
  tt₀ : bool
  tt₀ = snd (⊙Sphere {i} O)
  ff₀ : bool
  ff₀ = lift false


module bool-neutral
           {i j}
           (P : bool {i} → Type j)
           (p₀ : P tt₀) where

  bool-pair : (P tt₀ × P ff₀) ≃ ((b : bool) → P b)
  bool-pair = equiv (λ tf → (λ { (lift true) → fst tf ; (lift false) → snd tf }))
                    (λ f → (f tt₀ , f ff₀))
                    (λ f → λ= (λ { (lift true) → idp ; (lift false) → idp }))
                    (λ tf → idp)

  pair-red : Σ (P tt₀ × P ff₀) (λ tf → fst tf == p₀) → P ff₀
  pair-red ((pt , pf) , q) = pf

  sing-exp : P ff₀ → Σ (P tt₀ × P ff₀) (λ tf → fst tf == p₀)
  sing-exp pf = ((p₀ , pf) , idp)

  red-exp : (pf : P ff₀) → pair-red (sing-exp pf) == pf
  red-exp _ = idp

  exp-red : (x : Σ (P tt₀ × P ff₀) (λ tf → fst tf == p₀)) → sing-exp (pair-red x) == x
  exp-red ((.p₀ , pf) , idp) = idp
  {- I tried to do it with pattern matching, but this does not introduce 
     a dot [.] before [p₀]. Thus, is fails. Is this a bug? -}

  pair-one-determined : Σ (P tt₀ × P ff₀) (λ tf → fst tf == p₀) ≃ P ff₀
  pair-one-determined = equiv pair-red sing-exp red-exp exp-red


  {- This reduction result is (on paper) trivial, but for our formalization
     quite powerful! -}
  reduction : (Σ ((b : bool) → P b) λ g → g tt₀ == p₀)   ≃   P ff₀
  reduction = (Σ ((b : bool) → P b) λ g → g tt₀ == p₀)
                 ≃⟨ equiv-Σ-fst {A = P tt₀ × P ff₀}
                                {B = (b : bool) → P b}
                                (λ g → g tt₀ == p₀)
                                {h = fst bool-pair}
                                (snd bool-pair) ⁻¹ ⟩
               Σ (P tt₀ × P ff₀) ((λ g → g tt₀ == p₀) ∘ fst bool-pair)
                 ≃⟨ ide _ ⟩
               Σ (P tt₀ × P ff₀) (λ tf → fst tf == p₀)
                 ≃⟨ pair-one-determined ⟩
               P ff₀ 
                 ≃∎

