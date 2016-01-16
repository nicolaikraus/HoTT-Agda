{-# OPTIONS --without-K #-}

open import lib.Basics -- hiding (_=⟨_⟩_ ; _∎)
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.NType2
open import lib.PathGroupoid
open import lib.types.Pointed

open import lib.types.Suspension
open import lib.types.LoopSpace

open SuspensionRec public using () renaming (f to Susp-rec)

module nicolai.pseudotruncations.LoopsAndSpheres where

open import homotopy.PtdAdjoint
open import homotopy.SuspAdjointLoop


_→̇_ : ∀ {i j} (Â : Ptd i) (B̂ : Ptd j) → Type _
Â →̇ B̂ = fst (Â ⊙→ B̂)


-- fortunately, we have the following in the library -- thanks ecavallo!  

-- uncomment this if you want to wait forever for typechecking...
-- Σ⊣Ω-unitCounit : CounitUnitAdjoint Σ⊣Ω.SuspFunctor Σ⊣Ω.LoopFunctor
Σ⊣Ω-unitCounit = Σ⊣Ω.adj

Σ⊣Ω-homset : ∀ {i} → HomAdjoint {i} {i} Σ⊣Ω.SuspFunctor Σ⊣Ω.LoopFunctor
Σ⊣Ω-homset = counit-unit-to-hom Σ⊣Ω-unitCounit


-- _→ₚ_ : ∀ {i j} (Â : Ptd i) (B̂ : Ptd j) → Type _
-- Â →ₚ B̂ = fst (Â ⊙→ B̂) 

isNull : ∀ {i j} {A : Type i} {B : Type j} (b : B) (f : A → B) → Type _
isNull {A = A} b f = (a : A) → f a == b

isNulld : ∀ {i j} {Â : Ptd i} {B̂ : Ptd j} (g : Â →̇ B̂) → Type _
isNulld {Â = Â} {B̂ = B̂} g = (a : fst Â) → fst g a == snd B̂


module hom-adjoint {i} {Â : Ptd i} {B̂ : Ptd i} where

  A = fst Â
  B = fst B̂
  a₀ = snd Â
  b₀ = snd B̂

  Φeq : (⊙Susp Â →̇ B̂) ≃ (Â →̇ ⊙Ω B̂)
  Φeq = HomAdjoint.eq Σ⊣Ω-homset Â B̂  

  Φ : (⊙Susp Â →̇ B̂) → (Â →̇ ⊙Ω B̂)
  Φ = –> Φeq  



  Φ-pres-isNull : (p : _) (a : A)
                  → (fst (Φ ((λ _ → b₀) , p)) a) == idp
  Φ-pres-isNull p a = 
    (fst (Φ ((λ _ → b₀) , p)) a)
      =⟨ idp ⟩
    ! p ∙ (ap (λ _ → b₀) _) ∙' p
      =⟨ ap (λ x → ! p ∙ x ∙' p) (ap-cst b₀ _) ⟩
    ! p ∙ idp ∙' p
      =⟨ ap (λ x → ! p ∙ x) (∙'-unit-l p) ⟩ 
    ! p ∙ p
      =⟨ !-inv-l p ⟩ 
    idp {a = b₀}
      ∎

-- TODO is this true more generally? I.e. for any adjoint pair?
--  Φ-pres-isNull-equiv : (f : ⊙Susp Â →̇ B̂)



