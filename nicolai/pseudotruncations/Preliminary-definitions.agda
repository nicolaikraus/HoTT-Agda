{-# OPTIONS --without-K #-}

open import lib.Basics -- hiding (_=⟨_⟩_ ; _∎)
open import lib.types.Bool
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.Lift
open import lib.types.TLevel
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.NType2
open import lib.PathGroupoid
open import lib.types.Suspension

module nicolai.pseudotruncations.Preliminary-definitions where

-- definition of weak constancy
wconst : ∀ {i j} {A : Type i} {B : Type j} → (A → B) → Type (lmax i j)
wconst {A = A} f = (a₁ a₂ : A) → f a₁ == f a₂ 


{- Pointed maps (without the 'point') -}
_→̇_ : ∀ {i j} (Â : Ptd i) (B̂ : Ptd j) → Type _
Â →̇ B̂ = fst (Â ⊙→ B̂)



{- It is useful to have a lemma which allows to construct equalities
   between pointed types. Of course, we know that such an equality
   is a pair of equalities; however, transporting a function can 
   make things more tedious than necessary! -}
make-=-∙ : ∀ {i j} {Â : Ptd i} {B̂ : Ptd j} (f̂ ĝ : Â →̇ B̂)
           (p : fst f̂ == fst ĝ)
           → ! (app= p (snd Â)) ∙ snd f̂ == snd ĝ
           → f̂ == ĝ
make-=-∙ (f , p) (.f , q) idp t = pair= idp t


{- A lemma that allows to prove that the value of a map between 
   pointed maps, at some given point, is some given point.
   This would otherwise be an involved nesting of transports/
   PathOvers. -}
→̇-maps-to : ∀ {i} {Â B̂ Ĉ D̂ : Ptd i} (F̂ : (Â →̇ B̂) → (Ĉ →̇ D̂))
              (f̂ : Â →̇ B̂) (ĝ : Ĉ →̇ D̂)
              (p : fst (F̂ f̂) == (fst ĝ))
              (q : (app= p (snd Ĉ)) ∙ (snd ĝ) == snd (F̂ f̂)) 
              → F̂ f̂ == ĝ
→̇-maps-to F̂ f̂ (.(fst (F̂ f̂)) , .(snd (F̂ f̂))) idp idp = idp


module _ {i} where

{- Of course, spheres are defined in the library.
   Unfortunately, they do not play well together with iterated suspension.
   If f is an endofunction, one can define [f^Sn] either as [f^n ∘ f] or as
   [f ∘ f^n]. It turns out that it is much more convenient if one chooses
   different possibilites for Ω and for Σ (suspension), as the adjunction 
   can then be handled much more directly.
   In summary: It's best to redefine spheres. -}
  
  ⊙Susp-iter : (n : Nat) (Â : Ptd i) → Ptd i
  ⊙Susp-iter O Â = Â
  ⊙Susp-iter (S n) Â = ⊙Susp-iter n (⊙Susp Â)

{- compare: definition of iterated Ω
  ⊙Ω-iter : (n : Nat) (Â : Ptd i) → Ptd i
  ⊙Ω-iter O Â = Â
  ⊙Ω-iter (S n) Â = ⊙Ω (⊙Ω-iter n Â)
-}

  ⊙Sphere' : (n : Nat) → Ptd i
  ⊙Sphere' n = ⊙Susp-iter n (⊙Lift ⊙Bool) 

  Sphere' : (n : Nat) → Type i
  Sphere' = fst ∘ ⊙Sphere' 

  nor' : (n : Nat) → Sphere' n
  nor' = snd ∘ ⊙Sphere'


