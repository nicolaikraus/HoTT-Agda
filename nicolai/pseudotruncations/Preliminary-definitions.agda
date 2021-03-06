{-# OPTIONS --without-K #-}





open import lib.Basics
-- open import lib.NType2
-- open import lib.PathGroupoid

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

{- Also trivial: make pointed equivalences from an ordinary equality -}
coe-equiv∙ : ∀ {i} {Â B̂ : Ptd i} → (Â == B̂) → Â ⊙≃ B̂
coe-equiv∙ idp = (idf _ , idp) , idf-is-equiv _

module _ {i} where

  {- Of course, spheres are defined in the library.
     Unfortunately, they do not play well together with iterated suspension.
     If f is an endofunction, one can define [f^Sn] either as [f^n ∘ f] or as
     [f ∘ f^n]. It turns out that it is much more convenient if one chooses
     different possibilites for Ω and for Σ (suspension), as the adjunction 
     can then be handled much more directly.
     In summary: It's best to redefine spheres. -}
  
  ⊙Susp-iter' : (n : ℕ) (Â : Ptd i) → Ptd i
  ⊙Susp-iter' O Â = Â
  ⊙Susp-iter' (S n) Â = ⊙Susp-iter' n (⊙Susp Â)

  {- compare: definition of iterated Ω
    ⊙Ω-iter : (n : ℕ) (Â : Ptd i) → Ptd i
    ⊙Ω-iter O Â = Â
    ⊙Ω-iter (S n) Â = ⊙Ω (⊙Ω-iter n Â)
  -}

  ⊙Sphere' : (n : ℕ) → Ptd i
  ⊙Sphere' n = ⊙Susp-iter' n (⊙Lift ⊙Bool) 

  Sphere' : (n : ℕ) → Type i
  Sphere' = fst ∘ ⊙Sphere' 

  nor' : (n : ℕ) → Sphere' n
  nor' = snd ∘ ⊙Sphere'

  {- Unfortunately, we will sometimes still need the "other" behaviour of the sphere.
     Thus, we show at least the following: -}

  ⊙Susp-iter : (n : ℕ) (Â : Ptd i) → Ptd i
  ⊙Susp-iter O Â = Â
  ⊙Susp-iter (S n) Â = ⊙Susp (⊙Susp-iter n Â)

  ⊙Sphere* : (n : ℕ) → Ptd i
  ⊙Sphere* n = ⊙Susp-iter n (⊙Lift ⊙Bool)

  Sphere* : (n : ℕ) → Type i
  Sphere* = fst ∘ ⊙Sphere*

  {- Of course, this proof could be done for all endofunctions. -}
  susp-iter= : (n : ℕ) (Â : Ptd i) → ⊙Susp-iter' n Â == ⊙Susp-iter n Â
  susp-iter= O Â = idp 
  susp-iter= (S O) Â = idp 
  susp-iter= (S (S n)) Â = 
    ⊙Susp-iter' (S (S n)) Â
      =⟨ susp-iter= (S n) (⊙Susp Â) ⟩
    ⊙Susp (⊙Susp-iter n (⊙Susp Â))
      =⟨ ap ⊙Susp (! (susp-iter= n (⊙Susp Â))) ⟩
    ⊙Susp (⊙Susp-iter' (S n) Â)
      =⟨ ap ⊙Susp (susp-iter= (S n) Â) ⟩
    ⊙Susp-iter (S (S n)) Â
      ∎

  {- Thus, we have for the spheres: -}
  ⊙Spheres= : (n : ℕ) → ⊙Sphere' n == ⊙Sphere* n
  ⊙Spheres= n = susp-iter= n (⊙Lift ⊙Bool)

  Spheres= : (n : ℕ) → Sphere' n == Sphere* n
  Spheres= n = ap fst (⊙Spheres= n)

  {- Also, we have this: -}
  susp'-switch : (n : ℕ) → ⊙Sphere' (S n) == ⊙Susp (⊙Sphere' n)
  susp'-switch n = (⊙Spheres= (S n)) ∙ (ap ⊙Susp (! (⊙Spheres= n))) 
