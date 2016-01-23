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
open import nicolai.pseudotruncations.pointed-O-Sphere


module nicolai.pseudotruncations.LoopsAndSpheres where

{- We greatly benefit from Evan Cavallo's code - thank you! -}
open import homotopy.PtdAdjoint
open import homotopy.SuspAdjointLoop




isNull : ∀ {i j} {A : Type i} {B : Type j} (b : B) (f : A → B) → Type _
isNull {A = A} b f = (a : A) → f a == b


module null {i} {j} {Â : Ptd i} {B̂ : Ptd j} (ĝ : Â →̇ B̂) where

  A = fst Â
  a₀ = snd Â 
  B = fst B̂
  b₀ = snd B̂
  g = fst ĝ
  p = snd ĝ 

  -- derived isNull
  isNulld = (a : fst Â) → g a == b₀ 

  -- pointed isNull; we state it in the equivalence form (slightly easier to handle)
  isNull∙' = Σ ((a : A) → g a == b₀) λ pr → pr a₀ == p

  -- the 'real' pointed isNull
  isNull∙ = ĝ == ((λ _ → b₀) , idp)

  {- The two versions are equivalent -}
  isNull-equiv : isNull∙ ≃ isNull∙'
  isNull-equiv =
               ĝ == ((λ _ → b₀) , idp)
                 ≃⟨ (=Σ-eqv _ _) ⁻¹ ⟩
               =Σ ĝ ((λ _ → b₀) , idp)
                 ≃⟨ equiv-Σ' {A₀ = g == λ _ → b₀}
                             app=-equiv
                             (λ h → (p == idp [ (λ f → f a₀ == b₀) ↓ h ])
                                      ≃⟨ to-transp-equiv _ _ ⟩
                                    (transport (λ f → f a₀ == b₀) h p) == idp
                                      ≃⟨ coe-equiv
                                           (ap (λ x → x == idp)
                                               (trans-ap₁ (λ f → f a₀)
                                                          b₀ h p)) ⟩
                                    (! (app= h a₀) ∙ p) == idp
                                      ≃⟨ adhoc-=-eqv (app= h a₀) p ⟩
                                    (app= h a₀ == p)
                                      ≃∎) ⟩ 
               (Σ ((a : A) → g a == b₀) λ pr → pr a₀ == p)
                 ≃∎ 

-- Lemma 4.4: pointed and non-pointed 'nullness' are logically equivalent;
-- First, one direction:
  null-lequiv : isNulld → isNull∙'
  null-lequiv isnull = (λ a → isnull a ∙ ! (isnull a₀) ∙ p) , (
                 isnull a₀ ∙ ! (isnull a₀) ∙ p
                   =⟨ ! (∙-assoc (isnull a₀) _ _) ⟩
                 (isnull a₀ ∙ ! (isnull a₀)) ∙ p
                   =⟨ ap (λ t → t ∙ p) (!-inv-r (isnull a₀)) ⟩
                 p
                   ∎)

-- The other direction is very easy; we do it using the non-prime variant:
  null-lequiv-easy : isNull∙ → isNulld
  null-lequiv-easy isn = app= (ap fst isn)





-- uncomment this if you want to wait forever for typechecking...
-- Σ⊣Ω-unitCounit : CounitUnitAdjoint Σ⊣Ω.SuspFunctor Σ⊣Ω.LoopFunctor
Σ⊣Ω-unitCounit = Σ⊣Ω.adj

Σ⊣Ω-homset : ∀ {i} → HomAdjoint {i} {i} Σ⊣Ω.SuspFunctor Σ⊣Ω.LoopFunctor
Σ⊣Ω-homset = counit-unit-to-hom Σ⊣Ω-unitCounit

module hom-adjoint {i} (Â : Ptd i) (B̂ : Ptd i) where

  A = fst Â
  B = fst B̂
  a₀ = snd Â
  b₀ = snd B̂

  Φeq : (⊙Susp Â →̇ B̂) ≃ (Â →̇ ⊙Ω B̂)
  Φeq = HomAdjoint.eq Σ⊣Ω-homset Â B̂  

  {- This is Lemma 4.1 -}
  Φ : (⊙Susp Â →̇ B̂) → (Â →̇ ⊙Ω B̂)
  Φ = –> Φeq  

  Φ⁻¹ : (Â →̇ ⊙Ω B̂) → (⊙Susp Â →̇ B̂)
  Φ⁻¹ = <– Φeq
  

  open PtdFunctor
  open Σ⊣Ω
  open CounitUnitAdjoint

  {- Some lemmas which are easy on paper and thus not explicitly 
     mentioned in the paper. It still takes some effort to
     formalize them. -}
  module simplify where

    simpl-⊙ap : (⊙ap {X = obj SuspFunctor Â} ((λ _ → b₀) , idp))
                 ==
                ((λ _ → idp) , idp)
    simpl-⊙ap =  →̇-maps-to
                   ⊙ap ((λ _ → b₀) , idp)
                   ((λ _ → idp) , idp)
                   (λ= (λ _ → ap-cst b₀ _))

                   ((app= (λ= (λ _ → ap-cst b₀ _)) _) ∙ idp
                     =⟨ ∙-unit-r _ ⟩
                   app= (λ= (λ _ → ap-cst b₀ _)) _
                     =⟨ app=-β _ _ ⟩
                   ap-cst b₀ (idp {a = snd B̂}) 
                     =⟨ idp ⟩ --  !
                   idp
                     =⟨ idp ⟩ --  ! 
                   snd (⊙ap {X = obj SuspFunctor Â} ((λ _ → b₀) , idp))
                     ∎ )

    simpl-comp : ((λ (_ : Ω (⊙Susp Â)) → idp {a = b₀}) , idp)
                   ⊙∘ (⊙η Â)
                  ==
                 (λ _ → idp) , idp
    simpl-comp = pair= idp ((ap-cst idp (snd (⊙η Â))) ∙ᵣ idp)


  open simplify

  {- Lemma 4.2 -}
  Φ-is-pointed-map : Φ ((λ _ → b₀) , idp) == ((λ _ → idp) , idp)
  Φ-is-pointed-map = Φ ((λ _ → b₀) , idp)
                       =⟨ idp ⟩
                     (    arr LoopFunctor ((λ _ → b₀) , idp)
                      ⊙∘ (CounitUnitAdjoint.η adj Â))
                       =⟨ idp ⟩ 
                     (    (⊙ap {X = obj SuspFunctor Â} ((λ _ → b₀) , idp)
                      ⊙∘ (⊙η Â)))
                       =⟨ ap (λ f → f ⊙∘ (⊙η Â)) simpl-⊙ap ⟩
                     ((λ _ → idp) , idp) ⊙∘ (⊙η Â)
                       =⟨ simpl-comp ⟩ 
                     (λ _ → idp) , idp
                       ∎ 

-- fix i
module _ {i} where

  open hom-adjoint

  open HomAdjoint
  open null

  -- Lemma 4.3
  Φ-snd-nat : {Â B̂ Ĉ : Ptd i} (f : ⊙Susp Â →̇ B̂) (g : B̂ →̇ Ĉ)
              → Φ Â Ĉ (g ⊙∘ f) == ⊙ap g ⊙∘ Φ Â B̂ f
  Φ-snd-nat {Â} {B̂} {Ĉ} f g = ! (nat-cod Σ⊣Ω-homset Â {B̂} {Ĉ} g f)

  -- Lemma 4.4 is above (before 4.2).

  -- Lemma 4.5
  isnull-Φ : {Â B̂ : Ptd i} (g : ⊙Susp Â →̇ B̂) → (isNull∙ g) ≃ isNull∙ (Φ Â B̂ g)
  isnull-Φ {Â} {B̂} g =
    isNull∙ g
      ≃⟨ equiv-ap (Φeq Â B̂) _ _ ⟩
    (Φ Â B̂ g) == Φ Â B̂ ((λ _ → snd B̂) , idp)
      ≃⟨ coe-equiv
           {A = (Φ Â B̂ g) == Φ Â B̂ ((λ _ → snd B̂) , idp)}
           {B = (Φ Â B̂ g) == (λ _ → idp) , idp}
           (ap (λ q → (Φ Â B̂ g == q)) (Φ-is-pointed-map _ _ )) ⟩
    (Φ Â B̂ g) == (λ _ → idp) , idp
      ≃∎ 


  -- combination of 4.3 and 4.5
  combine-isnull-nat : {Â B̂ Ĉ : Ptd i} (f : ⊙Susp Â →̇ B̂) (g : B̂ →̇ Ĉ)
               → (isNull∙ (g ⊙∘ f)) ≃ (isNull∙ (⊙ap g ⊙∘ Φ Â B̂ f)) --   
  combine-isnull-nat {Â} {B̂} {Ĉ} f g = 
    isNull∙ (g ⊙∘ f)
      ≃⟨ isnull-Φ _ ⟩
    isNull∙ (Φ Â Ĉ (g ⊙∘ f))
      ≃⟨ coe-equiv (ap (λ q → isNull∙ q) (Φ-snd-nat f g)) ⟩
    isNull∙ (⊙ap g ⊙∘ Φ Â B̂ f)
      ≃∎

  combine-isnull-nat' : {Â B̂ Ĉ : Ptd i} (f : Â →̇ ⊙Ω B̂) (g : B̂ →̇ Ĉ)
               → (isNull∙ (g ⊙∘ (Φ⁻¹ Â B̂ f))) ≃ (isNull∙ (⊙ap g ⊙∘ f))
  combine-isnull-nat' {Â} {B̂} {Ĉ} f g = 
   isNull∙ (g ⊙∘ (Φ⁻¹ Â B̂ f))
      ≃⟨ combine-isnull-nat (Φ⁻¹ Â B̂ f) g ⟩
    isNull∙ (⊙ap g ⊙∘ (Φ Â B̂ (Φ⁻¹ Â B̂ f)))
      ≃⟨ coe-equiv (ap (λ h → isNull∙ (⊙ap g ⊙∘ h)) (<–-inv-r (Φeq Â B̂) f)) ⟩
    isNull∙ (⊙ap g ⊙∘ f)
      ≃∎ 
    
  


module _ {i} where

  open hom-adjoint

  -- This was tricky (todo: could explain why)
  Φ-iter : (Â B̂ : Ptd i) (n : Nat)
           → ((⊙Susp-iter' n Â) →̇ B̂)
           → (Â →̇ (⊙Ω^ n B̂))
  Φ-iter Â B̂ O f = f
  Φ-iter Â B̂ (S n) f = Φ Â (⊙Ω^ n B̂) (Φ-iter (⊙Susp Â) B̂ n f)

  Φ-iter-equiv : (Â B̂ : Ptd i) (n : Nat) → is-equiv (Φ-iter Â B̂ n)
  Φ-iter-equiv Â B̂ O = snd (ide _)
  Φ-iter-equiv Â B̂ (S n) =
    snd ((Φeq Â (⊙Ω^ n B̂)) ∘e ((Φ-iter (⊙Susp Â) B̂ n) , Φ-iter-equiv (⊙Susp Â) B̂ n) )



module _ {i} where

  open null
  open hom-adjoint
  
  -- Lemma 4.7 -- generalized, because we need to do it for Susp first before it works for Sphere!
  isNull-Φ-many : (m : Nat)
                  → (Â B̂ Ĉ : Ptd i)
                  → (f : ⊙Susp-iter' m Â →̇ B̂) (g : B̂ →̇ Ĉ)
                  → isNull∙ (g ⊙∘ f)
                    ≃
                    isNull∙ ((ap^ m g) ⊙∘ Φ-iter Â B̂ m f)
  isNull-Φ-many O Â B̂ Ĉ f g = ide _
  isNull-Φ-many (S m) Â B̂ Ĉ f g = 
                    isNull∙ (g ⊙∘ f)
                      ≃⟨ isNull-Φ-many m (⊙Susp Â) B̂ Ĉ f g   ⟩
                    isNull∙ ((ap^ m g) ⊙∘ Φ-iter (⊙Susp Â) B̂ m f)
                      ≃⟨ combine-isnull-nat (Φ-iter (⊙Susp Â) B̂ m f) (ap^ m g) ⟩
                    (isNull∙
                      (⊙ap (ap^ m g) ⊙∘
                        Φ Â (⊙Ω^ m B̂)
                          (Φ-iter (⊙Susp Â) B̂ m f)))
                      ≃∎

  -- Lemma 4.7 (special with k = 0)
  module _ {B̂ Ĉ : Ptd i} (m : Nat)
           (f : ⊙Sphere' {i} m →̇ B̂) (g : B̂ →̇ Ĉ) where

    isNull-Φ-Sphere : isNull∙ (g ⊙∘ f)
                      ≃
                      isNull∙ ((ap^ m g) ⊙∘ Φ-iter (⊙Sphere' {i} O) B̂ m f)
    isNull-Φ-Sphere = isNull-Φ-many m _ _ _ f g


  open bool-neutral
  
  module _ {B̂ Ĉ : Ptd i} (m : Nat)
           (g : B̂ →̇ Ĉ) where

    c₀ = snd (⊙Ω^ m Ĉ)


    {- Lemma 4.8 -}
    null-on-pspaces :
      ((f : (⊙Sphere' {i} m) →̇ B̂) → isNull∙ (g ⊙∘ f))
      ≃
      isNulld (ap^ m g)
      
    null-on-pspaces = -- {!equiv-Π-l!}

      ((f : (⊙Sphere' {i} m) →̇ B̂) → isNull∙ (g ⊙∘ f))

        ≃⟨ equiv-Π-r (λ f → isNull-Φ-Sphere m f g) ⟩

      ((f : (⊙Sphere' {i} m) →̇ B̂) → isNull∙ ((ap^ m g) ⊙∘ Φ-iter (⊙Sphere' {i} O) B̂ m f))

        ≃⟨ equiv-Π-l
             {A = (⊙Sphere' {i} m) →̇ B̂}
             {B = (⊙Sphere' {i} O) →̇ (⊙Ω^ m B̂)}
             (λ f' → isNull∙ ((ap^ m g) ⊙∘ f'))
             {h = Φ-iter (⊙Sphere' {i} O) B̂ m}
             (Φ-iter-equiv _ _ m)
              ⟩

      ((f' : (⊙Sphere' {i} O) →̇ (⊙Ω^ m B̂)) → isNull∙ ((ap^ m g) ⊙∘ f'))

        ≃⟨ equiv-Π-r {A = ⊙Sphere' {i} O →̇ (⊙Ω^ m B̂)} (λ _ → isNull-equiv _) ⟩

      ((f' : (⊙Sphere' {i} O) →̇ (⊙Ω^ m B̂)) → isNull∙' ((ap^ m g) ⊙∘ f'))
      
        ≃⟨ ide _ ⟩ 

      ((f' : (⊙Sphere' {i} O) →̇ (⊙Ω^ m B̂)) → Σ ((x : bool) → fst ((ap^ m g) ⊙∘ f') x == _) λ h → h tt₀ == _)
      
        ≃⟨ equiv-Π-r {A = ⊙Sphere' {i} O →̇ (⊙Ω^ m B̂)}
                     (λ fp → reduction (λ b → fst (ap^ m g ⊙∘ fp) b == null.b₀ (ap^ m g ⊙∘ fp)) _) ⟩ 

      ((f' : (⊙Sphere' {i} O) →̇ (⊙Ω^ m B̂)) → fst ((ap^ m g) ⊙∘ f') ff₀ == _)

        ≃⟨ ide _ ⟩ 

      ((f' : (⊙Sphere' {i} O) →̇ (⊙Ω^ m B̂)) → fst (ap^ m g) (fst f' ff₀) == _)

        ≃⟨ equiv-Π-l {A = (⊙Sphere' {i} O) →̇ (⊙Ω^ m B̂)}
                     {B = fst (⊙Ω^ m B̂)}
                     _
                     (snd (reduction (λ _ → fst (⊙Ω^ m B̂)) _)) ⟩ 

      ((x : fst (⊙Ω^ m B̂)) → fst (ap^ m g) x == c₀)

        ≃⟨ ide _ ⟩ 

      isNulld (ap^ m g)
        ≃∎


