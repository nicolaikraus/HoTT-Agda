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


{- It is useful to have a lemma which allows to construct equalities
   between pointed types. Of course, we know that such an equality
   is a pair of equalities; however, transporting a function can 
   make things more tedious than necessary! -}
make-=-∙ : ∀ {i j} {Â : Ptd i} {B̂ : Ptd j} (f̂ ĝ : Â →̇ B̂)
           (p : fst f̂ == fst ĝ)
           → ! (app= p (snd Â)) ∙ snd f̂ == snd ĝ
           → f̂ == ĝ
make-=-∙ (f , p) (.f , q) idp t = pair= idp t



module _ {i} where

  bool = fst (⊙Sphere {i} O)
  tt₀ : bool
  tt₀ = snd (⊙Sphere {i} O)
  ff₀ : bool
  ff₀ = lift false

{-
  -- standard lemma
  from-bool : ∀ {j} (X : Type j) → X × X ≃ (bool → X) 
  from-bool X =
    equiv (λ x2 → λ { (lift true) → fst x2 ; (lift false) → snd x2 })
          (λ f → f tt₀ , f ff₀)
          (λ f → λ= (λ { (lift true) → idp ; (lift false) → idp }))
          (λ x2 → idp)
-}

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


{- THIS IS NOW A SPECIAL CASE (with P ≡ λ _ → X)
module triv-O-sphere {i : ULevel} {j} {D̂ : Ptd j} where
    D = fst D̂
    d₀ = snd D̂

    -- a bit more interesting: pointed maps from bool
    from-bool∙ : (Σ (D × D) λ d2 → fst d2 == d₀) ≃ (⊙Sphere {i} O →̇ D̂)
    from-bool∙ = equiv-Σ-fst
                   {A = D × D}
                   {B = bool → D}
                   (λ f → f tt₀ == d₀)
                   {h = fst (from-bool D)}
                   (snd (from-bool D))


    -- but we also have (would maybe be much easier to prove with a library lemma?):
    Σ-sngltn : (Σ (D × D) λ d2 → fst d2 == d₀) ≃ D
    Σ-sngltn = equiv (λ dx → snd (fst dx))
                     (λ d → (d₀ , d) , idp)
                     (λ d → idp)
                     (λ {((d₁ , d) , p)
                         → pair= (pair×= (! p) idp)
                                 (from-transp (λ d2 → fst d2 == d₀)
                                 (pair×= (! p) idp)
                                 ((transport (λ d2 → fst d2 == d₀) (pair×= (! p) idp) idp)
                                    =⟨ trans-ap₁ fst d₀ (pair×= (! p) idp) idp ⟩
                                  ! (ap (λ r → fst r) (pair×= (! p) idp)) ∙ idp
                                    =⟨ ap (λ q → ! q ∙ idp) (ap-fst (! p) idp) ⟩
                                  ! (! p) ∙ idp
                                    =⟨ ∙-unit-r _ ⟩
                                  ! (! p)
                                    =⟨ !-! p ⟩
                                  p
                                    ∎))})

    -- finally: pointed maps from bool are actually just one element in the codomain.
    from-bool∙-single : (⊙Sphere {i} O →̇ D̂) ≃ D
    from-bool∙-single = (⊙Sphere {i} O →̇ D̂)
                           ≃⟨ from-bool∙ ⁻¹ ⟩
                         (Σ (D × D) λ d2 → fst d2 == d₀)
                           ≃⟨ Σ-sngltn ⟩
                         D
                           ≃∎ 
                   
    -- very good - it computes as it should!
    reduce : ((⊙Sphere {i} O) →̇ D̂) → D
    reduce (f , _) = f ff₀

    test : reduce == fst from-bool∙-single
    test = idp

-}
