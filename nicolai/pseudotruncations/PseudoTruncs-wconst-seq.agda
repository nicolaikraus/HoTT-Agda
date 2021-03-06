{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.PathFunctor
open import lib.PathGroupoid

open import lib.types.Bool
open import lib.types.IteratedSuspension
open import lib.types.LoopSpace
open import lib.types.Nat
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.Suspension
open import lib.types.TLevel
open import lib.types.Unit

open import nicolai.pseudotruncations.Preliminary-definitions
open import nicolai.pseudotruncations.Liblemmas
open import nicolai.pseudotruncations.SeqColim
open import nicolai.pseudotruncations.wconstSequence


module nicolai.pseudotruncations.PseudoTruncs-wconst-seq where


open import nicolai.pseudotruncations.pointed-O-Sphere
open import nicolai.pseudotruncations.LoopsAndSpheres
open import nicolai.pseudotruncations.PseudoTruncs

{- The special sequence that we consider -}
module PtruncsSeq {i} (X : Type i) where

  A : ℕ → Type i
  A O = X
  A (S n) = Pseudo n -1-trunc (A n)

  f : (n : ℕ) → A n → A (S n)
  f n x = point n -1 x
  
  C : Sequence {i}
  C = (A , f)





{- A main result: If we have an inhabitant of X, then the sequence is weakly constant. 
   This is Lemma 6.2 ! -}
module PtruncSeqWC {i} (X : Type i) (x₀ : X) where

  open PtruncsSeq {i} X

  fs : (n : ℕ) → A n
  fs O = x₀
  fs (S n) = f n (fs n)

  P : (n : ℕ) → (x : A n) → Type i
  P n x = f n x == fs (S n)

  {- This is the easy 'Case j ≡ -2' -}
  f₀-x₀ : (y : X) → P O y  
  f₀-x₀ y = (spoke O -1 r (lift false)) ∙ ! (spoke O -1 r (lift true))  where

    r : Sphere {i} O → X
    r (lift true) = x₀
    r (lift false) = y
  
  {- Now, the general case is done by induction on n 
     (note that this variable is called 'j' in the paper).
     Hence, what is 'j' in the paper is now 'S n'.

     Unfortunately, we have to do everything in one "big"
     step with many "where" clauses due to the mutual dependencies. -}
  
  fₙ-x₀ : (n : ℕ) → (y : A n) → P n y
  fₙ-x₀ O y = f₀-x₀ y
  fₙ-x₀ (S n) = Pseudotrunc-ind n Point Hub Spoke where

    -- just for convenience - saves brackets
    norₙ' : Sphere' {i} n
    norₙ' = nor' n

    fⁿx₀ = fs n

    Point : (w : A n) → P (S n) (point n -1 w)
    Point w = ap (point (S n) -1) (fₙ-x₀ n w)

    Hub : (r : Sphere' n → A n) → point S n -1 _ == _
    Hub r = ap (point (S n) -1) (! (spoke n -1 r norₙ') ∙ fₙ-x₀ n (r norₙ'))

    {- The definition of [Spoke] is the hard part. 
       First, we do the easy things that we have to do... -}
    Spoke : (r : _) → (x : Sphere' n) → _
    Spoke r = λ x → from-transp (P (S n))
                                (spoke n -1 r x)
                                (
      transport (P (S n)) (spoke n -1 r x) (Point (r x))
        =⟨ trans-ap₁ (f (S n)) (fs (S (S n))) (spoke n -1 r x) (Point (r x)) ⟩
      ! (ap (point (S n) -1) (spoke n -1 r x)) ∙ Point (r x)
        =⟨ ! (ap (point (S n) -1) (spoke n -1 r x)) ∙ₗ ! (∙-unit-r (Point (r x))) ⟩
      ! (ap (point (S n) -1) (spoke n -1 r x)) ∙ Point (r x) ∙ idp
        {- Now comes the hard step which requires A LOT of work in the where clause
           below: we can compose with something which, for a complicated reason, is idp! -}
        =⟨ ! (ap (point (S n) -1) (spoke n -1 r x)) ∙ₗ (Point (r x) ∙ₗ ! (k-const x)) ⟩
      ! (ap (point (S n) -1) (spoke n -1 r x)) ∙ Point (r x) ∙ k x
        {- From here, it's easy; we just have to re-associate paths and cancel inverses. 
           This could be done with standard library lemmas, but it's easier to just use
           an 'ad-hoc' lemma. -}
        =⟨ multi-cancelling (ap (point S n -1) (spoke n -1 r x)) (Point (r x)) (Hub r) ⟩
      Hub r
        ∎ 
      )

        where

          {- Now, the actual work follows! -}
      
          {- First, we define the interesting loop. 
             In the paper, it is called [kₓ]. 
             Here, it is just [k x].  -}
          k : (x : Sphere' {i} n)
              → Ω (Pseudo S n -1-trunc (A (S n)) ,
                   f (S n) (f n fⁿx₀))
          k x = ! (Point (r x)) ∙ ap (point (S n) -1) (spoke n -1 r x) ∙ (Hub r)

          {- We want to show that [k] factors as [ap pₙ ∘ h].
             First, we define h. -}
          h : Sphere' {i} n
              → Ω (Pseudo n -1-trunc (A n) ,
                   f n fⁿx₀)
          h x =   ! (fₙ-x₀ n (r x))
                ∙ (spoke n -1 r x)
                ∙ (! (spoke n -1 r norₙ') ∙ fₙ-x₀ n (r norₙ'))

          {- The statement that k == ap pₙ ∘ h: -}
          k-p-h : k == ap (point S n -1) ∘ h
          k-p-h = λ= (λ (x : Sphere' {i} n)
                     → k x
                         =⟨ idp ⟩
                         ! (Point (r x))
                       ∙ (ap (point (S n) -1) (spoke n -1 r x) ∙ (Hub r))
                         =⟨ !-ap (point S n -1) (fₙ-x₀ n (r x))
                                ∙ᵣ (  ap (point S n -1) (spoke n -1 r x)
                                    ∙ Hub r) ⟩
                         ap (point (S n) -1) (! (fₙ-x₀ n (r x)))
                       ∙ ap (point (S n) -1) (spoke n -1 r x)
                       ∙ (Hub r)
                         =⟨ ! (ap (point (S n) -1) (! (fₙ-x₀ n (r x)))
                                ∙ₗ ap-∙ point S n -1
                                        (spoke n -1 r x)
                                        _ ) ⟩
                         ap (point (S n) -1) (! (fₙ-x₀ n (r x)))
                       ∙ ap (point (S n) -1)
                            (  spoke n -1 r x
                             ∙ (! (spoke n -1 r norₙ')
                             ∙ fₙ-x₀ n (r norₙ')))
                         =⟨ ! (ap-∙ point S n -1 (! (fₙ-x₀ n (r x))) _) ⟩  
                       ap (point S n -1) (h x)
                         ∎)

          {- [h] can be made into a a pointed map, written [ĥ] -}
          ĥ : (⊙Sphere' {i} n)
                 →̇ ⊙Ω (A (S n) ,
                      f n fⁿx₀)
          ĥ = h , 
                  (! (fₙ-x₀ n (r _)) 
                ∙ (spoke n -1 r _)
                ∙ ! (spoke n -1 r norₙ')
                ∙ fₙ-x₀ n (r norₙ')

                  =⟨ (! (fₙ-x₀ n (r _)))
                      ∙ₗ (! (∙-assoc (spoke n -1 r _)
                                     (! (spoke n -1 r norₙ'))
                                     (fₙ-x₀ n (r norₙ')))) ⟩
                  
                ! (fₙ-x₀ n (r _))
                ∙ ((spoke n -1 r _) ∙ (! (spoke n -1 r norₙ')))
                ∙ fₙ-x₀ n (r norₙ')
                
                  =⟨ ! (fₙ-x₀ n (r _))
                     ∙ₗ !-inv-r (spoke n -1 r _)
                     ∙ᵣ fₙ-x₀ n (r norₙ') ⟩

                ! (fₙ-x₀ n (r _))
                ∙ idp
                ∙ fₙ-x₀ n (r norₙ')

                
                  =⟨ !-inv-l (fₙ-x₀ n (r _)) ⟩
                  
                idp
                
                  ∎ )

          {- A pointed version of the first constructor. -}
          pointsₙ : (A (S n) , f n fⁿx₀) →̇ A (S (S n)) , f (S n) (f n fⁿx₀) 
          pointsₙ = point S n -1 , idp 

          open null
          open hom-adjoint
          
          points-Φ⁻¹-null : isNull∙ (pointsₙ ⊙∘ Φ⁻¹ _ _ ĥ) 
          points-Φ⁻¹-null = <– (isNull-equiv (pointsₙ ⊙∘ Φ⁻¹ _ _ ĥ))
                            -- translate from isNull∙'
                                 (null-lequiv (pointsₙ ⊙∘ Φ⁻¹ _ _ ĥ)
                                 -- translate from isNulld; this,
                                 -- we have done already!
                                    (cmp-nll'.from-sphere-null'∙ n (Φ⁻¹ _ _ ĥ)))

          ap-points-ĥ-null : isNull∙ (⊙ap (point S n -1 , idp) ⊙∘ ĥ)
          ap-points-ĥ-null = –> (combine-isnull-nat' ĥ (point S n -1 , idp)) points-Φ⁻¹-null

          {- ... consequently, h is always refl [in the library "idp"]: -}
          points-h-const : (x : Sphere' n) → ap (point S n -1) (h x) == idp
          points-h-const x = null-lequiv-easy _ ap-points-ĥ-null x 

          {- ... and so is k: -}
          k-const : (x : Sphere' n) → k x == idp
          k-const x = app= k-p-h x  ∙ points-h-const x 





  {- Main result: each function in the sequence is propositional! -}
  wconst-f : wconst-chain C
  wconst-f n w₁ w₂ = fₙ-x₀ n w₁ ∙ ! (fₙ-x₀ n w₂)


{- Another important result: 
   if we want to show a proposition, we can assume A₀ instead of Aω
   But this should follow from the general induction principle, so... TODO
-} 
module PtruncSeqResult' {i} (X : Type i) where

  open PtruncsSeq {i} X -- this defines the chain C of pseudo-truncations

  SC = SeqCo C

  reduction-lemma : (P : Type i) → (is-prop P) → (A O → P) → (SC → P)
  reduction-lemma P ip ff = SeqCo-rec {C = C} {B = P} Ins Glue where

    Ins : (n : ℕ) → A n → P
    Ins O = ff 
    Ins (S n) = Pseudotrunc-rec {P = P} n Point-1 Hub-1 Spoke-1 where
      Point-1 : _ → P
      Point-1 x = Ins n x
      Hub-1 : (Sphere' n → A n) → P
      Hub-1 r = Ins n (r (nor' n))
      Spoke-1 : (r : Sphere' n → A n) (x : Sphere' n) → Point-1 (r x) == Hub-1 r
      Spoke-1 r x = prop-has-all-paths {A = P} ip _ _

    Glue : (n : ℕ) (a : A n) → Ins n a == Ins (S n) (f n a) 
    Glue n a = prop-has-all-paths ip _ _


{- Corollary of the main result: The colimit of the considered sequence is propositional! -}
module PtruncSeqResult {i} (X : Type i) where

  open PtruncsSeq {i} X -- this defines the chain C of pseudo-truncations

  colim-is-prp : is-prop (SeqCo C)
  colim-is-prp =
    inhab-to-contr-is-prop
      (PtruncSeqResult'.reduction-lemma X (is-contr (SeqCo C)) has-level-is-prop
        (λ x₀ → ins O x₀ , prop-has-all-paths (wconst-prop C (PtruncSeqWC.wconst-f X x₀))
          (ins O x₀)))


  open PtruncSeqResult' X

  {- If we have the propositional truncation in the theory: -}
  open import lib.types.Truncation
  
  colim-is-trunc : (Trunc ⟨-1⟩ X) ≃ SeqCo C
  colim-is-trunc = equiv (Trunc-rec (colim-is-prp) (ins 0))
                         (reduction-lemma (Trunc ⟨-1⟩ X) Trunc-level [_])
                         (λ _ → prop-has-all-paths colim-is-prp _ _)
                         (λ _ → prop-has-all-paths Trunc-level _ _)

