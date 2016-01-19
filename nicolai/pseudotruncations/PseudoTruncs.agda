{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.PathFunctor

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

open import nicolai.pseudotruncations.Liblemmas
open import nicolai.pseudotruncations.SeqColim
open import nicolai.pseudotruncations.wconstSequence


module nicolai.pseudotruncations.PseudoTruncs where


point-of-sphere : ∀ {i} (n : ℕ) → Sphere {i} n
point-of-sphere O = lift true
point-of-sphere (S n) = north _


{- Definition of the Pseudo-truncation -}
module _ {i} where

  private
    data #Pseudotrunc-aux (n : ℕ) (A : Type i) : Type i where
      #point : A → #Pseudotrunc-aux n A
      #hub : (r : Sphere n → A) → #Pseudotrunc-aux n A

    data #Pseudotrunc (n : ℕ) (A : Type i) : Type i where
      #trick-aux : #Pseudotrunc-aux n A → (Unit → Unit) → #Pseudotrunc n A

  Pseudo_-1-trunc : (n : ℕ) (A : Type i) → Type i
  Pseudo_-1-trunc = #Pseudotrunc

  point_-1 : {A : Type i} → (n : ℕ) → A → Pseudo n -1-trunc A
  point_-1 {A} n a = #trick-aux (#point a) _

  hub_-1 : {A : Type i} (n : ℕ) (r : Sphere n → A) → Pseudo n -1-trunc A
  hub_-1 {A} n r = #trick-aux (#hub r) _


  postulate
    spoke_-1 : {A : Type i} (n : ℕ) (r : Sphere n → A) (x : Sphere n)
               → point n -1 (r x) == hub n -1 r

  {- The induction principle -}
  module PseudotruncInduction
    {A : Type i} (n : ℕ) {j}
    {P : Pseudo n -1-trunc A → Type j}
    (Point-1 : (a : A) → P (point n -1 a))
    (Hub-1 : (r : Sphere n → A) → P (hub n -1 r))
    (Spoke-1 : (r : Sphere n → A) → (x : Sphere n)
               → Point-1 (r x) == Hub-1 r [ P ↓ spoke n -1 r x ])
    where

    f : Π (Pseudo n -1-trunc A) P
    f = f-aux phantom where
      f-aux : Phantom Spoke-1 → Π (Pseudo n -1-trunc A) P
      f-aux phantom (#trick-aux (#point x) _) = Point-1 x
      f-aux phantom (#trick-aux (#hub r) _) = Hub-1 r

    postulate
      pathβ : (r : Sphere {i} n → A)
              → (x : Sphere {i} n)
              → apd f (spoke n -1 r x) == Spoke-1 r x


open PseudotruncInduction public renaming
  (f to Pseudotrunc-ind ; pathβ to Pseudotrunc-ind-pathβ)


{- We derive the recursion principle from the induction principle -}
module PseudotruncRecursion
  {i j} {A : Type i} 
  {P : Type j} (n : ℕ)
  (Point-1 : A → P)
  (Hub-1 : (r : Sphere {i} n → A) → P)
  (Spoke-1 : (r : Sphere n → A) (x : Sphere n) → Point-1 (r x) == Hub-1 r)
  where

  rec : Pseudo n -1-trunc A → P
  rec = Pseudotrunc-ind n  {P = λ _ → P} Point-1 Hub-1
          (λ r x → from-transp
                    (λ _ → P)
                    (spoke n -1 r x)
                    ((transport (λ _ → P) (spoke n -1 r x) (Point-1 (r x)))
                        =⟨ transport-const-fam (spoke n -1 r x) (Point-1 (r x)) ⟩
                      Point-1 (r x)
                        =⟨ Spoke-1 r x ⟩
                      Hub-1 r
                        ∎))

open PseudotruncRecursion public renaming (rec to Pseudotrunc-rec)

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

  -- This is 'Case j ≡ -2'
  f₀-x₀ : (y : X) → P O y  
  f₀-x₀ y = (spoke O -1 r (lift false)) ∙ ! (spoke O -1 r (lift true))  where

    r : Sphere {i} O → X
    r (lift true) = x₀
    r (lift false) = y
  
  -- Now, the general case
  fₙ-x₀ : (n : ℕ) → (y : A n) → P n y
  fₙ-x₀ O y = f₀-x₀ y
  fₙ-x₀ (S n) = Pseudotrunc-ind n Point Hub Spoke where

    Point : (w : _) → _
    Point w = ap (point (S n) -1) (fₙ-x₀ n w)

    Hub : (r : _) → _
    Hub r = ap (point (S n) -1) (! (spoke n -1 r x) ∙ fₙ-x₀ n (r x)) where
      x : Sphere n
      x = point-of-sphere n

    Spoke : (r : _) → (x : Sphere n) → _
    Spoke r = λ x → from-transp (P (S n))
                                (spoke n -1 r x)
                                (
      transport (P (S n)) (spoke n -1 r x) (Point (r x))
        =⟨ trans-ap₁ (f (S n)) (fs (S (S n))) (spoke n -1 r x) (Point (r x)) ⟩
      ! (ap (point (S n) -1) (spoke n -1 r x)) ∙ Point (r x)
        =⟨ !-ap (point (S n) -1) (spoke n -1 r x) ∙ᵣ Point (r x) ⟩
      ap (point (S n) -1) (! (spoke n -1 r x)) ∙ Point (r x)
        =⟨ {!!} ⟩
      Hub r
        ∎ 
      )

        where

          -- careful: orientation change?
          k : (x : Sphere {i} n)
              → Ω (Pseudo S n -1-trunc (A (S n)) ,
                   point S n -1 (f n (fs n)))
          k x = ! (Point (r x)) ∙ ap (point (S n) -1) (spoke n -1 r x) ∙ (Hub r)


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
      Hub-1 : (Sphere n → A n) → P
      Hub-1 r = Ins n (r (point-of-sphere n))
      Spoke-1 : (r : Sphere n → A n) (x : Sphere n) → Point-1 (r x) == Hub-1 r
      Spoke-1 r x = prop-has-all-paths {A = P} ip _ _

    Glue : (n : ℕ) (a : A n) → Ins n a == Ins (S n) (f n a) 
    Glue n a = prop-has-all-paths ip _ _


-- A main result: this colimit is propositional!
module PtruncSeqResult {i} (X : Type i) where

  open PtruncsSeq {i} X -- this defines the chain C of pseudo-truncations

  colim-is-prp : is-prop (SeqCo C)
  colim-is-prp = inhab-to-contr-is-prop (PtruncSeqResult'.reduction-lemma X (is-contr (SeqCo C)) has-level-is-prop (λ x₀ → ins O x₀ , prop-has-all-paths (wconst-prop C (PtruncSeqWC.wconst-f X x₀)) (ins O x₀)))

