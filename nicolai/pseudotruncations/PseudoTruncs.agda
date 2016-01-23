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


module nicolai.pseudotruncations.PseudoTruncs where


{- Definition of the Pseudo-truncation -}
module _ {i} where

  private
    data #Pseudotrunc-aux (n : ℕ) (A : Type i) : Type i where
      #point : A → #Pseudotrunc-aux n A
      #hub : (r : Sphere' n → A) → #Pseudotrunc-aux n A

    data #Pseudotrunc (n : ℕ) (A : Type i) : Type i where
      #trick-aux : #Pseudotrunc-aux n A → (Unit → Unit) → #Pseudotrunc n A

  Pseudo_-1-trunc : (n : ℕ) (A : Type i) → Type i
  Pseudo_-1-trunc = #Pseudotrunc

  point_-1 : {A : Type i} → (n : ℕ) → A → Pseudo n -1-trunc A
  point_-1 {A} n a = #trick-aux (#point a) _

  hub_-1 : {A : Type i} (n : ℕ) (r : Sphere' n → A) → Pseudo n -1-trunc A
  hub_-1 {A} n r = #trick-aux (#hub r) _


  postulate
    spoke_-1 : {A : Type i} (n : ℕ) (r : Sphere' n → A) (x : Sphere' n)
               → point n -1 (r x) == hub n -1 r

  {- The induction principle -}
  module PseudotruncInduction
    {A : Type i} (n : ℕ) {j}
    {P : Pseudo n -1-trunc A → Type j}
    (Point-1 : (a : A) → P (point n -1 a))
    (Hub-1 : (r : Sphere' n → A) → P (hub n -1 r))
    (Spoke-1 : (r : Sphere' n → A) → (x : Sphere' n)
               → Point-1 (r x) == Hub-1 r [ P ↓ spoke n -1 r x ])
    where

    f : Π (Pseudo n -1-trunc A) P
    f = f-aux phantom where
      f-aux : Phantom Spoke-1 → Π (Pseudo n -1-trunc A) P
      f-aux phantom (#trick-aux (#point x) _) = Point-1 x
      f-aux phantom (#trick-aux (#hub r) _) = Hub-1 r

    postulate
      pathβ : (r : Sphere' {i} n → A)
              → (x : Sphere' {i} n)
              → apd f (spoke n -1 r x) == Spoke-1 r x


open PseudotruncInduction public renaming
  (f to Pseudotrunc-ind ; pathβ to Pseudotrunc-ind-pathβ)


{- We derive the recursion principle from the induction principle -}
module PseudotruncRecursion
  {i j} {A : Type i} 
  {P : Type j} (n : ℕ)
  (Point-1 : A → P)
  (Hub-1 : (r : Sphere' {i} n → A) → P)
  (Spoke-1 : (r : Sphere' n → A) (x : Sphere' n) → Point-1 (r x) == Hub-1 r)
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



{- A lemma that will be important later: any map from
   the sphere, composed with the points constructor,
   is null. -}
   
open import nicolai.pseudotruncations.pointed-O-Sphere
open import nicolai.pseudotruncations.LoopsAndSpheres
open null

module _ {i} {A : Type i} (n : ℕ) where

  from-sphere-null : (g : Sphere' {i} n → A)
                   → isNull (point n -1 (g (nor' n))) ((point n -1) ∘ g)
  from-sphere-null g x = point n -1 (g x)
                           =⟨ spoke n -1 g x ⟩
                         hub n -1 g
                           =⟨ ! (spoke n -1 g (nor' n)) ⟩
                         point n -1 (g (nor' n))
                           ∎

  {- Unforunately, we will need this lemma not for maps
        g : Sphere' (S n) → A,
     but we will need it for maps
        g : Susp (Sphere' n) → A,
     and Sphere' (S n) is NOT judgmentally equal to Susp (Sphere' n).
     We have to give a second proof. -}
