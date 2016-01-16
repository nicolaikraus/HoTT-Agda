{-# OPTIONS --without-K #-}

open import lib.Basics 
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.NType2
open import lib.PathGroupoid
-- some lemmas which should presumably be in the library (?)
open import nicolai.pseudotruncations.Liblemmas


module nicolai.pseudotruncations.SeqColim where

Sequence : ∀ {i} → Type (lsucc i) 
Sequence {i} = Σ (ℕ → Type i)
              (λ A → (n : ℕ) → A n → A (S n))


module _ {i} where

  private
    data #SeqCo-aux (C : Sequence {i}) : Type i where
      #ins : (n : ℕ) → (fst C n) → #SeqCo-aux C

    data #SeqCo (C : Sequence {i}) : Type i where
      #trick-aux : #SeqCo-aux C → (Unit → Unit) → #SeqCo C

  SeqCo : (C : Sequence {i}) → Type i
  SeqCo = #SeqCo

  ins : {C : Sequence {i}} → (n : ℕ) → (fst C n) → SeqCo C
  ins {C} n a = #trick-aux (#ins n a) _ 

  postulate
    glue : {C : Sequence {i}} → (n : ℕ) → (a : fst C n)
                           → (ins {C} n a) == (ins (S n) (snd C n a))

  module SeqCoInduction {C : Sequence {i}} {j} {P : SeqCo C → Type j}
                   (Ins : (n : ℕ) → (a : fst C n) → P (ins n a))
                   (Glue : (n : ℕ) → (a : fst C n)
                   → (Ins n a) == (Ins (S n) (snd C n a)) [ P ↓ (glue n a) ])
                   where
    f : Π (SeqCo C) P
    f = f-aux phantom where
      f-aux : Phantom Glue → Π (SeqCo C) P
      f-aux phantom (#trick-aux (#ins n a) _) = Ins n a

    postulate
      pathβ : (n : ℕ) → (a : fst C n) → apd f (glue n a) == (Glue n a)


open SeqCoInduction public renaming (f to SeqCo-ind ; pathβ to SeqCo-ind-pathβ)

{- we now have the induction principle [SeqCo-ind] with judgmental computation
   on points and 'homotopy' computation [SeqCo-ind-pathβ] on paths.
-}


module SeqCoRec {i j} {C : Sequence {i}} {B : Type j}
                (Ins : (n : ℕ) → (fst C n) → B)
                (Glue : (n : ℕ) → (a : fst C n)
                → (Ins n a) == (Ins (S n) (snd C n a))) 
                where

  private
    module M = SeqCoInduction {C = C} {P = λ _ → B} Ins (λ n a → ↓-cst-in (Glue n a))

  f : SeqCo C → B
  f = M.f

  pathβ : (n : ℕ) → (a : fst C n) → ap f (glue n a) == (Glue n a)
  pathβ n a = apd=cst-in {f = f} (M.pathβ n a)

open SeqCoRec public renaming (f to SeqCo-rec ; pathβ to SeqCo-rec-pathβ)

{- we now further have the recursion principle [SeqCo-rec], 
   which of course is just a special case of [SeqCo-ind]
-}

{- remove the first segment of a sequence -}
removeFst : ∀ {i} → Sequence {i} → Sequence {i}
removeFst (A , f) = (λ n → A (S n)) , (λ n → f (S n))

{- removing the first segment does not change the colimit -}
module ignoreFst {i} (C : Sequence {i}) where

  A = fst C
  f = snd C
  SC = SeqCo C

  C' = removeFst C
  A' = fst C'
  f' = snd C'
  SC' = SeqCo C'

  k-ins : (n : ℕ) → A n → SC'
  k-ins O a = ins O (f O a)
  k-ins (S n) a = ins n a

  k-glue : (n : ℕ) (a : A n) → k-ins n a == k-ins (S n) (f n a)
  k-glue O a = idp
  k-glue (S n) a = glue n a

  -- the first map
  k : SC → SC'
  k = SeqCo-rec {C = C} {B = SC'} k-ins k-glue

  m-ins : (n : ℕ) → A' n → SC
  m-ins n a' = ins (S n) a'

  m-glue : (n : ℕ) (a' : A' n) → m-ins n a' == m-ins (S n) (f' n a')
  m-glue n a' = glue (S n) a'

  -- the second map
  m : SC' → SC
  m = SeqCo-rec {C = C'} {B = SC} m-ins m-glue

  -- aux
  km-glue-comp : (n : ℕ) (a' : A' n) → ap (k ∘ m) (glue n a') == glue n a'
  km-glue-comp n a' =
    ap (k ∘ m) (glue n a')
      =⟨ ap-∘ _ _ _ ⟩
    ap k (ap m (glue n a'))
      =⟨ ap (λ p → ap k p) (SeqCo-rec-pathβ m-ins m-glue _ _) ⟩
    ap k (glue (S n) a')
      =⟨ SeqCo-rec-pathβ k-ins k-glue _ _ ⟩
    glue n a'
      ∎

  -- one direction, preparation
  km-ins : (n : ℕ) → (a' : A' n) → k (m (ins n a')) == ins n a'
  km-ins n a' = idp

  km-glue : (n : ℕ) → (a' : A' n) → (km-ins n a') == (km-ins (S n) (f' n a')) [(λ x' → k (m x') == x') ↓ (glue n a')]
  km-glue n a' = from-transp (λ x' → k (m x') == x') (glue n a')
                   (transport (λ x' → k (m x') == x') (glue n a') (km-ins n a')
                     =⟨ trans-ap {A = SC'} {B = SC'} (k ∘ m) (idf SC') (glue n a') (km-ins n a') ⟩
                   ! (ap (k ∘ m) (glue n a')) ∙ ap (idf SC') (glue n a')
                     =⟨ ap (λ p → (! (ap (k ∘ m) (glue n a'))) ∙ p) (ap-idf _) ⟩
                   ! (ap (k ∘ m) (glue n a')) ∙ (glue n a')
                     =⟨ ap (λ p → ! p ∙ (glue n a')) (km-glue-comp n a') ⟩
                   ! (glue n a') ∙ (glue n a')
                     =⟨ !-inv-l (glue n a') ⟩
                   km-ins (S n) (f' n a')
                     ∎ )

  -- one direction
  km : (x' : SC') → k (m x') == x'
  km = SeqCo-ind {P = λ x' → k (m x') == x'} km-ins km-glue 

  -- other direction, preparation
  mk-ins : (n : ℕ) → (a : A n) → m (k (ins n a)) == ins n a
  mk-ins O a = ! (glue 0 a)
  mk-ins (S n) a = idp

  -- auxiliary calculation
  mk-glue-comp : (n : ℕ) → (a : A n) → mk-ins n a ∙ glue n a == ap (m ∘ k) (glue n a)
  mk-glue-comp O a = 
    mk-ins O a ∙ glue O a
      =⟨ !-inv-l (glue O a) ⟩
    idp
      =⟨ idp ⟩
    ap m (idp {a = ins O (f O a)})
      =⟨ ap (λ p → ap m p) (! (SeqCo-rec-pathβ k-ins k-glue O a)) ⟩
    ap m (ap k (glue O a))
      =⟨ ! (ap-∘ m k _) ⟩
    ap (m ∘ k) (glue O a)
      ∎ 
  mk-glue-comp (S n) a = 
    mk-ins (S n) a ∙ glue (S n) a
      =⟨ idp ⟩
    glue (S n) a
      =⟨ ! (SeqCo-rec-pathβ m-ins m-glue n a) ⟩
    ap m (glue n a)
      =⟨ ap (λ p → ap m p) (! (SeqCo-rec-pathβ k-ins k-glue (S n) a)) ⟩
    ap m (ap k (glue (S n) a))
      =⟨ ! (ap-∘ m k _) ⟩
    ap (m ∘ k) (glue (S n) a)
      ∎ 

  mk-glue : (n : ℕ) → (a : A n) → (mk-ins n a) == (mk-ins (S n) (f n a)) [(λ x → m (k x) == x) ↓ (glue n a)]
  mk-glue n a = from-transp (λ x → m (k x) == x) (glue n a)
                  (transport (λ x → m (k x) == x) (glue n a) (mk-ins n a)
                    =⟨ trans-ap (m ∘ k) (idf _) (glue n a) (mk-ins n a) ⟩
                  ! (ap (m ∘ k) (glue n a)) ∙ mk-ins n a ∙ ap (idf SC) (glue n a)
                    =⟨ ap (λ p → ! (ap (m ∘ k) (glue n a)) ∙ (mk-ins n a) ∙ p) (ap-idf (glue n a)) ⟩
                  ! (ap (m ∘ k) (glue n a)) ∙ mk-ins n a ∙ (glue n a)
                    =⟨ ap (λ p → (! (ap (m ∘ k) (glue n a))) ∙ p) (mk-glue-comp n a) ⟩
                  ! (ap (m ∘ k) (glue n a)) ∙ ap (m ∘ k) (glue n a)
                    =⟨ !-inv-l (ap (m ∘ k) (glue n a)) ⟩
                  idp
                    =⟨ idp ⟩
                  mk-ins (S n) (f n a)
                    ∎)

  -- other direction
  mk : (x : SC) → m (k x) == x
  mk = SeqCo-ind {P = λ x → m (k x) == x} mk-ins mk-glue 

  remove : SC ≃ SC'
  remove = equiv k m km mk



{- summarized -}
ignore-fst : ∀ {i} → (C : Sequence {i}) → (SeqCo C) ≃ (SeqCo (removeFst C))
ignore-fst C = ignoreFst.remove C 

{- Now, we do this n times instead of once ...-}

removeInit : ∀ {i} → (C : Sequence {i}) → (n : ℕ) → Sequence {i}
removeInit C O = C
removeInit C (S n) = removeInit (removeFst C) n

ignore-init-aux : ∀ {i} → (C C' : Sequence {i}) → (SeqCo C) ≃ (SeqCo C') → (n : ℕ) → (SeqCo C) ≃ (SeqCo (removeInit C' n))
ignore-init-aux C C' e O = e
ignore-init-aux C C' e (S n) =
  ignore-init-aux C (removeFst C') (ignore-fst C' ∘e e) n

{- Result: the sequential colimit of a sequence stays the same if we remove 
   an initial finite segment of the sequence.
-}
ignore-init : ∀ {i} → (C : Sequence {i}) → (n : ℕ) → (SeqCo C) ≃ (SeqCo (removeInit C n))
ignore-init C = ignore-init-aux C C (ide _) 


-- TODO do we need this?
{- if we have a sequence and a point of the first type,
   we get a point of the type after removing some initial segment
-}
new-initial : ∀ {i} (C : Sequence {i}) (n : ℕ) →  (fst C n) → fst (removeInit C n) O
new-initial C O a₀ = a₀
new-initial C (S n) a₀ = new-initial (removeFst C) n a₀ 


module _ {i} (C : Sequence {i}) (a₀ : fst C O) where

  {- nearly the same as above:
     lift the 'starting point' a₀ to any later type -}
  lift-point : (n : ℕ) → fst C n
  lift-point O = a₀
  lift-point (S n) = snd C n (lift-point n)

  {- this is more special than in the text, as we only consider (0,n), not (k,n) -}
  {- In the colimit, the lifted point is equal to the 'starting point' -}
  lift-point-= : (n : ℕ) → ins {C = C} O a₀ == ins n (lift-point n)  
  lift-point-= O = idp
  lift-point-= (S n) = (lift-point-= n) ∙ glue n _
