{-# OPTIONS --without-K #-}

{- After a few preliminary lemmata about representing dependent functions,
   this module will derive the dependent universal property of
   our truncations (defined later) from the non-dependent one. -}
module Trunc.Universal where

-- This file contains the proof of Lemma 7.6.6

open import lib.Basics hiding (_⊔_)
open import lib.Equivalences2
open import lib.NType2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Unit

open import Preliminaries
open import UniverseOfNTypes

-- In the fibration fst : Σ A B → A, the fiber over a is given by B a.
trivial-fibers : ∀ {i j} {A : Type i} {B : A → Type j} (a : A)
                 → B a ≃ Σ (Σ A B) (λ s → a == fst s)
trivial-fibers {A = A} {B} a =
  B a                               ≃⟨ Σ₁-Unit ⁻¹ ⟩
  Σ ⊤ (λ _ → B a)                   ≃⟨ equiv-Σ-fst _ (snd (e ⁻¹)) ⟩
  Σ (Σ A (λ s → a == s)) (B ∘ fst)  ≃⟨ Σ-comm-snd ⟩
  Σ (Σ A B) (λ s → a == fst s)      ≃∎ where

  e : Σ A (λ s → a == s) ≃ ⊤
  e = contr-equiv-Unit (pathfrom-is-contr a)

{- Liftings of u : Π A B through fst : {a : A} → Σ (B a) (C a) → B a
   correponds to dependent functions from (a : A) to C a (u a).

   As mentioned in the article, we will make use only of a special case:
   liftings of u : A → B through fst : Σ B C → B correponds to
   dependent functions from (a : A) to C a. -}
Π-as-liftings : ∀ {i j k} {A : Type i} {B : A → Type j}
             (u : Π A B) {C : (a : A) → B a → Type k} → _
Π-as-liftings {A = A} {B} u {C} =
    Π A (λ a → C a (u a))
  ≃⟨ trivial-fibers u ⟩
    Σ (Σ (Π A B) (λ r → Π A (λ a → C a (r a)))) (λ {(r , _) → u == r})
  ≃⟨ equiv-Σ-fst _ (snd choice) ⁻¹ ⟩
    Σ (Π A (λ a → Σ (B a) (C a))) (λ s → u == fst ∘ s)
  ≃∎

{- Dependent functions from (a : A) to B a
   are given by sections of fst : Σ A B → A.

   Noting that sections are non-dependent functions, this folklore insight
   is a main ingredient in passing from non-dependent universal property
   to the dependent one. -}
Π-as-sections : ∀ {i j} {A : Type i} {B : A → Type j}
                → Π A B ≃ Σ (A → Σ A B) (λ s → idf _ == fst ∘ s)
Π-as-sections = Π-as-liftings (idf _)

{- Fix a truncation level n and a Type A. We will examine what it means
   for an n-type 'type' with constructor cons : A → ⟦ type ⟧
   to have the universal property of the n-truncation of A. -}
module _ {i} {n : ℕ₋₂} {A : Type i}
         (type : n -Type i) (cons : A → ⟦ type ⟧) where

  -- Definition 7.6.2: A with type and cons has the up if 'univ-Type':
  {- The (non-dependent) universal property:
     λ f → f ∘ cons  induces equivalence  (type → X) ≃ (A → X) -}
  univ-Type : (k : ULevel) → Type (i ⊔ lsucc k)
  univ-Type k = (X : n -Type k) → is-equiv
                  {A = ⟦ type ⟧ → ⟦ X ⟧}
                  {B = A → ⟦ X ⟧}
                  (λ f → f ∘ cons)

  -- Definition in Lemma 7.6.6 of 'dup'
  {- The dependent universal property:
     λ f → f ∘ cons  induces  ((a : type) → X a) ≃ ((a : A) → X (cons a)) -}
  duniv-Type : (k : ULevel) → Type (i ⊔ lsucc k)
  duniv-Type k = (X : ⟦ type ⟧ → n -Type k) → is-equiv
                   {A = Π ⟦ type ⟧ (⟦_⟧ ∘ X )}
                   {B = Π A (⟦_⟧ ∘ X ∘ cons)}
                   (λ f → f ∘ cons)
  
  {- If the universal property holds for a certain elimination universe U_j₂,
     then also for an elimination universe U_j₁ with j₁ ≤ j₂.
     Agda does not support specifying ordering relations between
     universe levels directly, but we may simulate j₁ ≤ j₂
     by decomposing j₁ = k₁ and j₂ = k₁ ⊔ k₂. -}
  univ-lower : ∀ {k₁} (k₂ : ULevel) → univ-Type (k₁ ⊔ k₂) → univ-Type k₁
  univ-lower {k₁} k₂ univ X = transport (λ z → is-equiv (λ f → z ∘ f ∘ cons))
                                        (λ= (<–-inv-r e)) hup where
    e : Lift {j = k₁ ⊔ k₂} ⟦ X ⟧ ≃ ⟦ X ⟧
    e = lift-equiv

    -- Adapted to the new version: had to replace "pre" with "post".
    -- Apparently, this was changed at some point.
    hup : is-equiv (λ (f : ⟦ type ⟧ → ⟦ X ⟧) → –> e ∘ <– e ∘ f ∘ cons)
    hup = snd construct-equivalence
      where
        construct-equivalence =
          (⟦ type ⟧ → ⟦ X ⟧)
            ≃⟨ (λ f → fst (e ⁻¹) ∘ f) , post∘-is-equiv (snd (e ⁻¹)) ⟩
          (⟦ type ⟧ → Lift {j = k₁ ⊔ k₂} ⟦ X ⟧)
            ≃⟨ (λ (ef : ⟦ type ⟧ → Lift {j = k₁ ⊔ k₂} ⟦ X ⟧) → ef ∘ cons) , univ (Lift-≤ X) ⟩
          (A → Lift {j = k₁ ⊔ k₂} ⟦ X ⟧)
            ≃⟨ (λ f → fst e ∘ f) , post∘-is-equiv (snd e) ⟩
          (A → ⟦ X ⟧)
            ≃∎ 
          
  {- We will now prove the main lemma of this section:
     The (non-dependent) universal property implies the dependent one. -}
  module with-univ {j} (univ : univ-Type (i ⊔ j)) (P : ⟦ type ⟧ → n -Type j) where
   
    -- abbreviating the underlying types (for readability)
    T = ⟦ type ⟧
    Q = ⟦_⟧ ∘ P

    {- As is usual for deriving dependent eliminators, the crux for deriving
       the dependent universal property is to first transform the *dependent*
       function spaces into *non-dependent* sections/liftings according to
       the lemmata above. -}
    eqv : Π T Q ≃ Π A (Q ∘ cons)
    eqv = Π-as-liftings cons ⁻¹ ∘e eqv-liftings ∘e Π-as-liftings (idf _) where
      
      {- Our goal now is an equivalence of Σ-types where the first components
         fit the template of the *non-dependent* universal property. -}
      eqv-liftings : Σ (T → Σ T Q) (λ s → idf _ == fst ∘ s)
                   ≃ Σ (A → Σ T Q) (λ t → cons  == fst ∘ t)
      eqv-liftings = equiv-Σ' (_ , univ (Σ-≤ type P)) lem where

        {- What remains is just the universal property applied to X itself,
           and then switching to path spaces. In the usual derivation of
           dependent elimination, this corresponds to application of
           the η-rule to the identity function. -}
        lem : (s : T → Σ T Q) → (idf _ == fst ∘ s) ≃ (cons == fst ∘ s ∘ cons)
        lem s = equiv-ap (_ , univ-lower (i ⊔ j) univ type) (idf _) (fst ∘ s)


    -- Finally: (the non-trivial direction of) Lemma 7.6.6
    {- Due to construction of the above equivalence via conjugation of
       the (non-dependent) universal property (on the first component),
       its action ends up being precisely composition with the constructor.
       Because of technical limitations of the Agda type-checker,
       we encapsulate the result in an abstract block to prevent
       the type checker from unnecessarily unfolding its value later on. -}
    abstract
      duniv : is-equiv (λ (f : ⟦ Π-≤ ⟦ type ⟧ P ⟧) → f ∘ cons)
      duniv = snd eqv
