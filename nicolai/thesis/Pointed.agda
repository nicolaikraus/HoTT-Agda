{-# OPTIONS --without-K #-}

{- This module serves to develop some basic theory about pointed types.
   After defining the usual notions of pointed types, pointed equivalences,
   and loop spaces, we derive a version of univalence for pointed equivalences
   and observe that univalence between identical types is a pointed equivalence.

   We define pointed versions of dependent sums and products using the usual
   notion of pointed families and observe that they commute in a certain sense
   with taking loop spaces. -}

module Pointed where

open import lib.Basics hiding (_⊔_)
open import lib.NType2
open import lib.types.Nat hiding (_+_)
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel

open import Preliminaries
open import UniverseOfNTypes

{- This file contains 
     2.2.15: Fam•
   and 
     2.2.17: has-level-equiv-contr-loops  (see end of file)
-}

{- Pointed types.
   A pointed type is a type (base) together with a chosen element (pt).
   The loop space construction Ω takes a pointed type and returns the type
   of all loops at the given basepoint. The trivial loop is taken as
   canonical element, thus forming a new pointed type. -}
Type• : (i : ULevel) → Type (lsucc i)
Type• i = Σ (Type i) (idf _)

module _ {i} (X : Type• i) where
  base = fst X
  pt   = snd X

-- Definition 2.2.15
{- Pointed families.
   A pointed family over a pointed type is a family over the base
   together with a inhabitant of the family at the point.
   Note that pointed types are equivalent to pointed families
   over the pointed unit type (not shown here). -}
Fam• : ∀ {i} (X : Type• i) (j : ULevel) → Type (i ⊔ lsucc j)
Fam• X j = Σ (base X → Type j) (λ P → P (pt X))


-- Alternate definition: Σ (n -Type i) ⟦_⟧
_-Type•_ : (n : ℕ₋₂) (i : ULevel) → Type (lsucc i)
n -Type• i = Σ (Type• i) (has-level n ∘ base)

-- For alternate definition: Σ-≤ (n -Type-≤ i) raise
_-Type•-≤_ : (n : ℕ₋₂) (i : ULevel) → S n -Type lsucc i
n -Type•-≤ i = ((n -Type• i)
              , equiv-preserves-level Σ-comm-snd
                                      (snd (Σ-≤ (n -Type-≤ i) raise)))

{- Pointed equivalences.
   An equivalence of pointed types is an equivalences of the bases
   that preserves the points -}
_≃•_ : ∀ {i j} → Type• i → Type• j → Set (i ⊔ j)
A ≃• B = Σ (base A ≃ base B) (λ f → –> f (pt A) == pt B)

ide• : ∀ {i} (X : Type• i) → X ≃• X
ide• _ = ide _ , idp

_∘e•_ : ∀ {i j k} {X : Type• i} {Y : Type• j} {Z : Type• k}
       → Y ≃• Z → X ≃• Y → X ≃• Z
(u , p) ∘e• (v , q) = (u ∘e v , ap (–> u) q ∙ p)

_⁻¹• : ∀ {i j} {X : Type• i} {Y : Type• j} → X ≃• Y → Y ≃• X
(u , p) ⁻¹• = u ⁻¹ , ap (<– u) (! p) ∙ <–-inv-l u _

-- Equational reasoning for pointed equivalences.
infix  2 _≃•∎
infixr 2 _≃•⟨_⟩_

_≃•⟨_⟩_ : ∀ {i j k} (X : Type• i) {Y : Type• j} {Z : Type• k}
          → X ≃• Y → Y ≃• Z → X ≃• Z
_ ≃•⟨ u ⟩ v = v ∘e• u

_≃•∎ : ∀ {i} (X : Type• i) → X ≃• X
_≃•∎ = ide•


-- The loop space construction.
Ω : ∀ {i} → Type• i → Type• i
Ω (A , a) = ((a == a) , idp)

Ω-≤ : ∀ {i} {n : ℕ₋₂} → (S n) -Type• i → n -Type• i
Ω-≤ ((A , a) , t) = (Ω (A , a) , t a a)

-- Loop spaces are preserved by pointed equivalences.
equiv-Ω : ∀ {i j} {X : Type• i} {Y : Type• j} → X ≃• Y → Ω X ≃• Ω Y
equiv-Ω (u , p) = split u p where
  split : ∀ u {a} {b} → –> u a == b → Ω (_ , a) ≃• Ω (_ , b)
  split u idp = (equiv-ap u _ _ , idp)

equiv-Ω^ : ∀ {i j} {X : Type• i} {Y : Type• j} (n : ℕ)
           → X ≃• Y → (Ω ^ n) X ≃• (Ω ^ n) Y
equiv-Ω^ 0     e = e
equiv-Ω^ (S n) e = equiv-Ω^ n (equiv-Ω e)


{- We call a pointed type n-truncated if its base is.
   Constructing the loop space decrements the truncation level. -}
has-level• : ∀ {i} → ℕ₋₂ → Type• i → Type i
has-level• n = has-level n ∘ base

trunc-many : ∀ {i} {X : Type• i} {k : ℕ} (n : ℕ)
             → has-level• ((k + n) -2)          X
             → has-level• (k     -2) ((Ω ^ n) X)
trunc-many 0     t = t
trunc-many (S n) t = trunc-many n (t _ _)

--Ω^-≤ : ∀ {i} {k : ℕ} (n : ℕ) → (k + n -2) -Type• i → (k -2) -Type• i
--Ω^-≤ O     X = X
--Ω^-≤ (S n) X = Ω^-≤ n (Ω-≤ X)

Ω^-≤ : ∀ {i} {k : ℕ} (n : ℕ) → ((k + n) -2) -Type• i → (k -2) -Type• i
Ω^-≤ n (X , t) = ((Ω ^ n) X , trunc-many n t)

Ω^-≤' : ∀ {i} {k : ℕ} (n : ℕ) → ((n + k) -2) -Type• i → (k -2) -Type• i
Ω^-≤' n (X , t) =
  ((Ω ^ n) X , trunc-many n (transport (λ z → has-level• (z -2) X)
                                       (+-comm _ n) t))


{- Pointedness allows for a more direct notion of contractibility.
   Beware that is-contr• will be equivalent --- not definitionally equal ---
   to has-level∙ ⟨-2⟩. -}
module _ {i} (X : Type• i) where
  is-contr• : Type i
  is-contr• = ∀ a → pt X == a

{- Since pointed types are always inhabited,
   being contractible and propositional is equivalent. -}
module _ {i} {X : Type• i} where
  contr•-equiv-contr : is-contr• X ≃ is-contr (base X)
  contr•-equiv-contr = prop-equiv'
                         (λ c → Π-level (λ a → raise-level-<T (ltSR ltS) c _ _))
                         (cst is-contr-is-prop)
                         (λ x → (pt X , x))
                         (λ y _ → prop-has-all-paths (contr-is-prop y) _ _)

  is-contr•-is-prop : is-prop (is-contr• X)
  is-contr•-is-prop = equiv-preserves-level (contr•-equiv-contr ⁻¹)
                                            is-contr-is-prop

  prop-equiv-contr : is-prop (base X) ≃ is-contr (base X)
  prop-equiv-contr = prop-equiv is-prop-is-prop
                                is-contr-is-prop
                                (inhab-prop-is-contr (pt X))
                                contr-is-prop

  contr•-equiv-prop : is-contr• X ≃ is-prop (base X)
  contr•-equiv-prop = prop-equiv-contr ⁻¹ ∘e contr•-equiv-contr



-- Pointed equivalences preserve (pointed) contractibility.
equiv-is-contr• : ∀ {i j} {X : Type• i} {Y : Type• j}
                → X ≃• Y → is-contr• X ≃ is-contr• Y
equiv-is-contr• (u , p) = contr•-equiv-contr ⁻¹
                       ∘e equiv-level u
                       ∘e contr•-equiv-contr


-- Univalence for pointed equivalences.
module _ {i} {A B : Type• i} where
  ua•-equiv : (A ≃• B) ≃ (A == B)
  ua•-equiv = 
      A ≃• B
    ≃⟨ ide _ ⟩
      Σ (base A ≃ base B) (λ f → –> f (pt A) == pt B)
    ≃⟨ equiv-Σ-fst _ (snd (ua-equiv ⁻¹)) ⁻¹ ⟩
      Σ (base A == base B) (λ q → coe q (pt A) == pt B)
    ≃⟨ equiv-Σ-snd (λ q → coe-equiv (ap (λ f → coe f (pt A) == pt B)
                                        (! (ap-idf q)))) ⟩
      Σ (base A == base B) (λ q → coe (ap (idf _) q) (pt A) == pt B)
    ≃⟨ equiv-Σ-snd (λ q → to-transp-equiv _ q ⁻¹) ⟩
      Σ (base A == base B) (λ q → pt A == pt B [ idf _ ↓ q ])
    ≃⟨ =Σ-eqv _ _ ⟩
      A == B
    ≃∎

  ua• : A ≃• B → A == B
  ua• = –> ua•-equiv

  coe•-equiv : A == B → A ≃• B
  coe•-equiv = <– ua•-equiv

-- Normal univalence can be made pointed in the endo-setting.
module _ {i} {A : Type i} where
  ua-equiv• : ((A ≃ A) , ide _) ≃• ((A == A) , idp)
  ua-equiv• = ((ua-equiv ⁻¹) , idp) ⁻¹•


-- Lemma 2.2.17
{- The induction step for Lemma 7.2.9 in the HoTT Book is
   more complicated than necesarry. Associating iterated loop spaces in
   the reverse order, we can do it with the prerequisites 7.2.7 and 7.2.8
   (of the book) as well as further auxiliary steps. -}
has-level-equiv-contr-loops : ∀ {i} {n : ℕ} {A : Type i}
                              →   has-level (n -1) A
                                ≃ ((a : A) → is-contr• ((Ω ^ n) (A , a)))
has-level-equiv-contr-loops {n = O} {A} =
    is-prop A                      ≃⟨ prop-equiv-inhab-to-contr ⟩
    (A → is-contr A)               ≃⟨ equiv-Π-r (λ _ → contr•-equiv-contr ⁻¹) ⟩
    ((a : A) → is-contr• (A , a))  ≃∎
has-level-equiv-contr-loops {n = S n} {A} = equiv-Π-r lem where
  lem = λ a →
      (((b : A) → has-level (n -1) (a == b)))
    ≃⟨ equiv-Π-r (λ _ → has-level-equiv-contr-loops) ⟩
      (((b : A) (p : a == b) → is-contr• ((Ω ^ n) ((a == b) , p))))
    ≃⟨ Π₁-contr (pathfrom-is-contr _) ∘e curry-equiv ⁻¹ ⟩
      is-contr• ((Ω ^ n) ((a == a) , idp))
    ≃∎


