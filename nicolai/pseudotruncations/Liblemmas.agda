{-# OPTIONS --without-K #-}

open import lib.Basics -- hiding (_=⟨_⟩_ ; _∎)
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.NType2
open import lib.PathGroupoid

module nicolai.pseudotruncations.Liblemmas where

-- transport along constant family
transport-const-fam : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A}
                → (p : a₁ == a₂) → (b : B) → transport (λ _ → B) p b == b
transport-const-fam idp b = idp

-- interaction of transport and ap
trans-ap : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A}
           → (f g : A → B) → (p : a₁ == a₂) → (q : f a₁ == g a₁)
           → transport (λ x → f x == g x) p q == ! (ap f p) ∙ q ∙ (ap g p)
trans-ap f g idp q = ! (∙-unit-r q)


-- TODO this special case should be used a couple of times instead of the general version!

-- special interaction of transport and ap, where the second map is constant at a point
trans-ap₁ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a₁ a₂ : A} (b : B)
            (p : a₁ == a₂) (q : f a₁ == b)
            → transport (λ a → f a == b) p q == ! (ap f p) ∙ q
trans-ap₁ f b idp q = idp

-- first map is constant at a point
trans-ap₂ : ∀ {i j} {A : Type i} {B : Type j} (g : A → B) {a₁ a₂ : A} (b : B)
            (p : a₁ == a₂) (q : b == g a₁)
            → transport (λ a → b == g a) p q == q ∙ ap g p
trans-ap₂ g b idp q = !( ∙-unit-r _) 

-- definition of weak constancy
wconst : ∀ {i j} {A : Type i} {B : Type j} → (A → B) → Type (lmax i j)
wconst {A = A} f = (a₁ a₂ : A) → f a₁ == f a₂ 

-- if f is weakly constant, then so is ap f
ap-const : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
           → wconst f → {a₁ a₂ : A} → wconst (ap f {x = a₁} {y = a₂})
ap-const {A = A} f wc p q = calc-ap p ∙ ! (calc-ap q) where
  calc-ap : {a₁ a₂ : A} → (p : a₁ == a₂) → ap f p == wc a₁ a₂ ∙ ! (wc a₂ a₂)
  calc-ap idp = ! (!-inv-r (wc _ _))

-- in particular, if f is weakly constant, then ap f maps loops to 'refl'
ap-const₁ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
           → wconst f → {a₁ : A} → (p : a₁ == a₁) → ap f p == idp
ap-const₁ f wc p = ap-const f wc p idp

-- if f is constant at a point, it maps every path to 'refl'
ap-const-at-point : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A}
                    (b : B) (p : a₁ == a₂) → ap (λ _ → b) p == idp
ap-const-at-point b idp = idp


{- this lemma is ad-hoc; it could be proved as a concatenation of
   many library lemmas, but it would be much more tedious to do -}
adhoc-lemma : ∀ {i} {A : Type i} {x y z : A}
                (p : x == y)
                (q : z == y)
                (r : z == x)
                → p ∙ ! q ∙ r == idp
                → p == ! r ∙ q
adhoc-lemma p idp idp e = ! (∙-unit-r p) ∙ e
