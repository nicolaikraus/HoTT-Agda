{-# OPTIONS --without-K #-}


open import library.Basics hiding (Type ; Σ)
open import library.types.Sigma

open import Sec2preliminaries 

module Sec3hedberg where

-- Lemma 3.2
discr→pathHasConst : {X : Type} → has-dec-eq X → pathHasConst X
discr→pathHasConst dec x₁ x₂ with (dec x₁ x₂) 
discr→pathHasConst dec x₁ x₂ | inl p  = (λ _ → p) , (λ _ _ → idp)
discr→pathHasConst dec x₁ x₂ | inr np = idf _ , λ p → Empty-elim (np p)

-- Lemma 3.3
pathHasConst→isSet : {X : Type} → pathHasConst X → is-set X
pathHasConst→isSet {X} pc x₁ x₂ = all-paths-is-prop paths-equal where
  claim : (y₁ y₂ : X) → (p : y₁ == y₂) → p == ! (fst (pc _ _) idp) ∙ fst (pc _ _) p 
  claim x₁ .x₁ idp = ! (!-inv-l (fst (pc x₁ x₁) idp))
  paths-equal : (p₁ p₂ : x₁ == x₂) → p₁ == p₂
  paths-equal p₁ p₂ = 
    p₁                                      =⟨ claim _ _ p₁ ⟩
    ! (fst (pc _ _) idp) ∙ fst (pc _ _) p₁  =⟨ ap (λ q → (! (fst (pc x₁ x₁) idp)) ∙ q) (snd (pc _ _) p₁ p₂) ⟩ -- whiskering
    ! (fst (pc _ _) idp) ∙ fst (pc _ _) p₂  =⟨ ! (claim _ _ p₂) ⟩
    p₂                                      ∎  

-- Theorem 3.1
hedberg : {X : Type} → has-dec-eq X → is-set X
hedberg = pathHasConst→isSet ∘ discr→pathHasConst 

-- Definition 3.4
stable : Type → Type
stable X = ¬ (¬ X) → X

separated : Type → Type
separated X = (x₁ x₂ : X) → stable (x₁ == x₂)

-- Lemma 3.5
sep→set : {X : Type} → (separated X) → ({x₁ x₂ : X} → Funext {¬ (x₁ == x₂)} {Empty}) → is-set X
sep→set {X} sep ⊥-funext = pathHasConst→isSet isPc where
  isPc : pathHasConst X 
  isPc x₁ x₂ = f , c where 
    f : x₁ == x₂ → x₁ == x₂
    f = (sep x₁ x₂) ∘ (λ p np → np p)
    c : const f 
    c p₁ p₂ = 
      f p₁                        =⟨ idp ⟩
      (sep x₁ x₂) (λ np → np p₁)  =⟨ ap (sep x₁ x₂) 
                                     (⊥-funext _ _ λ np → Empty-elim {A = λ _ → np p₁ == np p₂} (np p₁)) ⟩
      (sep x₁ x₂) (λ np → np p₂)  =⟨ idp ⟩
      f p₂                        ∎ 

-- Definition 3.6
postulate 
  Trunc : Type → Type
  h-tr : (X : Type) → is-prop (Trunc X)
  ∣_∣ : {X : Type} → X → Trunc X
  rec : {X : Type} → {P : Type} → (is-prop P) → (X → P) → Trunc X → P

-- the propositional β rule is derivable:
trunc-β : {X : Type} → {P : Type} → (pp : is-prop P) → (f : X → P) → (x : X) → rec pp f ∣ x ∣ == f x 
trunc-β pp f x = prop-has-all-paths pp _ _

-- Lemma 3.7
module _ (X : Type) (P : Trunc X → Type) (h : (z : Trunc X) → is-prop (P z)) (k : (x : X) → P(∣ x ∣)) where
  total : Type
  total = Σ (Trunc X) P

  j : X → total
  j x = ∣ x ∣ , k x

  total-prop : is-prop total
  total-prop = Σ-level (h-tr X) h

  total-map : Trunc X → total
  total-map = rec total-prop j

  induction : (z : Trunc X) → P z 
  induction z = transport P (prop-has-all-paths (h-tr _) _ _) (snd (total-map z))

-- comment: Trunc is functorial
trunc-functorial : {X Y : Type} → (X → Y) → (Trunc X → Trunc Y)
trunc-functorial {X} {Y} f = rec (h-tr Y) (∣_∣ ∘ f)

-- Theorem 3.8
impred : {X : Type} → (Trunc X ↔₀₁ ((P : Type) → (is-prop P) → (X → P) → P))
impred {X} = one , two where
  one : Trunc X → (P : Type) → (is-prop P) → (X → P) → P 
  one z P p-prop f = rec p-prop f z
  two : ((P : Type) → (is-prop P) → (X → P) → P) → Trunc X
  two k = k (Trunc X) (h-tr _) ∣_∣

-- Definition 3.9 
splitSup : Type → Type
splitSup X = Trunc X → X

hseparated : Type → Type
hseparated X = (x₁ x₂ : X) → splitSup (x₁ == x₂)

-- Theorem 3.10
set-characterizations : {X : Type} → (pathHasConst X → is-set X) 
                                   × ((is-set X → hseparated X) 
                                   × (hseparated X → pathHasConst X))
set-characterizations {X} = one , two , three where
  one : pathHasConst X → is-set X
  one = pathHasConst→isSet
  two : is-set X → hseparated X
  two h = λ x₁ x₂ → rec (h x₁ x₂) (idf _)
  three : hseparated X → pathHasConst X
  three hsep x₁ x₂ = f , c where
    f = (hsep _ _) ∘ ∣_∣
    c = λ p₁ p₂ → f p₁              =⟨ idp ⟩
                  hsep _ _ (∣ p₁ ∣)  =⟨ ap (hsep _ _) (prop-has-all-paths (h-tr _) _ _) ⟩
                  hsep _ _ (∣ p₂ ∣)  =⟨ idp ⟩
                  f p₂              ∎ 

-- The rest of this section is only a replication of the arguments that we have given so far (for that reason, the proofs are not given in the article).
-- They do not directly follow from the statements that we have proved before, but they directly imply them.
-- Of course, replication of arguments is not a good style for a formalization -
-- we chose this "disadvantageous" order purely as we believe it led to a better presentation in the article.

-- Lemma 3.11
pathHasConst→isSet-local : {X : Type} → {x₀ : X} → ((y : X) → hasConst (x₀ == y)) → (y : X) → is-prop (x₀ == y)
pathHasConst→isSet-local {X} {x₀} pc y = all-paths-is-prop paths-equal  where
  claim : (y : X) → (p : x₀ == y) → p == ! (fst (pc _) idp) ∙ fst (pc _) p 
  claim .x₀ idp = ! (!-inv-l (fst (pc _) idp))
  paths-equal : (p₁ p₂ : x₀ == y) → p₁ == p₂
  paths-equal p₁ p₂ = 
    p₁                                  =⟨ claim _ p₁ ⟩
    ! (fst (pc _) idp) ∙ fst (pc _) p₁  =⟨ ap (λ q → (! (fst (pc x₀) idp)) ∙ q) (snd (pc y) p₁ p₂) ⟩ -- whiskering
    ! (fst (pc _) idp) ∙ fst (pc _) p₂  =⟨ ! (claim _ p₂) ⟩
    p₂                                  ∎  

-- Theorem 3.12
hedberg-local : {X : Type} → {x₀ : X} → ((y : X) → (x₀ == y) + ¬(x₀ == y)) → (y : X) → is-prop (x₀ == y)
hedberg-local {X} {x₀} dec = pathHasConst→isSet-local local-pathHasConst where
  local-pathHasConst : (y : X) → hasConst (x₀ == y)
  local-pathHasConst y with (dec y)
  local-pathHasConst y₁ | inl p  = (λ _ → p) , (λ _ _ → idp)
  local-pathHasConst y₁ | inr np = idf _ , (λ p → Empty-elim (np p))

-- Lemma 3.13
sep→set-local : {X : Type} → {x₀ : X} → ((y : X) → stable (x₀ == y)) → ({y : X} → Funext {¬ (x₀ == y)} {Empty}) → (y : X) → is-prop (x₀ == y)
sep→set-local {X} {x₀} sep ⊥-funext = pathHasConst→isSet-local is-pathHasConst where
  is-pathHasConst : (y : X) → hasConst (x₀ == y)
  is-pathHasConst y = f , c where
    f : x₀ == y → x₀ == y
    f = (sep y) ∘ (λ p np → np p)
    c : const f 
    c p₁ p₂ = 
      f p₁                    =⟨ idp ⟩
      (sep _) (λ np → np p₁)  =⟨ ap (sep _) 
                                     (⊥-funext _ _ λ np → Empty-elim {A = λ _ → np p₁ == np p₂} (np p₁)) ⟩
      (sep _) (λ np → np p₂)  =⟨ idp ⟩
      f p₂ ∎ 

-- Theorem 3.14
set-characterizations-local : {X : Type} → {x₀ : X} → 
  (((y : X) → hasConst (x₀ == y)) → (y : X) → is-prop (x₀ == y)) 
  × ((((y : X) → is-prop (x₀ == y)) → (y : X) → splitSup (x₀ == y)) 
  × (((y : X) → splitSup (x₀ == y)) → (y : X) → hasConst (x₀ == y)))
set-characterizations-local {X} {x₀} = one , two , three where
  one = pathHasConst→isSet-local
  two : ((y : X) → is-prop (x₀ == y)) → (y : X) → splitSup (x₀ == y) 
  two h y = rec (h y) (idf _) 
  three : ((y : X) → splitSup (x₀ == y)) → (y : X) → hasConst (x₀ == y) 
  three hsep y = f , c where
    f = (hsep _) ∘ ∣_∣
    c = λ p₁ p₂ → 
      f p₁           =⟨ idp ⟩
      (hsep _) ∣ p₁ ∣ =⟨ ap (hsep _) (prop-has-all-paths (h-tr _) _ _) ⟩
      (hsep _) ∣ p₂ ∣ =⟨ idp ⟩
      f p₂           ∎ 

