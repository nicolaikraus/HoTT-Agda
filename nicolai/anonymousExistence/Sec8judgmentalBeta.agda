{-# OPTIONS --without-K #-}

open import library.Basics

open import library.types.Sigma
open import library.types.Bool
open import library.types.Truncation hiding (Trunc)

module Sec8judgmentalBeta where

{- 
Recall Definition 3.6:

postulate 
  Trunc : Type → Type
  h-tr : (X : Type) → is-prop (Trunc X)
  ∣_∣ : {X : Type} → X → Trunc X
  rec : {X : Type} → {P : Type} → (is-prop P) → (X → P) → Trunc X → P

We now redefine the propositional truncation so that rec has the judgmental β rule.
We use the library implementation (library.types.Truncation).
However, we still only talk about the *propositional* truncation (not the more general n-truncation).

This file is independent of all the previous files of the article. 
For the part in Subsection 9.4, we need some statements for for than the lowest universe. Therefore, 
we choose to be more careful about universe levels.
-}

Trunc : ∀ {i} → Type i → Type i
Trunc = library.types.Truncation.Trunc ⟨-1⟩ 

h-tr : ∀ {i} → (X : Type i) → is-prop (Trunc X)
h-tr X = Trunc-level

∣_∣ : ∀ {i} → {X : Type i} → X → Trunc X
∣_∣ = [_]

rec : ∀ {i j} → {X : Type i} → {P : Type j} → (is-prop P) → (X → P) → Trunc X → P
rec = Trunc-rec

ind : ∀ {i j} → {X : Type i} → {P : Trunc X → Type j} → ((z : Trunc X) → is-prop (P z)) → ((x : X) → P ∣ x ∣) → (z : Trunc X) → P z
ind = Trunc-elim 


-- Subsection 8.1

-- Theorem 8.1
interval : Type₀
interval = Trunc Bool

i₁ : interval
i₁ = ∣ true ∣

i₂ : interval
i₂ = ∣ false ∣

seg : i₁ == i₂
seg = prop-has-all-paths (h-tr _) _ _

-- We prove that the interval has the "correct" recursion principle:
module interval {i} {Y : Type i} (y₁ y₂ : Y) (p : y₁ == y₂) where

  g : Bool → Σ Y λ y → y₁ == y
  g true = (y₁ , idp)
  g false = (y₂ , p)

  ĝ : interval → Σ Y λ y → y₁ == y
  ĝ = rec (contr-is-prop (pathfrom-is-contr _)) g

  f : interval → Y
  f = fst ∘ ĝ

  f-i₁ : f i₁ == y₁
  f-i₁ = idp

  f-i₂ : f i₂ == y₂
  f-i₂ = idp

  f-seg : ap f seg == p
  f-seg = 
    ap f seg                  =⟨ idp ⟩
    ap (fst ∘ ĝ) seg          =⟨ ! (∘-ap _ _ _) ⟩
    (ap fst) (ap ĝ seg)       =⟨ ap (ap fst) (prop-has-all-paths (contr-is-set (pathfrom-is-contr _) _ _) _ _) ⟩
    (ap fst) (pair= p po-aux) =⟨ fst=-β p _ ⟩
    p                         ∎ where
      po-aux : idp == p [ _==_ y₁ ↓ p ]
      po-aux = from-transp (_==_ y₁) p (trans-pathfrom p idp)


-- Everything again outside the module: 

interval-rec : ∀ {i} → {Y : Type i} → (y₁ y₂ : Y) → (p : y₁ == y₂) → (interval → Y) 
interval-rec  = interval.f

interval-rec-i₁ : ∀ {i} → {Y : Type i} → (y₁ y₂ : Y) → (p : y₁ == y₂) → (interval-rec y₁ y₂ p) i₁ == y₁
interval-rec-i₁ = interval.f-i₁  -- or: λ _ _ _ → idp

interval-rec-i₂ : ∀ {i} →  {Y : Type i} → (y₁ y₂ : Y) → (p : y₁ == y₂) → (interval-rec y₁ y₂ p) i₂ == y₂
interval-rec-i₂ = interval.f-i₂  -- or: λ _ _ _ → idp

interval-rec-seg : ∀ {i} → {Y : Type i} → (y₁ y₂ : Y) → (p : y₁ == y₂) → ap (interval-rec y₁ y₂ p) seg == p
interval-rec-seg = interval.f-seg



-- Subsection 8.2

-- Lemma 8.2 (Shulman) / Corollary 8.3
interval→funext : ∀ {i j} → {X : Type i} → {Y : Type j} → (f g : (X → Y)) → ((x : X) → f x == g x) → f == g
interval→funext {X = X} {Y = Y} f g hom = ap i-x seg where

  x-i : X → interval → Y
  x-i x = interval-rec (f x) (g x) (hom x)

  i-x : interval → X → Y
  i-x i x = x-i x i

-- Thus, function extensionality holds automatically.

open import library.types.Pi

-- Subsection 8.3

-- We use the definitions from Section 5, but we re-define them as our definition of "Trunc" has chanced
factors : ∀ {i j} → {X : Type i} → {Y : Type j} → (f : X → Y) → Type (lmax i j)
factors {X = X} {Y = Y} f = Σ (Trunc X → Y) λ f' → (x : X) → f' ∣ x ∣ == f x


-- Theorem 8.4 - note the line   proof' = λ _ → idp
judgmental-factorr : ∀ {i j} → {X : Type i} → {Y : Type j} → (f : X → Y) → factors f → factors f
judgmental-factorr {X = X} {Y = Y} f (f₂ , proof) = f' , proof' where

  g : X → (z : Trunc X) → Σ Y λ y → y == f₂ z
  g x = λ z → f x , f x     =⟨ ! (proof _) ⟩
                    f₂ ∣ x ∣ =⟨ ap f₂ (prop-has-all-paths (h-tr _) _ _) ⟩
                    f₂ z    ∎

  g-codom-prop : is-prop ((z : Trunc X) → Σ Y λ y → y == f₂ z)
  g-codom-prop = contr-is-prop (Π-level (λ z → pathto-is-contr _))

  ĝ : Trunc X → (z : Trunc X) → Σ Y λ y → y == f₂ z
  ĝ = rec g-codom-prop g

  f' : Trunc X → Y
  f' = λ z → fst (ĝ z z)

  proof' : (x : X) → f' ∣ x ∣ == f x
  proof' = λ _ → idp

-- Theorem 8.5 - we need the induction principle, but with that, it is actually simpler than the previous construction.
-- Still, it is nearly a replication.
factors-dep : ∀ {i j} → {X : Type i} → {Y : Trunc X → Type j} → (f : (x : X) → (Y ∣ x ∣)) → Type (lmax i j)
factors-dep {X = X} {Y = Y} f = Σ ((z : Trunc X) → Y z) λ f₂ → ((x : X) → f x == f₂ ∣ x ∣)

judgmental-factorr-dep : ∀ {i j} → {X : Type i} → {Y : Trunc X → Type j} 
  → (f : (x : X) → Y ∣ x ∣) → factors-dep {X = X} {Y = Y} f → factors-dep {X = X} {Y = Y} f
judgmental-factorr-dep {X = X} {Y = Y} f (f₂ , proof) = f' , proof' where

  g : (x : X) → Σ (Y ∣ x ∣) λ y → y == f₂ ∣ x ∣ 
  g x = f x , proof x

  g-codom-prop : (z : Trunc X) → is-prop (Σ (Y z) λ y → y == f₂ z)
  g-codom-prop z = contr-is-prop (pathto-is-contr _)

  ĝ : (z : Trunc X) →  Σ (Y z) λ y → y == f₂ z
  ĝ = ind g-codom-prop g

  f' : (z : Trunc X) → Y z
  f' = fst ∘ ĝ 

  proof' : (x : X) → f' ∣ x ∣ == f x
  proof' x = idp 


-- Subsection 8.4

-- The content of this section is partially taken from an earlier formalization by the first-named author;
-- see 
--
--       http://homotopytypetheory.org/2013/10/28/
--
-- for a discussion and
--
--       http://red.cs.nott.ac.uk/~ngk/html-trunc-inverse/trunc-inverse.html
--
-- for a formalization (the slightly simpler formalization that is mentioned in the article).

-- Definition 8.6
-- Pointed types
Type• : ∀ {i} → Type (lsucc i)
Type• {i} = Σ (Type i) (idf _)

module _ {i} (X : Type• {i}) where
  base = fst X
  pt   = snd X

  -- We have already used the pathto-types a couple of times. 
  -- Let's introduce a name for those that work with pointed types:
  pathto : Type (lsucc i)
  pathto = Σ (Type• {i}) (λ Y → Y == X) 

  -- As it is well-known, these type is contractible and thereby propositional:
  pathto-prop : is-prop pathto
  pathto-prop = contr-is-prop (pathto-is-contr X)


-- Definition 8.7
is-transitive : ∀ {i} → Type i → Type (lsucc i)
is-transitive {i} X = (x₁ x₂ : X) → _==_ {A = Type•} (X , x₁) (X , x₂)

-- Example 8.8
module dec-trans {i} (X : Type i) (dec : has-dec-eq X) where

  module _ (x₁ x₂ : X) where

    -- I define a function X → X that switches x and x₀.
    switch : X → X
    switch = λ y → match dec y x₁ 
                     withl (λ _ → x₂) 
                     withr (λ _ → match dec y x₂
                                    withl (λ _ → x₁)
                                    withr (λ _ → y))

    -- Rather tedious to prove, but completely straightforward:
    -- this map is its own inverse.
    switch-selfinverse : (y : X) → switch (switch y) == y
    switch-selfinverse y with dec y x₁
    switch-selfinverse y | inl _ with dec x₂ x₁
    switch-selfinverse y | inl y-x₁  | inl x-x₁ = x-x₁ ∙ ! y-x₁
    switch-selfinverse y | inl _     | inr _ with dec x₂ x₂
    switch-selfinverse y | inl y-x₁  | inr _     | inl _ = ! y-x₁
    switch-selfinverse y | inl _     | inr _     | inr ¬x₂-x₂ = Empty-elim {A = λ _ → x₂ == y} (¬x₂-x₂ idp)
    switch-selfinverse y | inr _ with dec y x₂ 
    switch-selfinverse y | inr _     | inl _ with dec x₂ x₁ 
    switch-selfinverse y | inr ¬x₂-x₁ | inl y-x₂  | inl x₂-x₁ = Empty-elim (¬x₂-x₁ (y-x₂ ∙ x₂-x₁))
    switch-selfinverse y | inr _     | inl _     | inr _ with dec x₁ x₁ 
    switch-selfinverse y | inr _     | inl y-x₂  | inr _ | inl _ = ! y-x₂
    switch-selfinverse y | inr _     | inl _     | inr _ | inr ¬x₁-x₁ = Empty-elim {A = λ _ → _ == y} (¬x₁-x₁ idp) 
    switch-selfinverse y | inr _     | inr _ with dec y x₁
    switch-selfinverse y | inr ¬y-x₁ | inr _     | inl y-x₁ = Empty-elim {A = λ _ → x₂ == y} (¬y-x₁ y-x₁)
    switch-selfinverse y | inr _     | inr _     | inr _  with dec y x₂
    switch-selfinverse y | inr _     | inr ¬y-x₂ | inr _ | inl y-x₂ = Empty-elim {A = λ _ → x₁ == y} (¬y-x₂ y-x₂)
    switch-selfinverse y | inr _     | inr _     | inr _ | inr _ = idp

    switch-maps : switch x₂ == x₁
    switch-maps with dec x₂ x₁ 
    switch-maps | inl x₂-x₁ = x₂-x₁
    switch-maps | inr _ with dec x₂ x₂
    switch-maps | inr _ | inl _ = idp
    switch-maps | inr _ | inr ¬x-x = Empty-elim {A = λ _ → x₂ == x₁} (¬x-x idp)

    -- switch is an equivalence
    switch-eq : X ≃ X
    switch-eq = equiv switch switch 
                      switch-selfinverse switch-selfinverse

  -- X is transitive:
  is-trans : is-transitive X
  is-trans x₁ x₂  = pair= (ua X-X) x₁-x₂ where
    X-X : X ≃ X
    X-X = switch-eq x₂ x₁
    x₁-x₂ : PathOver (idf (Type i)) (ua X-X) x₁ x₂
    x₁-x₂ = ↓-idf-ua-in X-X (switch-maps x₂ x₁)


-- Example 8.8 addendum: ℕ is transitive.
open import library.types.Nat

ℕ-trans : is-transitive ℕ
ℕ-trans = dec-trans.is-trans ℕ ℕ-has-dec-eq 


-- Example 9.9
-- (Note that this does not need the univalence axiom)

-- preparation
path-trans-aux : ∀ {i} → (X : Type i) → (x₁ x₂ x₃ : X) → (x₂ == x₃) 
  → (p₁₂ : x₁ == x₂) → (p₁₃ : x₁ == x₃) → _==_ {A = Type•} (x₁ == x₂ , p₁₂) (x₁ == x₃ , p₁₃)
path-trans-aux X x₁ .x₁ .x₁ p idp idp = idp

-- the lemma
path-trans : ∀ {i} → (X : Type i) → (x₁ x₂ : X) → is-transitive (x₁ == x₂)
path-trans X x₁ x₂ = path-trans-aux X x₁ x₂ x₂ idp

-- In particular, the lemma works for loop spaces.
-- We define them as follows:
Ω : ∀ {i} → Type• {i} → Type• {i}
Ω (X , x) = (x == x , idp)

-- We choose precomposition here - whether the function exponentiation operator is more
-- convenient to use with pre- or postcomposition depends on the concrete case.
infix 10 _^_
_^_ : ∀ {i} {A : Set i} → (A → A) → ℕ → A → A
f ^ 0   = idf _ 
f ^ S n = f ∘ f ^ n

loop-trans : ∀ {i} → (X : Type• {i}) → (n : ℕ) → is-transitive (fst ((Ω ^ (1 + n)) X))
loop-trans {i} X n = path-trans type point point where 

  type : Type i
  type = fst ((Ω ^ n) X)

  point : type
  point = snd ((Ω ^ n) X)


-- Example 8.10 and 8.11 
-- (not formalized)


module constr-myst {i} (X : Type i) (x₀ : X) (t : is-transitive X) where

  f : X → Type• {i}
  f x = (X , x)

  f'' : Trunc X → Type• {i}
  f'' _ = (X , x₀)
  
  f-fact : factors f
  f-fact = f'' , (λ x → t x₀ x)

  f' : Trunc X → Type• {i}
  f' = fst (judgmental-factorr f f-fact)

-- Theorem 9.12
-- the myst function:
  myst : (z : Trunc X) → fst (f' z)
  myst = snd ∘ f'

  check : (x : X) → myst ∣ x ∣ == x
  check x = idp

  myst-∣_∣-is-id : myst ∘ ∣_∣ == idf X
  myst-∣_∣-is-id = λ= λ x → idp


-- Let us do it explicitly for ℕ:
open import library.types.Nat

myst-ℕ = constr-myst.myst ℕ 0 (dec-trans.is-trans ℕ ℕ-has-dec-eq)

myst-∣_∣-is-id : (n : ℕ) → myst-ℕ ∣ n ∣ == n
myst-∣_∣-is-id n = idp

test : myst-ℕ ∣ 17 ∣ == 17
test = idp
