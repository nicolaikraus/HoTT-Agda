{-# OPTIONS --without-K #-}
module Preliminaries where

open import lib.Basics hiding (_⊔_)
open import lib.NType2

open import lib.types.Nat hiding (_+_)
open import lib.types.Pi
open import lib.types.Sigma hiding (×-comm)
open import lib.types.Unit
open import lib.types.TLevel

open import lib.types.Paths

-- Most of the contents of Chapter 2.1 are in the library, e.g.
-- natural numbers. We only do the following two adaptions here:

-- A readable notation for the join of universe levels.
infixr 8  _⊔_

_⊔_ : ULevel → ULevel → ULevel
_⊔_ = lmax

-- Addition operator adjustment.
_+_ : ℕ → ℕ → ℕ
a + b = b lib.types.Nat.+ a  -- n + 1 should mean S n (author preference)!

-- Chapter 2.2: We list the lemmata and other statements here.

-- Lemma 2.2.1
transport-is-comp : ∀ {i j} {X : Type i} {Y : Type j} → {x₁ x₂ : X} 
  → (h k : X → Y) → (t : x₁ == x₂) → (p : h x₁ == k x₁)
  → (transport _ t p) == ! (ap h t) ∙ p ∙ ap k t
transport-is-comp h k idp p = ! (∙-unit-r _)

-- Lemma 2.2.2 is in the library:
-- lib.NType2.raise-level-<T

-- Lemma 2.2.3 is in the library as well:
-- lib.types.Sigma.Σ-level

-- ... and so is Definition 2.2.4:
-- lib.NType2._-Type_

-- Lemma 2.2.6 as well:
-- lib.types.Pi.Π-level

-- Lemma 2.2.7:
-- lib.NType2.has-level-is-prop

module _ {i j} {A : Type i} {B : A → Type j} where
  module _ (h : (a : A) → is-contr (B a)) where

    -- Lemma 2.2.8 (i)
    Σ₂-contr : Σ A B ≃ A
    Σ₂-contr = Σ₂-Unit ∘e equiv-Σ-snd (λ _ → contr-equiv-Unit (h _))

    -- Lemma 2.2.8 (ii)
    Π₂-contr : Π A B ≃ ⊤
    Π₂-contr = Π₂-Unit ∘e equiv-Π-r (λ _ → contr-equiv-Unit (h _))

  module _ (h : is-contr A) where

    -- Lemma 2.2.9 (i)
    Σ₁-contr : Σ A B ≃ B (fst h)
    Σ₁-contr = Σ₁-Unit ∘e equiv-Σ-fst _ (snd (contr-equiv-Unit h ⁻¹)) ⁻¹

    -- Lemma 2.2.9 (ii)
    Π₁-contr : Π A B ≃ B (fst h)
    Π₁-contr = Π₁-Unit ∘e equiv-Π-l _ (snd (contr-equiv-Unit h ⁻¹)) ⁻¹

-- Lemma 2.2.10 - we refer to the library again
-- lib.types.Sigma.Σ-level
-- and
-- lib.types.Sigma.×-level

-- Lemma 2.2.11
-- lib.Equivalences.equiv-ap

-- Lemma 2.2.12 and Remark 2.2.13
module TT-AC {i j k : ULevel} {A : Type i} 
                          {B : A → Type j} 
                          {C : (Σ A B) → Type k} where
  -- the two types:
  ONE = (a : A) → Σ (B a) λ b → C (a , b)
  TWO = Σ ((a : A) -> B a) λ g → (a : A) → C (a , g a)

  -- the two canonical functions:
  f : ONE → TWO
  f one = fst ∘ one , snd ∘ one

  g : TWO → ONE
  g two = λ a → (fst two) a , (snd two) a

  -- the compositions are indeed pointwise judgmentally 
  -- the identity!
  f∘g : (two : TWO) → f (g two) == two
  f∘g two = idp

  g∘f : (one : ONE) → g (f one) == one
  g∘f one = idp


-- Lemma 2.2.14 is in the library:
-- lib.NType.pathto-is-contr
-- lib.NType.pathfrom-is-contr

-- This formalisation has a separated file for Pointed 
-- types, called 'Pointed.agda', which contains
-- (among other things) Definition 2.2.15
-- and Lemma 2.2.17

-- Definition 2.2.19
LEM : ∀ {i} → Type (lsucc i)
LEM {i} = (X : Type i) → is-prop X → Coprod X (¬ X)

LEM∞ : ∀ {i} → Type (lsucc i)
LEM∞ {i} = (X : Type i) → Coprod X (¬ X)


-- The following are some auxiliary lemmata/definitions
-- (not numbered in the thesis)

{- The (function) exponentiation operator. For convenience, we
   choose to define it via postcomposition in the recursion step. -}
infix 10 _^_
_^_ : ∀ {i} {A : Set i} → (A → A) → ℕ → A → A
f ^ 0   = idf _ 
f ^ S n = (f ^ n) ∘ f

-- Logical equivalence: maps in both directions
_↔_ : ∀ {i j} → Type i → Type j → Type (i ⊔ j)
X ↔ Y = (X → Y) × (Y → X)

-- Composition of ↔
_◎_ : ∀ {i j k} {X : Type i} {Y : Type j} {Z : Type k} → (X ↔ Y) → (Y ↔ Z) → (X ↔ Z) 
e₁ ◎ e₂ = fst e₂ ∘ fst e₁ , snd e₁ ∘ snd e₂


-- Subsection 2.3.3
module wtrunc where
  postulate
    -- Definition 2.3.2
    ∣∣_∣∣ : ∀ {i} → (X : Type i) → Type i
    tr-is-prop : ∀ {i} {X : Type i} → is-prop (∣∣ X ∣∣)
    ∣_∣ : ∀ {i} {X : Type i} → X → ∣∣ X ∣∣
    tr-rec : ∀ {i j} {X : Type i} {P : Type j} → (is-prop P) → (X → P) →   ∣∣ X ∣∣ → P

  -- Lemma 2.3.4
  -- the induction principle is derivable:
  module _ {i j : _} {X : Type i} {P : ∣∣ X ∣∣ → Type j} (h : (z : ∣∣ X ∣∣) → is-prop (P z)) (k : (x : X) → P ∣ x ∣) where

    total : Type (i ⊔ j)
    total = Σ ∣∣ X ∣∣ P

    jj : X → total
    jj x = ∣ x ∣ , k x

    total-prop : is-prop total
    total-prop = Σ-level tr-is-prop h

    total-map : ∣∣ X ∣∣ → total
    total-map = tr-rec total-prop jj

    tr-ind : (z : ∣∣ X ∣∣) → P z 
    tr-ind z = transport P (prop-has-all-paths tr-is-prop _ _) (snd (total-map z))

  -- Remark 2.3.5
  -- further, the propositional β-rule is derivable:
  trunc-β : ∀ {i j} {X : Type i} {P : Type j} → (pp : is-prop P) → (f : X → P) → (x : X) → tr-rec pp f ∣ x ∣ == f x 
  trunc-β pp f x = prop-has-all-paths pp _ _

  -- comment: Trunc is functorial
  trunc-functorial : ∀ {i} {j} {X : Type i} {Y : Type j} → (X → Y) → ∣∣ X ∣∣ → ∣∣ Y ∣∣
  trunc-functorial f = tr-rec tr-is-prop (∣_∣ ∘ f)

  -- Proposition 2.3.6
  impred : ∀ {i} {X : Type i} → ∣∣ X ∣∣ ↔ ((P : Type i) → is-prop P → (X → P) → P)
  impred {X = X} = (λ z P pp f → tr-rec pp f z) , λ h → h ∣∣ X ∣∣ tr-is-prop ∣_∣

  -- Proposition 2.3.6 (second part) - note that we use funext (in the form: Π preserves truncation level)
  impr-equiv : ∀ {i} {X : Type i} → is-equiv (fst (impred {X = X}))
  impr-equiv {i} {X} = is-eq (fst (impred {X = X})) (snd (impred {X = X})) 
    (λ top → prop-has-all-paths (Π-level (λ P → Π-level (λ pp → (Π-level (λ _ → pp))))) _ _)
    (λ z → prop-has-all-paths tr-is-prop _ _)


-- The rest of the file contains various useful lemmata
-- and definitions that are NOT in the thesis (at least 
-- not as numbered statements).


{- Since natural numbers and universe levels use
   different types, we require a translation operation. 
   We will only make use of this in chapter 7: Higher
   Homotopies in a Hierarchy of Univalent Universes. -}
｢_｣ : ℕ → ULevel
｢ 0   ｣ = lzero
｢ S n ｣ = lsucc ｢ n ｣
 

-- A trivial, but useful lemma. The only thing we do is hiding the arguments.
prop-eq-triv : ∀ {i} {P : Type i} → {p₁ p₂ : P} → is-prop P → p₁ == p₂
prop-eq-triv h = prop-has-all-paths h _ _

-- A second such useful lemma
second-comp-triv : ∀ {i} {X : Type i} → {P : X → Type i} → ((x : X) → is-prop (P x)) → (a b : Σ X P) → (fst a == fst b) → a == b
second-comp-triv {P = P} h a b q = pair= q (from-transp P q (prop-eq-triv (h (fst b))))

-- the following is the function which the univalence 
-- axiom postulates to be an equivalence
-- (we define it ourselves as we do not want to 
-- implicitly import the whole univalence library)
path-to-equiv : ∀ {i} {X : Type i} {Y : Type i} → X == Y → X ≃ Y
path-to-equiv {X = X} idp = ide X


-- some rather silly lemmata

delete-idp : ∀ {i} {X : Type i} → {x₁ x₂ : X} → (p q : x₁ == x₂) → (p ∙ idp == q) ≃ (p == q)
delete-idp idp q = ide _

add-path : ∀ {i} {X : Type i} → {x₁ x₂ x₃ : X} → (p q : x₁ == x₂) → (r : x₂ == x₃) → (p == q) == (p ∙ r == q ∙ r)
add-path idp q idp = transport (λ q₁ → (idp == q₁) == (idp == q ∙ idp)) {x = q ∙ idp} {y = q} (∙-unit-r _) idp

reverse-paths : ∀ {i} {X : Type i} → {x₁ x₂ : X} → (p : x₂ == x₁) → (q : x₁ == x₂) → (! p == q) ≃ (p == ! q)
reverse-paths p idp = 
  ! p == idp   ≃⟨ path-to-equiv (add-path _ _ _) ⟩
  ! p ∙ p == p ≃⟨ path-to-equiv (transport (λ p₁ → (! p ∙ p == p) == (p₁ == p)) (!-inv-l p) idp) ⟩
  idp == p     ≃⟨ !-equiv ⟩
  p == idp     ≃∎

switch-args : ∀ {i j k} {X : Type i} {Y : Type j} {Z : X → Y → Type k} → ((x : X) → (y : Y) → Z x y) ≃ ((y : Y) → (x : X) → Z x y)
switch-args = equiv f g h₁ h₂ where
  f = λ k y x → k x y
  g = λ i x y → i y x
  h₁ = λ _ → idp
  h₂ = λ _ → idp

-- another useful (but simple) lemma: if we have a proof of (x , y₁) == (x , y₂) and the type of x is a set, we get a proof of y₁ == y₂.
set-lemma : ∀ {i j} {X : Type i} → (is-set X) → {Y : X → Type j} → (x₀ : X) → (y₁ y₂ : Y x₀) → _==_ {A = Σ X Y} (x₀ , y₁) (x₀ , y₂) → y₁ == y₂
set-lemma {X = X} h {Y = Y} x₀ y₁ y₂ p = 
  y₁ =⟨ idp ⟩
  transport Y idp        y₁ =⟨ transport {A = x₀ == x₀} (λ q → y₁ == transport Y q y₁) 
                                 {x = idp} {y = ap fst p} 
                                 (prop-has-all-paths (h x₀ x₀) _ _) 
                                 idp ⟩
  transport Y (ap fst p) y₁ =⟨ snd-of-p ⟩
  y₂ ∎ where
    pairs : =Σ {B = Y} (x₀ , y₁) (x₀ , y₂)
    pairs = <– (=Σ-eqv _ _) p

    paov : y₁ == y₂ [ Y ↓ fst (pairs) ]
    paov = snd pairs

    snd-of-p : transport Y (ap fst p) y₁ == y₂
    snd-of-p = to-transp paov

×-comm : ∀ {i j} {A : Type i} {B : Type j} → (A × B) ≃ (B × A)
×-comm = equiv (λ {(a , b) → (b , a)})
               (λ {(b , a) → (a , b)})
               (λ _ → idp) (λ _ → idp)

Σ-comm-snd : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
           → Σ (Σ A B) (λ ab → C (fst ab)) ≃ Σ (Σ A C) (λ ac → B (fst ac))
Σ-comm-snd {A = A} {B} {C} = 
  Σ (Σ A B) (λ ab → C (fst ab))  ≃⟨ Σ-assoc ⟩
  Σ A (λ a → B a × C a)          ≃⟨ equiv-Σ-snd (λ _ → ×-comm) ⟩
  Σ A (λ a → C a × B a)          ≃⟨ Σ-assoc ⁻¹ ⟩
  Σ (Σ A C) (λ ac → B (fst ac))  ≃∎

flip : ∀ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k}
       → ((a : A) (b : B) → C a b) → ((b : B) (a : A) → C a b)
flip = –> (curry-equiv ∘e equiv-Π-l _ (snd ×-comm) ∘e curry-equiv ⁻¹)


module _ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k} where
  ↓-cst→app-equiv : {x x' : A} {p : x == x'} {u : (b : B) → C x b} {u' : (b : B) → C x' b}
                  → ((b : B) → u b == u' b [ (λ x → C x b) ↓ p ]) ≃ (u == u' [ (λ x → (b : B) → C x b) ↓ p ])
  ↓-cst→app-equiv {p = idp} = equiv λ= app= (! ∘ λ=-η) (λ= ∘ app=-β)

module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} where
  ↓-cst2-equiv : {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v : B y}
    → (u == v [ B ↓ p ]) ≃ (u == v [ (λ xy → B (fst xy)) ↓ (pair= p q) ])
  ↓-cst2-equiv idp idp = ide _

module _ {i} {A B : Type i} (e : A ≃ B) {u : A} {v : B} where
  ↓-idf-ua-equiv : (–> e u == v) ≃ (u == v [ (λ x → x) ↓ (ua e) ])
  ↓-idf-ua-equiv = to-transp-equiv _ _ ⁻¹ ∘e (_ , pre∙-is-equiv (ap (λ z → z u) (ap coe (ap-idf (ua e)) ∙ ap –> (coe-equiv-β e))))


-- On propositions, equivalence coincides with logical equivalence.
module _ {i j} {A : Type i} {B : Type j} where
  prop-equiv' : (B → is-prop A) → (A → is-prop B) → (A → B) → (B → A) → A ≃ B
  prop-equiv' h k f g = equiv f g (λ b → prop-has-all-paths (k (g b)) _ _)
                                  (λ a → prop-has-all-paths (h (f a)) _ _)

  prop-equiv : is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
  prop-equiv h k f g = prop-equiv' (cst h) (cst k) f g

-- Equivalent types have equivalent truncatedness propositions.
equiv-level : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂}
            → A ≃ B → has-level n A ≃ has-level n B
equiv-level u = prop-equiv has-level-is-prop
                           has-level-is-prop
                           (equiv-preserves-level u)
                           (equiv-preserves-level (u ⁻¹))

prop-equiv-inhab-to-contr : ∀ {i} {A : Type i} → is-prop A ≃ (A → is-contr A)
prop-equiv-inhab-to-contr = prop-equiv is-prop-is-prop
                                       (Π-level (λ _ → is-contr-is-prop))
                                       (flip inhab-prop-is-contr)
                                       inhab-to-contr-is-prop

