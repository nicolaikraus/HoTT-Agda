{-# OPTIONS --without-K #-}

open import library.Basics hiding (Type ; Σ)
open import library.types.Sigma

module Sec2preliminaries where

-- is-prop, is-contr, is-set, has-dec-eq exist in library.Basicss

-- Let us redefine Type and Σ so that they only refer to the lowest universe.
Type = Type₀
Σ = library.Basics.Σ {lzero} {lzero} 

_+_ : Type → Type → Type
X + Y = Coprod X Y

const : {X Y : Type} → (f : X → Y) → Type
const {X} f = (x₁ x₂ : X) → (f x₁) == (f x₂)

hasConst : Type → Type
hasConst X = Σ (X → X) const

pathHasConst : Type → Type
pathHasConst X = (x₁ x₂ : X) → hasConst (x₁ == x₂)

LEM : Type₁
LEM = (P : Type) → is-prop P → P + (¬ P)

LEM∞ : Type₁
LEM∞ = (X : Type) → X + (¬ X)

Funext : {X Y : Type} → Type
Funext {X} {Y} = (f g : X → Y) → ((x : X) → (f x) == (g x)) → f == g


-- In the rest of this file, we define several auxiliary notations or lemmata that are not mentioned 
-- explicitly in the article but are somewhat self-explaining.

-- for convenience, we also define ↔ to mean logical equivalence (maps in both directions)
_↔_ : Type → Type → Type
X ↔ Y = (X → Y) × (Y → X)

-- we define it for types in the higher universe separately 
-- (because most of the time, we only need the lowest universe and do not want to carry around indices)
_↔₀₁_ : Type → Type₁ → Type₁
A ↔₀₁ B = (A → B) × (B → A)

_↔₁₁_ : Type₁ → Type₁ → Type₁
X ↔₁₁ Y = (X → Y) × (Y → X)

-- composition of ↔
_◎_ : {X Y Z : Type} → (X ↔ Y) → (Y ↔ Z) → (X ↔ Z) 
e₁ ◎ e₂ = fst e₂ ∘ fst e₁ , snd e₁ ∘ snd e₂

-- A trivial, but useful lemma. The only thing we do is hiding the arguments.
prop-eq-triv : {P : Type} → {p₁ p₂ : P} → is-prop P → p₁ == p₂
prop-eq-triv h = prop-has-all-paths h _ _

-- A second such useful lemma
second-comp-triv : {X : Type} → {P : X → Type} → ((x : X) → is-prop (P x)) → (a b : Σ X P) → (fst a == fst b) → a == b
second-comp-triv {X} {P} h a b q = pair= q (from-transp P q (prop-eq-triv (h (fst b))))

open import library.types.Pi

-- Note that this lemma needs function extensionality (we use Π-level).
neutral-codomain : {X : Type} → {Y : X → Type} → ((x : X) → is-contr (Y x)) → Π X Y ≃ Unit
neutral-codomain = contr-equiv-Unit ∘ Π-level

-- the following is the function which the univalence axiom postulates to be an equivalence
-- (we define it ourselves as we do not want to implicitly import the whole univalence library)
path-to-equiv : {X Y : Type} → X == Y → X ≃ Y
path-to-equiv {X} idp = ide X

-- some rather silly lemmata

delete-idp : {X : Type} → {x₁ x₂ : X} → (p q : x₁ == x₂) → (p ∙ idp == q) ≃ (p == q)
delete-idp idp q = ide _

add-path : {X : Type} → {x₁ x₂ x₃ : X} → (p q : x₁ == x₂) → (r : x₂ == x₃) → (p == q) == (p ∙ r == q ∙ r)
add-path idp q idp = transport (λ q₁ → (idp == q₁) == (idp == q ∙ idp)) {x = q ∙ idp} {y = q} (∙-unit-r _) idp

open import library.types.Paths

reverse-paths : {X : Type} → {x₁ x₂ : X} → (p : x₂ == x₁) → (q : x₁ == x₂) → (! p == q) ≃ (p == ! q)
reverse-paths p idp = 
  ! p == idp   ≃⟨ path-to-equiv (add-path _ _ _) ⟩
  ! p ∙ p == p ≃⟨ path-to-equiv (transport (λ p₁ → (! p ∙ p == p) == (p₁ == p)) (!-inv-l p) idp) ⟩
  idp == p     ≃⟨ !-equiv ⟩
  p == idp     ≃∎

switch-args : {X Y : Type} → {Z : X → Y → Type} → ((x : X) → (y : Y) → Z x y) ≃ ((y : Y) → (x : X) → Z x y)
switch-args = equiv f g h₁ h₂ where
  f = λ k y x → k x y
  g = λ i x y → i y x
  h₁ = λ _ → idp
  h₂ = λ _ → idp


-- another useful (but simple) lemma: if we have a proof of (x , y₁) == (x , y₂) and the type of x is a set, we get a proof of y₁ == y₂.
set-lemma : {X : Type} → (is-set X) → {Y : X → Type} → (x₀ : X) → (y₁ y₂ : Y x₀) → _==_ {A = Σ X Y} (x₀ , y₁) (x₀ , y₂) → y₁ == y₂
set-lemma {X} h {Y} x₀ y₁ y₂ p = 
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

