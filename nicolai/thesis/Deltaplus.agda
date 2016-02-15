{-# OPTIONS --without-K #-}

module Deltaplus where

{- Chapter 9.2: Semi-Simplicial Types

   This file contains the definition of the index category 
   for semi-simplicial with judgmental categorical laws: Δ₊
   In other words, we check Proposition 9.2.1.

   We want to keep it independent of the other files,
   so we do not import anything. -}

{- For simplicity, we only use the lowest universe
   (totally sufficient) -} 
Type = Set 

-- the empty type
data Empty : Type where

-- the unit type
data ⊤ : Type where
  * : ⊤

-- the natural numbers
data ℕ : Type where
  O : ℕ
  S : (n : ℕ) → ℕ


{- Finite types: these are the 

   ===  OBJECTS of Δ₊ ===

-}
data Fin : ℕ → Type where
  fz : {n : ℕ} → Fin (S n)
  fs : {n : ℕ} → Fin n → Fin (S n)

-- >-relation on finite types
_>fin_ : {n : ℕ} → (i j : Fin n) → Set
fz >fin i = Empty
fs j >fin fz = ⊤
fs j >fin fs i = j >fin i

{- the proposition [we do not need to prove propositionality here, but 
   we could prove it easily] that a function is increasing;
   this is the tricky part: it needs to be done in a way which ensures
   that composition will behave nicely (strictly associative etc) later -}
is-increasing : {m n : ℕ} → (Fin m → Fin n) → Type
is-increasing {m} {n} f = {j i : Fin m} → (j >fin i) → ((f j) >fin (f i))


infixr 1 _,_

record Σ (A : Type) (B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst

{- Strictly increasing maps: these are the

   === MORPHISMS of Δ₊ ===

-}
_⇒+_ : ℕ → ℕ → Set
m ⇒+ n = Σ (Fin m → Fin n) is-increasing

_∘+_ : {l m n : ℕ} → (m ⇒+ n) → (l ⇒+ m) → (l ⇒+ n)
(g , p₂) ∘+ (f , p₁) = (λ i → g(f(i))) , (λ p → p₂ (p₁ p))


-- === IDENTITY MORPHISMS of Δ₊ ===

idΔ₊ : ∀ {n} → n ⇒+ n
idΔ₊ = (λ x → x) , (λ p → p)


{- Now, let us check that the categorical laws hold judgmentally.
   To do this, we use the usual notion of equality. -}

infix 3 _==_

data _==_ {A : Type} (a : A) : A → Type where
  idp : a == a


-- === IDENTITY LAWS ===

id-comp : ∀ {m n} → (f : m ⇒+ n) → (idΔ₊ ∘+ f) == f
id-comp f = idp

comp-id : ∀ {m n} → (f : m ⇒+ n) → (f ∘+ idΔ₊) == f
comp-id f = idp

-- === ASSOCIATIVITY LAW ===

comp-assoc : ∀ {i j m n} → (f : i ⇒+ j) → (g : j ⇒+ m) → (h : m ⇒+ n)
             → h ∘+ (g ∘+ f) == (h ∘+ g) ∘+ f
comp-assoc f g h = idp
