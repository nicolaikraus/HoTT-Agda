{-# OPTIONS --type-in-type --without-K #-}

{- Semi-simplicial types: A small demonstration that the "usual approach"
   works if we postulate the required coherence for the functorial behaviour
   of the "Skeleton" functor.
   This coherence can be achieved in a 2-level system, where the required 
   functor law can be shown to hold strictly. -}

module nicolai.SemiSimp.SStypes where

open import lib.Basics
open import lib.types.Unit
open import lib.types.Nat


-- This is the usual lemma about equality of pairs
-- (ideally, it should be imported from lib.types.Sigma )
pair== : {A : Set}{B : A → Set}{ab ab' : Σ A B}
     → (Σ (fst ab == fst ab') (λ α → transport B α (snd ab) == snd ab')) → ab == ab'
pair== {ab = (a , b)}{ab' = (.a , .b)} ( idp , idp ) = idp 

-- Finite types
data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (S n)
  fs : {n : ℕ} → Fin n → Fin (S n)

_>fin_ : {n : ℕ} → (i j : Fin n) → Set
fz >fin i = Empty
fs j >fin fz = ⊤
fs j >fin fs i = j >fin i


-- The category Δ₊ can be implemented such that the categorical laws
-- (unit, associativity) hold strictly (see my thesis).
-- Objects are natural numbers.

is-increasing : {m n : ℕ} → (Fin m → Fin n) → Set
is-increasing {m} {n} f = {j i : Fin m} → (j >fin i) → ((f j) >fin (f i))

-- hom-sets of Δ₊

_⇒+_ : ℕ → ℕ → Set
m ⇒+ n = Σ (Fin (S m) → Fin (S n)) is-increasing

-- composition:

_∘+_ : {l m n : ℕ} → (m ⇒+ n) → (l ⇒+ m) → (l ⇒+ n)
(g , p₂) ∘+ (f , p₁) = (λ i → g(f(i))) , (λ p → p₂ (p₁ p))


-- general lemmas (possibly in the library, should be added if they are not there)

trans-ap : {A B : Set} → (f : B → A) → (F : A → Set) → {b₁ b₂ : B} → (p : b₁ == b₂) → (x : F (f b₁)) → (transport (λ b → F (f b)) p x) == (transport F (ap f p) x)
trans-ap f F idp x = idp

trans-λ : {A B : Set} → (F : A → B → Set) → {a₁ a₂ : A} → (f : (b : B) → F a₁ b) → (p : a₁ == a₂) → transport (λ a → (b : B) → F a b) p f == λ b → transport (λ a → F a b) p (f b)
trans-λ F f idp = idp



-- Semi-simplicial types

-- SST j is the type of (j-1)-truncated semi-simplicial types, i.e. "Σ X₀ Σ ... Xⱼ₋₁"
SST : ℕ → Set

-- skeleton of a k-simplex: cells lower (!) than level j
Sk : {j : ℕ} → (SST j) → (k : ℕ) → Set

Skm : {j : ℕ} → (X : SST j) → {k₁ k₂ : ℕ} → (k₁ ⇒+ k₂) → Sk {j = j} X k₂ → Sk {j = j} X k₁

Skm-∘ : {j : ℕ} → (X : SST j) → {k₁ k₂ k₃ : ℕ} → (f : k₁ ⇒+ k₂) → (g : k₂ ⇒+ k₃) → (x : Sk X k₃) → Skm X (g ∘+ f) x == Skm X f (Skm X g x)


-- We postulate that Skm is coherent. This is automatic if we use equality with K.
-- We want to demonstrate that the "usual" construction of semi-simplicial types
-- (the one that many people have tried; see Herbelin's paper) works if we can
-- somehow get this coherence.
-- Of course, this is not new (see e.g. Herbelin).

postulate
  Skm-∘-coh :  {j : ℕ} → (X : SST j) → {k₀ k₁ k₂ k₃ : ℕ} → (h : k₀ ⇒+ k₁) → (f : k₁ ⇒+ k₂) → (g : k₂ ⇒+ k₃) → (x : Sk X k₃)
                → ((Skm-∘ X h (g ∘+ f) x) ∙ (ap (Skm X h) (Skm-∘ X f g x)))
                  ==
                  (Skm-∘ X (f ∘+ h) g x) ∙ (Skm-∘ X h f (Skm X g x)) 


SST O = ⊤
SST (S j) = Σ (SST j) λ X →
               Sk X j → Set

Sk {O} ⋆ k = ⊤
Sk {S j} (X , Fibʲ) k = Σ (Sk {j} X k) λ sk →
                           (f : j ⇒+ k) → Fibʲ (Skm X f sk)


Skm {O} ⋆ f sk = ⋆
Skm {S j} (X , Fibʲ) f (x , fibs) = Skm {j} X f x , λ g → transport Fibʲ (Skm-∘ X g f x) (fibs (f ∘+ g))

Skm-∘ {O} ⊤ f g x = idp
Skm-∘ {S j} (X , Fibʲ) {k₁} {k₂} {k₃} f g (x , fibs) = 

    Skm (X , Fibʲ) (g ∘+ f) (x , fibs)

  =⟨ idp ⟩

    Skm X (g ∘+ f) x , (λ h → transport Fibʲ (Skm-∘ X h (g ∘+ f) x) (fibs ((g ∘+ f) ∘+ h)))

  =⟨ pair== (Skm-∘ X f g x , idp) ⟩

    Skm X f (Skm X g x)  ,  transport (λ y → (h : j ⇒+ k₁) → Fibʲ (Skm X h y)) (Skm-∘ X f g x) (λ h → transport Fibʲ (Skm-∘ X h (g ∘+ f) x) (fibs ((g ∘+ f) ∘+ h)))

  =⟨ idp ⟩

    Skm X f (Skm X g x)  ,  transport  (λ y → (h : j ⇒+ k₁) → Fibʲ (Skm X h y))  (Skm-∘ X f g x)  (λ h → transport Fibʲ (Skm-∘ X h (g ∘+ f) x) (fibs ((g ∘+ f) ∘+ h)))

  =⟨ pair== (idp , trans-λ {B = j ⇒+ k₁} (λ y h → Fibʲ (Skm X h y))
                                       (λ h → transport Fibʲ (Skm-∘ X h (g ∘+ f) x) (fibs ((g ∘+ f) ∘+ h)))
                                       (Skm-∘ X f g x)) ⟩

    Skm X f (Skm X g x)  ,  (λ (h : j ⇒+ k₁) → transport  (λ y → Fibʲ (Skm X h y))  (Skm-∘ X f g x)  (transport Fibʲ (Skm-∘ X h (g ∘+ f) x) (fibs ((g ∘+ f) ∘+ h))))

  =⟨ pair== (idp , λ= (λ (h : j ⇒+ k₁) → trans-ap (Skm X h) Fibʲ (Skm-∘ X f g x) (transport Fibʲ (Skm-∘ X h (g ∘+ f) x) (fibs ((g ∘+ f) ∘+ h)))  )) ⟩ 

    Skm X f (Skm X g x)  ,  (λ (h : j ⇒+ k₁) → transport  Fibʲ (ap (Skm X h) (Skm-∘ X f g x))  (transport Fibʲ (Skm-∘ X h (g ∘+ f) x) (fibs ((g ∘+ f) ∘+ h))))

  =⟨ pair== (idp , λ= (λ (h : j ⇒+ k₁) → ! (trans-∙ ((Skm-∘ X h (g ∘+ f) x)) ((ap (Skm X h) (Skm-∘ X f g x))) _))) ⟩ 

    Skm X f (Skm X g x)  ,  (λ (h : j ⇒+ k₁) → transport  Fibʲ ((Skm-∘ X h (g ∘+ f) x) ∙ (ap (Skm X h) (Skm-∘ X f g x))) (fibs ((g ∘+ f) ∘+ h)))

  =⟨ pair== (idp , λ= (λ (h : j ⇒+ k₁) → ap (λ p → transport Fibʲ p (fibs ((g ∘+ f) ∘+ h))) (Skm-∘-coh X h f g _ ))) ⟩ -- crucial step that requires coherence! Easy with equality that has K.

    Skm X f (Skm X g x)  ,  (λ (h : j ⇒+ k₁) → transport Fibʲ  ((Skm-∘ X (f ∘+ h) g x) ∙ (Skm-∘ X h f (Skm X g x))) (fibs ((g ∘+ f) ∘+ h)))

  =⟨ pair== (idp ,  λ= (λ (h : j ⇒+ k₁) → trans-∙ (Skm-∘ X (f ∘+ h) g x) ((Skm-∘ X h f (Skm X g x))) (fibs ((g ∘+ f) ∘+ h))) ) ⟩  -- functoriality of transport; very simple. Uses funext.

    Skm X f (Skm X g x)  ,  (λ (h : j ⇒+ k₁) → transport Fibʲ  (Skm-∘ X h f (Skm X g x)) (transport Fibʲ (Skm-∘ X (f ∘+ h) g x) (fibs ((g ∘+ f) ∘+ h))))

  =⟨ idp ⟩  -- nothing happening here, only formatting

    Skm X f (Skm X g x) , (λ h → transport Fibʲ (Skm-∘ X h f (Skm X g x)) (transport Fibʲ (Skm-∘ X (f ∘+ h) g x) (fibs ((g ∘+ f) ∘+ h))))

  =⟨ idp ⟩ -- at this point, we use the strictness of Δ₊ in Agda!

    Skm X f (Skm X g x) , (λ h → transport Fibʲ (Skm-∘ X h f (Skm X g x)) (transport Fibʲ (Skm-∘ X (f ∘+ h) g x) (fibs (g ∘+ (f ∘+ h)))))

  =⟨ idp ⟩

    Skm (X , Fibʲ) f (Skm X g x , λ h' → transport Fibʲ (Skm-∘ X h' g x) (fibs (g ∘+ h')))

  =⟨ idp ⟩

    Skm (X , Fibʲ) f (Skm (X , Fibʲ) g (x , fibs))

  ∎


