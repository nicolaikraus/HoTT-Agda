{-# OPTIONS --without-K #-}

open import library.Basics hiding (Type ; Σ ; S)
open import library.types.Sigma

open import Sec2preliminaries 
open import Sec3hedberg
open import Sec4hasConstToSplit
open import Sec5factorConst
open import Sec6hasConstToDecEq
open import Sec7populatedness


module Sec8taboos where


-- Subsection 8.1

all-hasConst : Type₁
all-hasConst = (X : Type) → hasConst X

-- Theorem 8.1
module functional-subrelation (ac : all-hasConst) (X : Type) (R : X × X → Type) where

  all-sets : (Y : Type) → is-set Y
  all-sets Y = pathHasConst→isSet (λ y₁ y₂ → ac _)

  R₋ : (x : X) → Type
  R₋ x = Σ X λ y → R(x , y)

  k : (x : X) → (R₋ x) → (R₋ x)
  k x = fst (ac _)

  kc : (x : X) → const (k x)
  kc x = snd (ac _)

  S : X × X → Type
  S (x , y) = Σ (R(x , y)) λ a → 
                (y , a) == k x (y , a)

  -- the relation S
  S₋ : (x : X) → Type
  S₋ x = Σ X λ y → S(x , y)

  -- fix kₓ is equivalent to Sₓ
  -- This is just Σ-assoc. We try to make it more readable by adding some (trivial) steps.
  fixk-S : (x : X) → (fix (k x)) ≃ S₋ x
  fixk-S x = 
      (fix (k x))                                           ≃⟨ ide _ ⟩
      (Σ (Σ X λ y → R(x , y)) λ a → a == k x a)             ≃⟨ Σ-assoc ⟩
      (Σ X λ y → Σ (R(x , y)) λ r → (y , r) == k x (y , r)) ≃⟨ ide _ ⟩
      (S₋ x)                                                ≃∎

  -- claim (0)
  subrelation : (x y : X) → S(x , y) →  R(x , y)
  subrelation x y (r , _) = r

   -- claim (1)
  prop-Sx : (x : X) → is-prop (S₋ x)
  prop-Sx x = equiv-preserves-level {A = fix (k x)} {B = (S₋ x)} (fixk-S x) (fixed-point _ (kc x)) 

  -- claim (2)
  same-domain : (x : X) → (R₋ x) ↔ (S₋ x)
  same-domain x = rs , sr where
    rs : (R₋ x) → (S₋ x)
    rs a = –> (fixk-S x) (to-fix (k x) (kc x) a)
    sr : (S₋ x) → (R₋ x)
    sr (y , r , _) = y , r

  -- claim (3) 
  prop-S : (x y : X) → is-prop (S (x , y))
  prop-S x y = all-paths-is-prop all-paths where
    all-paths : (s₁ s₂ : S(x , y)) → s₁ == s₂
    all-paths s₁ s₂ = ss where

      yss : (y , s₁) == (y , s₂)
      yss = prop-has-all-paths (prop-Sx x) _ _

      ss : s₁ == s₂
      ss = set-lemma (all-sets _) y s₁ s₂ yss


-- intermediate definition
-- see the caveat about the notion 'epimorphism' in the article
is-split-epimorphism : {U V : Type} → (U → V) → Type
is-split-epimorphism {U} {V} e = Σ (V → U) λ s → (v : V) → e (s v) == v

is-epimorphism : {U V : Type} → (U → V) → Type₁
is-epimorphism {U} {V} e = (W : Type) → (f g : V → W) → ((u : U) → f (e u) == g (e u)) → (v : V) → f v == g v

-- Lemma 8.2
path-trunc-epi→set : {Y : Type} → ((y₁ y₂ : Y) → is-epimorphism (∣_∣ {X = y₁ == y₂})) → is-set Y
path-trunc-epi→set {Y} path-epi = reminder special-case where

  f : (y₁ y₂ : Y) → Trunc (y₁ == y₂) → Y
  f y₁ _ _ = y₁

  g : (y₁ y₂ : Y) → Trunc (y₁ == y₂) → Y
  g _ y₂ _ = y₂

  special-case : (y₁ y₂ : Y) → Trunc (y₁ == y₂) → y₁ == y₂
  special-case y₁ y₂ = path-epi y₁ y₂ Y (f y₁ y₂) (g y₁ y₂) (idf _)

  reminder : hseparated Y → is-set Y
  reminder = fst set-characterizations ∘ snd (snd set-characterizations)

-- Theorem 8.3 (1)
all-split→all-deceq : ((X : Type) → is-split-epimorphism (∣_∣ {X = X})) → (X : Type) → has-dec-eq X
all-split→all-deceq all-split = all-hasConst→dec-eq ac where
  ac : (X : Type) → hasConst X
  ac X = snd hasConst↔splitSup (fst (all-split X))

-- Theorem 8.3 (2)
all-epi→all-set : ((X : Type) → is-epimorphism (∣_∣ {X = X})) → (X : Type) → is-set X
all-epi→all-set all-epi X = path-trunc-epi→set (λ y₁ y₂ → all-epi (y₁ == y₂))


-- Subsection 8.2

-- Lemma 8.4, first proof
pop-splitSup-1 : {X : Type} → Pop (splitSup X)
pop-splitSup-1 {X} f c = to-fix f c (hasConst→splitSup (g , gc)) where

  g : X → X
  g x = f (λ _ → x) ∣ x ∣

  gc : const g
  gc x₁ x₂ = 
    g x₁               =⟨ idp ⟩
    f (λ _ → x₁) ∣ x₁ ∣ =⟨ ap (λ k → k ∣ x₁ ∣) (c (λ _ → x₁) (λ _ → x₂)) ⟩
    f (λ _ → x₂) ∣ x₁ ∣ =⟨ ap (f (λ _ → x₂)) (prop-has-all-paths (h-tr X) ∣ x₁ ∣ ∣ x₂ ∣) ⟩
    f (λ _ → x₂) ∣ x₂ ∣ =⟨ idp ⟩
    g x₂               ∎  

-- Lemma 8.4, second proof
pop-splitSup-2 : {X : Type} → Pop (splitSup X)
pop-splitSup-2 {X} = snd (pop-alt₂ {splitSup X}) get-P where
  get-P : (P : Type) → is-prop P → splitSup X ↔ P → P
  get-P P pp (hstp , phst) = hstp free-hst where

    xp : X → P
    xp x = hstp (λ _ → x)

    zp : Trunc X → P
    zp = rec pp xp

    free-hst : splitSup X
    free-hst z = phst (zp z) z

-- Lemma 8.5, third proof
pop-splitSup-3 : {X : Type} → Pop (splitSup X)
pop-splitSup-3 {X} = snd pop-alt translation where

  translation-aux : splitSup (splitSup X) → splitSup X
  translation-aux = λ hsthst z → hsthst (trunc-functorial {X = X} {Y = splitSup X} (λ x _ → x) z) z

  translation : Trunc (splitSup (splitSup X)) → Trunc (splitSup X)
  translation = trunc-functorial translation-aux

-- Theorem 8.5
module thm85 where

  One = (X : Type) → Pop X → Trunc X

  Two = (X : Type) → Trunc (splitSup X)

  Three = (P : Type) → is-prop P → (Y : P → Type) → ((p : P) → Trunc (Y p)) → Trunc ((p : P) → Y p)

  Four = (X Y : Type) → (X → Y) → (Pop X → Pop Y)


  One→Two : One → Two
  One→Two poptr X = poptr (splitSup X) pop-splitSup-1 

  Two→One : Two → One
  Two→One trhst X pop = fst pop-alt pop (trhst X)

  One→Four : One → Four
  One→Four poptr X Y f = Trunc→Pop ∘ (trunc-functorial f) ∘ (poptr X)

  Four→One : Four → One
  Four→One funct X px = prop-pop (h-tr _) pz where
    pz : Pop (Trunc X)
    pz  =  funct X (Trunc X) ∣_∣ px

  -- only very slightly different to the proof in the article
  One→Three : One → Three
  One→Three poptr P pp Y = λ py → poptr _ (snd pop-alt' (λ hst p₀ → hst (contr-trick p₀ py) p₀)) where
    contr-trick : (p₀ : P) → ((p : P) → Trunc (Y p)) → Trunc ((p : P) → Y p)
    contr-trick p₀ py = rec {X = Y p₀} 
                            {P = Trunc ((p : P) → Y p)} 
                            (h-tr _) 
                            (λ y₀ → ∣ <– (thm55aux.neutral-contr-exp {P = P} {Y = Y} pp p₀) y₀ ∣) (py p₀)

  Three→Two : Three → Two
  Three→Two proj X = proj (Trunc X) (h-tr _) (λ _ → X) (idf _)


-- Subsection 8.3

-- Some very simple lemmata

-- If P is a proposition, so is P + ¬ P
dec-is-prop : {P : Type} → (Funext {X = P} {Y = Empty}) → is-prop P → is-prop (P + ¬ P)
dec-is-prop {P} fext pp = all-paths-is-prop (λ { (inl p₁) (inl p₂) → ap inl (prop-has-all-paths pp _ _) ; 
                                (inl p₁) (inr np₂) → Empty-elim {A = λ _ → inl p₁ == inr np₂} (np₂ p₁) ; 
                                (inr np₁) (inl p₂) → Empty-elim {A = λ _ → inr np₁ == inl p₂} (np₁ p₂) ; 
                                (inr np₁) (inr np₂) → ap inr (fext np₁ np₂ (λ p → prop-has-all-paths (λ ()) _ _)) })


-- Theorem 8.7
nonempty-pop→lem : ((X : Type) → Funext {X} {Empty}) 
                         → ((X : Type) → (¬(¬ X) → Pop X)) → LEM
nonempty-pop→lem fext nn-pop P pp = from-fix {X = dec} (idf _) (nn-pop dec nndec (idf _) idc) where
  dec : Type
  dec = P + ¬ P

  idc : const (idf dec)
  idc = λ _ _ → prop-has-all-paths (dec-is-prop {P} (fext P) pp) _ _

  nndec : ¬(¬ dec)
  nndec ndec = (λ np → ndec (inr np)) λ p → ndec (inl p)

-- Corollary 8.8
nonempty-pop↔lem : ((X : Type) → Funext {X} {Empty}) 
                         → ((X : Type) → (¬(¬ X) → Pop X)) ↔₁₁ LEM
nonempty-pop↔lem fext = nonempty-pop→lem fext , other where
  other : LEM → ((X : Type) → (¬(¬ X) → Pop X))
  other lem X nnX = p where
    pnp : Pop X + ¬ (Pop X)
    pnp = lem (Pop X) pop-property₂

    p : Pop X
    p = match pnp withl idf _ withr (λ np → Empty-elim {A = λ _ → Pop X} (nnX (λ x → np (pop-property₁ x))))
