{-# OPTIONS --without-K #-}

open import lib.Basics hiding (_⊔_)
open import lib.types.Sigma
open import lib.types.Bool
open import lib.types.Empty

open import Preliminaries
open import Truncation_Level_Criteria
open import Anonymous_Existence_CollSplit
open import Anonymous_Existence_Populatedness


module Anonymous_Existence_Comparison where

-- Chapter 4.3: Comparison of Notions of Existence

-- Section 4.3.1: Inhabited and Merely Inhabited

-- Lemma 4.3.1
coll-family-dec : ∀ {i} {X : Type i} → (x₁ x₂ : X) → ((x : X) → coll (Coprod (x₁ == x) (x₂ == x))) → Coprod (x₁ == x₂) (¬(x₁ == x₂))
coll-family-dec {i} {X} x₁ x₂ coll-fam = solution where
  f₋ : (x : X) → Coprod (x₁ == x) (x₂ == x) → Coprod (x₁ == x) (x₂ == x)
  f₋ x = fst (coll-fam x)

  E₋ : X → Type i
  E₋ x = fix (f₋ x)

  E : Type i
  E = Σ X λ x → (E₋ x)

  E-fst-determines-eq : (e₁ e₂ : E) → (fst e₁ == fst e₂) → e₁ == e₂
  E-fst-determines-eq e₁ e₂ p = second-comp-triv (λ x → fixed-point (f₋ x) (snd (coll-fam x))) _ _ p

  r : Bool → E
  r true = x₁ , to-fix (f₋ x₁) (snd (coll-fam x₁)) (inl idp) 
  r false = x₂ , to-fix (f₋ x₂) (snd (coll-fam x₂)) (inr idp)

  about-r : (r true == r false) ↔ (x₁ == x₂)
  about-r = (λ p → ap fst p) , (λ p → E-fst-determines-eq _ _ p)

  s : E → Bool
  s (_ , inl _ , _) = true
  s (_ , inr _ , _) = false

  s-section-of-r : (e : E) → r(s e) == e
  s-section-of-r (x , inl p , q) = E-fst-determines-eq _ _ p
  s-section-of-r (x , inr p , q) = E-fst-determines-eq _ _ p

  about-s : (e₁ e₂ : E) → (s e₁ == s e₂) ↔ (e₁ == e₂)
  about-s e₁ e₂ = one , two where
    one : (s e₁ == s e₂) → (e₁ == e₂)
    one p = 
      e₁       =⟨ ! (s-section-of-r e₁) ⟩
      r(s(e₁)) =⟨ ap r p ⟩
      r(s(e₂)) =⟨ s-section-of-r e₂ ⟩
      e₂       ∎
    two : (e₁ == e₂) → (s e₁ == s e₂)
    two p = ap s p

  combine : (s (r true) == s (r false)) ↔ (x₁ == x₂)
  combine = (about-s _ _) ◎ about-r

  check-bool : Coprod (s (r true) == s (r false)) (¬(s (r true) == s (r false)))
  check-bool = Bool-has-dec-eq _ _

  solution : Coprod (x₁ == x₂) (¬(x₁ == x₂))
  solution with check-bool 
  solution | inl p = inl (fst combine p)
  solution | inr np = inr (λ p → np (snd combine p))


-- definition: "all types have a weakly constant endofunction".
-- this assumption is, if we have ∣∣_∣∣, logically equivalent to saying that
-- every type has split support.
all-coll : ∀ {i} → Type (lsucc i)
all-coll {i} = (X : Type i) → coll X

-- Proposition 4.3.2
all-coll→dec-eq : ∀ {i} → all-coll {i} → (X : Type i) → has-dec-eq X
all-coll→dec-eq all-coll X x₁ x₂ = coll-family-dec x₁ x₂ (λ x → all-coll _)


open with-weak-trunc
open wtrunc


--  Proposition 4.3.3
module functional-subrelation {i : ULevel} (ac : all-coll {i}) (X : Type i) (R : X × X → Type i) where

  all-sets : (Y : Type i) → is-set Y
  all-sets Y = pathColl→isSet (λ y₁ y₂ → ac _)

  R₋ : (x : X) → Type i
  R₋ x = Σ X λ y → R(x , y)

  k : (x : X) → (R₋ x) → (R₋ x)
  k x = fst (ac _)

  kc : (x : X) → const (k x)
  kc x = snd (ac _)

  SS : X × X → Type i
  SS (x , y) = Σ (R(x , y)) λ a → 
                (y , a) == k x (y , a)

  -- the relation S
  SS₋ : (x : X) → Type i
  SS₋ x = Σ X λ y → SS(x , y)

  -- fix kₓ is equivalent to Sₓ
  -- This is just Σ-assoc. We try to make it more readable by adding some (trivial) steps.
  fixk-SS : (x : X) → (fix (k x)) ≃ SS₋ x
  fixk-SS x = 
      (fix (k x))                                           ≃⟨ ide _ ⟩
      (Σ (Σ X λ y → R(x , y)) λ a → a == k x a)             ≃⟨ Σ-assoc ⟩
      (Σ X λ y → Σ (R(x , y)) λ r → (y , r) == k x (y , r)) ≃⟨ ide _ ⟩
      (SS₋ x)                                                ≃∎

  -- claim (0)
  subrelation : (x y : X) → SS(x , y) →  R(x , y)
  subrelation x y (r , _) = r

   -- claim (1)
  prop-SSx : (x : X) → is-prop (SS₋ x)
  prop-SSx x = equiv-preserves-level {A = fix (k x)} {B = (SS₋ x)} (fixk-SS x) (fixed-point _ (kc x)) 

  -- claim (2)
  same-domain : (x : X) → (R₋ x) ↔ (SS₋ x)
  same-domain x = rs , sr where
    rs : (R₋ x) → (SS₋ x)
    rs a = –> (fixk-SS x) (to-fix (k x) (kc x) a)
    sr : (SS₋ x) → (R₋ x)
    sr (y , r , _) = y , r

  -- claim (3) 
  prop-SS : (x y : X) → is-prop (SS (x , y))
  prop-SS x y = all-paths-is-prop all-paths where
    all-paths : (s₁ s₂ : SS(x , y)) → s₁ == s₂
    all-paths s₁ s₂ = ss where

      yss : (y , s₁) == (y , s₂)
      yss = prop-has-all-paths (prop-SSx x) _ _

      ss : s₁ == s₂
      ss = set-lemma (all-sets _) y s₁ s₂ yss


-- intermediate definition
-- see the caveat about the notion 'epimorphism' in the article
is-split-epimorphism : ∀ {i j} {U : Type i} {V : Type j} → (U → V) → Type (i ⊔ j)
is-split-epimorphism {U = U} {V = V} e = Σ (V → U) λ s → (v : V) → e (s v) == v

is-epimorphism : ∀ {i j} {U : Type i} {V : Type j} → (U → V) → Type (lsucc (i ⊔ j))
is-epimorphism {i} {j} {U = U} {V = V} e = (W : Type (i ⊔ j)) → (f g : V → W) → ((u : U) → f (e u) == g (e u)) → (v : V) → f v == g v

-- Lemma 4.3.4
path-trunc-epi→set : ∀ {i} {Y : Type i} → ((y₁ y₂ : Y) → is-epimorphism (∣_∣ {X = y₁ == y₂})) → is-set Y
path-trunc-epi→set {Y = Y} path-epi = reminder special-case where

  f : (y₁ y₂ : Y) → ∣∣ y₁ == y₂ ∣∣ → Y
  f y₁ _ _ = y₁

  g : (y₁ y₂ : Y) → ∣∣ y₁ == y₂ ∣∣ → Y
  g _ y₂ _ = y₂

  special-case : (y₁ y₂ : Y) → ∣∣ y₁ == y₂ ∣∣ → y₁ == y₂
  special-case y₁ y₂ = path-epi y₁ y₂ Y (f y₁ y₂) (g y₁ y₂) (idf _)

  -- we know that hSeparated(X) implies that X is a set, 
  -- from the previous Proposition 3.1.9; 
  -- however, we have proved it in such a way which forces 
  -- us to combine three directions:
  reminder : hSeparated Y → is-set Y
  reminder = (fst (set-characterisations Y)) ∘ (fst (snd (snd (set-characterisations Y)))) ∘ (snd (snd (snd (snd (set-characterisations Y)))))

-- Proposition 4.3.5 (1)
all-split→all-deceq : ∀ {i} → ((X : Type i) → is-split-epimorphism (∣_∣ {X = X})) → (X : Type i) → has-dec-eq X
all-split→all-deceq {i} all-split = all-coll→dec-eq ac where
  ac : (X : Type i) → coll X
  ac X = snd coll↔splitSup (fst (all-split X))

-- Proposition 4.3.5 (2)
all-epi→all-set : ∀ {i} → ((X : Type i) → is-epimorphism (∣_∣ {X = X})) → (X : Type i) → is-set X
all-epi→all-set all-epi X = path-trunc-epi→set (λ y₁ y₂ → all-epi (y₁ == y₂))


-- Section 4.3.2: Merely Inhabited and Populated

-- Lemma 4.3.6, first proof
pop-hstable-1 : ∀ {i} {X : Type i} → ⟪ splitSup X ⟫
pop-hstable-1 {X = X} f c = to-fix f c (coll→splitSup (g , gc)) where

  g : X → X
  g x = f (λ _ → x) ∣ x ∣

  gc : const g
  gc x₁ x₂ = 
    g x₁               =⟨ idp ⟩
    f (λ _ → x₁) ∣ x₁ ∣ =⟨ ap (λ k → k ∣ x₁ ∣) (c (λ _ → x₁) (λ _ → x₂)) ⟩
    f (λ _ → x₂) ∣ x₁ ∣ =⟨ ap (f (λ _ → x₂)) (prop-has-all-paths tr-is-prop ∣ x₁ ∣ ∣ x₂ ∣) ⟩
    f (λ _ → x₂) ∣ x₂ ∣ =⟨ idp ⟩
    g x₂               ∎  

-- Lemma 4.3.6, second proof
pop-hstable-2 : ∀ {i} {X : Type i} → ⟪ splitSup X ⟫
pop-hstable-2 {i} {X} = snd (pop-alt₂ {X = splitSup X}) get-P where
  get-P : (P : Type i) → is-prop P → splitSup X ↔ P → P
  get-P P pp (hstp , phst) = hstp free-hst where

    xp : X → P
    xp x = hstp (λ _ → x)

    zp : ∣∣ X ∣∣ → P
    zp = tr-rec pp xp

    free-hst : splitSup X
    free-hst z = phst (zp z) z

-- Lemma 4.3.6, third proof
pop-hstable-3 : ∀ {i} {X : Type i} → ⟪ splitSup X ⟫
pop-hstable-3 {X = X} = snd pop-alt translation where

  translation-aux : splitSup (splitSup X) → splitSup X
  translation-aux = λ hsthst z → hsthst (trunc-functorial {X = X} {Y = splitSup X} (λ x _ → x) z) z

  translation :  ∣∣ splitSup (splitSup X) ∣∣ → ∣∣ splitSup X ∣∣ 
  translation = trunc-functorial translation-aux

-- Lemma 4.3.7
module tlem437 {i : ULevel} where

  One = (X : Type i) → ⟪ X ⟫ → ∣∣ X ∣∣

  Two = (X : Type i) → ∣∣ splitSup X ∣∣

  Three = (P : Type i) → is-prop P → (Y : P → Type i) → ((p : P) → ∣∣ Y p ∣∣) → ∣∣ ((p : P) → Y p) ∣∣

  Four = (X Y : Type i) → (X → Y) → (⟪ X ⟫ → ⟪ Y ⟫)


  One→Two : One → Two
  One→Two poptr X = poptr (splitSup X) pop-hstable-1 

  Two→One : Two → One
  Two→One trhst X pop = fst pop-alt pop (trhst X)

  One→Four : One → Four
  One→Four poptr X Y f = Trunc→Pop ∘ (trunc-functorial f) ∘ (poptr X)

  Four→One : Four → One
  Four→One funct X px = prop-pop tr-is-prop pz where -- (tr-rec _) pz where
    pz : ⟪ ∣∣ X ∣∣ ⟫
    pz  =  funct X (∣∣ X ∣∣) ∣_∣ px

  -- only very slightly different to the proof in the article
  One→Three : One → Three
  One→Three poptr P pp Y = λ py → poptr _ (snd pop-alt' (λ hst p₀ → hst (contr-trick p₀ py) p₀)) where
    contr-trick : (p₀ : P) → ((p : P) → ∣∣ Y p ∣∣) → ∣∣ ((p : P) → Y p) ∣∣
    contr-trick p₀ py = tr-rec {X = Y p₀} 
                               {P = ∣∣ ((p : P) → Y p) ∣∣} 
                               tr-is-prop 
                               (λ y₀ → ∣ (λ p → transport Y (prop-has-all-paths pp p₀ p) y₀) ∣) 
                               (py p₀) 

  Three→Two : Three → Two
  Three→Two proj X = proj (∣∣ X ∣∣) tr-is-prop (λ _ → X) (idf _)


-- Section 4.3.3: Populated and Non-Empty

-- We now need function extensionality. We 
-- start with some very simple auxiliary 
-- lemmata (not numbered in the thesis).

-- If P is a proposition, so is P + ¬ P
dec-is-prop : ∀ {i} {P : Type i} → is-prop P → is-prop (Coprod P (¬ P))
dec-is-prop {P = P} pp = all-paths-is-prop (λ { (inl p₁) (inl p₂) → ap inl (prop-has-all-paths pp _ _) ;  
                                (inl p₁) (inr np₂) → Empty-elim {P = λ _ → inl p₁ == inr np₂} (np₂ p₁) ; 
                                (inr np₁) (inl p₂) → Empty-elim {P = λ _ → inr np₁ == inl p₂} (np₁ p₂) ; 
                                (inr np₁) (inr np₂) → ap inr (λ= (λ x → prop-has-all-paths Empty-is-prop _ _ )) }) 


-- Proposition 4.3.8
nonempty-pop→LEM : ∀ {i} → ((X : Type i) → (¬(¬ X) → ⟪ X ⟫)) → LEM {i}
nonempty-pop→LEM {i} nn-pop P pp = from-fix {X = dec} (idf _) (nn-pop dec nndec (idf _) idc) where
  dec : Type i
  dec = Coprod P (¬ P)

  idc : const (idf dec)
  idc = λ _ _ → prop-has-all-paths (dec-is-prop {P = P} pp) _ _

  nndec : ¬(¬ dec)
  nndec ndec = (λ np → ndec (inr np)) λ p → ndec (inl p)

-- Corollary 4.3.9
nonempty-pop↔lem : ∀ {i} → ((X : Type i) → (¬(¬ X) → ⟪ X ⟫)) ↔ LEM {i}
nonempty-pop↔lem {i} = nonempty-pop→LEM , other where
  other : LEM {i} → ((X : Type i) → (¬(¬ X) → ⟪ X ⟫))
  other lem X nnX = p where
    pnp : Coprod ⟪ X ⟫ (¬ ⟪ X ⟫)
    pnp = lem ⟪ X ⟫ pop-property₂

    p : ⟪ X ⟫
    p = match pnp withl idf _ withr (λ np → Empty-elim {P = λ _ → ⟪ X ⟫} (nnX (λ x → np (pop-property₁ x))))
