{-# OPTIONS --without-K #-}


open import lib.Basics hiding (_⊔_)
open import lib.types.Sigma
open import lib.NType2

open import Preliminaries
open import Truncation_Level_Criteria
open import Anonymous_Existence_CollSplit

open wtrunc
open with-weak-trunc


module Weakly_Constant_Functions where

-- Definition 5.1.1
factorizes-through : ∀ {i j} {X : Type i} {Y : Type j} → Type i → (X → Y) → Type (i ⊔ j)
factorizes-through {X = X} {Y = Y} Z f = Σ (X → Z) λ f₁ → Σ (Z → Y) λ f₂ → (x : X) → f₂ (f₁ x) == f x

-- Definition 5.1.1 addendum: 'factorizes through the truncation'
-- In the theory of the thesis, universes are cumulative.
-- Here, we ask all the types to be in the same universe.
factorizes : ∀ {i} {X : Type i} {Y : Type i} → (X → Y) → Type i
factorizes {X = X} = factorizes-through (∣∣ X ∣∣)

-- Principle 5.2.1
factorize-helper : ∀ {i} {X : Type i} {Y : Type i} → (f : X → Y) → (P : Type i) → (X → is-prop P) → (factorizes-through P f) → factorizes f
factorize-helper {X = X} {Y = Y} f P xpp (f₁ , f₂ , q) = f₁' , f₂' , q' where
  f₁' : X → ∣∣ X ∣∣
  f₁' = ∣_∣

  f₂' : ∣∣ X ∣∣ → Y
  f₂' z = f₂ (tr-rec {X = X} (tr-rec is-prop-is-prop xpp z) f₁ z)

  q' : (x : X) → f₂' (f₁' x) == f x
  q' x =
    f₂' (f₁' x)         =⟨ idp ⟩
    f₂' ∣ x ∣            =⟨ idp ⟩ 
    f₂ (tr-rec _ f₁ ∣ x ∣ ) =⟨ ap f₂ (trunc-β _ f₁ x) ⟩
    f₂ (f₁ x)           =⟨ q x ⟩  
    f x                 ∎ 

-- Proposition 5.2.2
module st522 {i : ULevel} {X : Type i} {Y : Type i} (f : X → Y) (c : const f) where
  One = ¬ X
  Two = X
  Three = ∣∣ X ∣∣ → X
  Four = coll X
  Five = Y → X

  One→Three : One → Three
  One→Three nx z = Empty-elim {P = λ _ → X} (tr-rec Empty-elim nx z)

  Two→Three : Two → Three
  Two→Three x = λ _ → x

  Five→Four : Five → Four
  Five→Four g = g ∘ f , (λ x₁ x₂ → ap g (c x₁ x₂))

  Three↔Four : Three ↔ Four
  Three↔Four = snd coll↔splitSup , fst coll↔splitSup

  Three→factorizes : Three → factorizes f
  Three→factorizes s = ∣_∣ , f ∘ s , (λ x → c _ _)

-- Proposition 5.2.3 preparation
-- as a small preparation, let us define a function that applies the truncation tr-recursor twice.
-- Because of how we have defined the operator ∣∣_∣∣, we need everything to happen in the same universe
double-tr-rec : ∀ {i} {X₁ X₂ P : Type i} → (is-prop P) → (X₁ → X₂ → P) → ∣∣ X₁ ∣∣ → ∣∣ X₂ ∣∣ → P
double-tr-rec {i} {X₁} {X₂} {P} pp f z₁ z₂ = next-step z₁ z₂ where
  step : X₁ → ∣∣ X₂ ∣∣ → P 
  step x₁ = tr-rec {X = X₂} {P = P} pp (f x₁)
  step-switch : ∣∣ X₂ ∣∣ → X₁ → P
  step-switch z₂ x₁ = step x₁ z₂
  next-step : ∣∣ X₁ ∣∣ → ∣∣ X₂ ∣∣ → P
  next-step z₁ z₂ = tr-rec pp (step-switch z₂) z₁ -- tr-rec pp (step-switch z₂)

-- now, the actual Proposition 5.2.3
factorize-codomain-set : ∀ {i} {X : Type i} {Y : Type i} → (f : X → Y) → const f → is-set Y → factorizes f
factorize-codomain-set {i} {X} {Y} f c h = factorize-helper f P (λ _ → pp) fact-through-p where
  P : Type i 
  P = Σ Y λ y → ∣∣ (Σ X λ x → f x == y) ∣∣

  pp : is-prop P
  pp = all-paths-is-prop all-paths where
    all-paths : has-all-paths P
    all-paths (y₁ , t₁) (y₂ , t₂) = pair= ys ts where
      ys = double-tr-rec {P = y₁ == y₂} (h _ _) (λ {(x₁ , p₁) (x₂ , p₂) → ! p₁ ∙ c _ _ ∙ p₂}) t₁ t₂
      ts = from-transp _ ys (prop-has-all-paths tr-is-prop _ _)

  fact-through-p : factorizes-through P f
  fact-through-p = f₁ , f₂ , q where
    f₁ : X → P
    f₁ x = f x , ∣ x , idp ∣ 
    f₂ : P → Y
    f₂ = fst
    q : (x : X) → f₂ (f₁ x) == f x
    q x = idp

-- Theorem 5.2.6
-- We need function extensionality and thus import 
-- the following:
open import lib.types.Pi

-- A general auxiliary function which switches the second 
-- and third component of a Σ-type with four components
-- (provided that it is possible).
-- We formulate this explicitly as we will need it several times:
switch23 : ∀ {i} {X : Type i} → {Y Z : X → Type i} → {W : (x : X) → (Y x) → (Z x) → Type i} → 
  (Σ X λ x → Σ (Y x) λ y → Σ (Z x) λ z → (W x y z)) ≃ 
  (Σ X λ x → Σ (Z x) λ z → Σ (Y x) λ y → (W x y z))
switch23 = equiv (λ {(y , s , t , coh) → (y , t , s , coh)}) (λ {(y , t , s , coh) → (y , s , t , coh)}) (λ _ → idp) (λ _ → idp)

-- Theorem 5.2.6, with the 'equivalence reasoning' tactic:
module thm526 {i : ULevel} {Q R Y : Type i} (qq : is-prop Q) (rr : is-prop R) (f : Coprod Q R → Y) (c : const f) where

  P : Type i
  P = Σ Y λ y →
        Σ ((q : Q) → y == f(inl q)) λ s → 
        Σ ((r : R) → y == f(inr r)) λ t →
          (q : Q) → (r : R) → ! (s q) ∙ (t r) == c (inl q) (inr r)

  -- This is going to be tedious: if q₀ : Q is given, we can show that P is equivalent to the Unit type.
  given-q-reduce-P : Q → P ≃ Unit
  given-q-reduce-P q₀ = 

    P 

                         ≃⟨ switch23 ⟩

    (Σ Y λ y →
        Σ ((r : R) → y == f(inr r)) λ t →
        Σ ((q : Q) → y == f(inl q)) λ s → 
          (q : Q) → (r : R) → ! (s q) ∙ (t r) == c (inl q) (inr r))

                         ≃⟨ equiv-Σ-snd (λ y → equiv-Σ-snd (λ t → choice ⁻¹)) ⟩

    (Σ Y λ y →
        Σ ((r : R) → y == f(inr r)) λ t →
          (q : Q) → Σ (y == f(inl q)) λ s-reduced → 
                      (r : R) → ! s-reduced ∙ (t r) == c (inl q) (inr r))

                         ≃⟨ equiv-Σ-snd (λ y → equiv-Σ-snd (λ t → Π₁-contr (q₀ , prop-has-all-paths qq q₀))) ⟩ 

    (Σ Y λ y →
        Σ ((r : R) → y == f(inr r)) λ t →
          Σ (y == f(inl q₀)) λ s-reduced → 
            (r : R) → ! s-reduced ∙ (t r) == c (inl q₀) (inr r))

                         ≃⟨ switch23 ⟩ 

    (Σ Y λ y →
        Σ (y == f(inl q₀)) λ s-reduced → 
          Σ ((r : R) → y == f(inr r)) λ t →
            (r : R) → ! s-reduced ∙ (t r) == c (inl q₀) (inr r))

                         ≃⟨ equiv-Σ-snd (λ y → equiv-Σ-snd (λ t → choice ⁻¹)) ⟩ 

    (Σ Y λ y →
        Σ (y == f(inl q₀)) λ s-reduced → 
          (r : R) → Σ (y == f(inr r)) λ t-reduced → 
                       ! s-reduced ∙ t-reduced == c (inl q₀) (inr r))

                         ≃⟨ Σ-assoc ⁻¹ ⟩ 

    (Σ (Σ Y λ y → (y == f(inl q₀))) λ {(y , s-reduced) → 
       (r : R) → Σ (y == f(inr r)) λ t-reduced → 
                   ! s-reduced ∙ t-reduced == c (inl q₀) (inr r)})

                         ≃⟨ Σ₁-contr (pathto-is-contr _) ⟩  

    ((r : R) → Σ (f(inl q₀) == f(inr r)) λ t-reduced →
                 idp ∙ t-reduced == c (inl q₀) (inr r))

                         ≃⟨ Π₂-contr (λ r → pathto-is-contr _) ⟩  

    Unit                 ≃∎



  given-r-reduce-P : R → P ≃ Unit
  given-r-reduce-P r₀ =

    P 

                         ≃⟨ equiv-Σ-snd (λ _ → equiv-Σ-snd (λ _ → equiv-Σ-snd (λ _ → switch-args))) ⟩

    (Σ Y λ y →
        Σ ((q : Q) → y == f(inl q)) λ s → 
        Σ ((r : R) → y == f(inr r)) λ t →
          (r : R) → (q : Q) → ! (s q) ∙ (t r) == c (inl q) (inr r))

                         ≃⟨ equiv-Σ-snd (λ y → equiv-Σ-snd (λ s → choice ⁻¹)) ⟩

    (Σ Y λ y →
        Σ ((q : Q) → y == f(inl q)) λ s →
          (r : R) → Σ (y == f(inr r)) λ t-reduced → 
                      (q : Q) → ! (s q) ∙ t-reduced == c (inl q) (inr r))


                         ≃⟨ equiv-Σ-snd (λ y → equiv-Σ-snd (λ t → Π₁-contr (r₀ , prop-has-all-paths rr r₀))) ⟩ 

    (Σ Y λ y →
        Σ ((q : Q) → y == f(inl q)) λ s →
          Σ (y == f(inr r₀)) λ t-reduced → 
            (q : Q) → ! (s q) ∙ t-reduced == c (inl q) (inr r₀))

                         ≃⟨ switch23 ⟩

    (Σ Y λ y →
        Σ (y == f(inr r₀)) λ t-reduced → 
          Σ ((q : Q) → y == f(inl q)) λ s →
            (q : Q) → ! (s q) ∙ t-reduced == c (inl q) (inr r₀))


                         ≃⟨ equiv-Σ-snd (λ y → equiv-Σ-snd (λ s → choice ⁻¹)) ⟩ 

    (Σ Y λ y →
        Σ (y == f(inr r₀)) λ t-reduced → 
          (q : Q) → Σ (y == f(inl q)) λ s-reduced → 
                       ! s-reduced ∙ t-reduced == c (inl q) (inr r₀))


                         ≃⟨ Σ-assoc ⁻¹ ⟩ 

    (Σ (Σ Y λ y → (y == f(inr r₀))) λ {(y , t-reduced) → 
       (q : Q) → Σ (y == f(inl q)) λ s-reduced → 
                   ! s-reduced ∙ t-reduced == c (inl q) (inr r₀)})

                         ≃⟨ Σ₁-contr (pathto-is-contr _) ⟩

    ((q : Q) → Σ (f(inr r₀) == f(inl q)) λ s-reduced → 
                  ! s-reduced ∙ idp == c (inl q) (inr r₀))

                         ≃⟨ equiv-Π-r (λ q → equiv-Σ-snd (λ proof → 
                              ! proof ∙ idp == c (inl q) (inr r₀) ≃⟨ delete-idp _ _ ⟩
                              ! proof == c (inl q) (inr r₀) ≃⟨ reverse-paths _ _ ⟩
                              proof == ! (c (inl q) (inr r₀))   ≃∎
                         )) ⟩

    ((q : Q) → Σ (f(inr r₀) == f(inl q)) λ s-reduced → 
                  s-reduced == ! (c (inl q) (inr r₀)))

                         ≃⟨ Π₂-contr (λ q → pathto-is-contr _) ⟩ 

    Unit                 ≃∎



  given-q+r-reduce-P : Coprod Q R → P ≃ Unit
  given-q+r-reduce-P (inl q) = given-q-reduce-P q
  given-q+r-reduce-P (inr r) = given-r-reduce-P r

  Q+R→P : Coprod Q R → P
  Q+R→P x = <– (given-q+r-reduce-P x) _ 

  P→Y : P → Y
  P→Y = fst

  open import lib.types.Unit

  -- Finally : the statement of Theorem 5.2.6
  factorize-f : factorizes f
  factorize-f = factorize-helper f P (λ x → equiv-preserves-level ((given-q+r-reduce-P x) ⁻¹) Unit-is-prop) (Q+R→P , P→Y , proof) where
    proof : (x : Coprod Q R) → P→Y (Q+R→P x) == f x
    proof (inl q) = idp
    proof (inr r) = idp

-- and Theorem 5.2.6 again (outside of a specialized module)
Theorem526 : ∀ {i} {Q R Y : Type i} → (is-prop Q) → (is-prop R) → (f : Coprod Q R → Y) → (const f) → factorizes f
Theorem526 = thm526.factorize-f 
