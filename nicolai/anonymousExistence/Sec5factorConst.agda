{-# OPTIONS --without-K #-}

open import library.Basics hiding (Type ; Σ)
open import library.types.Sigma
open import library.NType2

open import Sec2preliminaries 
open import Sec3hedberg
open import Sec4hasConstToSplit

module Sec5factorConst where

-- Definition 5.1
factors-through : {X Y : Type} → Type → (X → Y) → Type
factors-through {X} {Y} Z f = Σ (X → Z) λ f₁ → Σ (Z → Y) λ f₂ → (x : X) → f₂ (f₁ x) == f x

-- Definition 5.1 addendum: "factors through the truncation"
factors : {X Y : Type} → (X → Y) → Type
factors {X} = factors-through (Trunc X)

-- Principle 5.2
factor-helper : {X Y : Type} → (f : X → Y) → (P : Type) → (X → is-prop P) → (factors-through P f) → factors f
factor-helper {X} {Y} f P xpp (f₁ , f₂ , q) = f₁' , f₂' , q' where
  f₁' : X → Trunc X
  f₁' = ∣_∣

  f₂' : Trunc X → Y
  f₂' z = f₂ (rec {X} (rec is-prop-is-prop xpp z) f₁ z)

  q' : (x : X) → f₂' (f₁' x) == f x
  q' x =
    f₂' (f₁' x)         =⟨ idp ⟩
    f₂' ∣ x ∣            =⟨ idp ⟩ 
    f₂ (rec _ f₁ ∣ x ∣ ) =⟨ ap f₂ (trunc-β _ f₁ x) ⟩
    f₂ (f₁ x)           =⟨ q x ⟩  
    f x                 ∎ 

-- Theorem 5.3
module thm53 {X Y : Type} (f : X → Y) (c : const f) where
  One = ¬ X
  Two = X
  Three = Trunc X → X
  Four = hasConst X
  Five = Y → X

  One→Three : One → Three
  One→Three nx z = Empty-elim {A = λ _ → X} (rec Empty-elim nx z)

  Two→Three : Two → Three
  Two→Three x = λ _ → x

  Five→Four : Five → Four
  Five→Four g = g ∘ f , (λ x₁ x₂ → ap g (c x₁ x₂))

  Three↔Four : Three ↔ Four
  Three↔Four = snd hasConst↔splitSup , fst hasConst↔splitSup

  Three→factors : Three → factors f
  Three→factors s = ∣_∣ , f ∘ s , (λ x → c _ _)

-- Theorem 5.4
-- as a small preparation, let us define a function that applies the truncation recursor twice:
double-rec : {X₁ X₂ P : Type} → (is-prop P) → (X₁ → X₂ → P) → Trunc X₁ → Trunc X₂ → P
double-rec {X₁} {X₂} {P} pp f z₁ z₂ = next-step z₂ z₁ where
  step : X₁ → Trunc X₂ → P 
  step x₁ = rec {X = X₂} {P = P} pp (f x₁)
  step-switch : Trunc X₂ → X₁ → P
  step-switch z₂ x₁ = step x₁ z₂
  next-step : Trunc X₂ → Trunc X₁ → P
  next-step z₂ = rec pp (step-switch z₂)

-- now, the actual Theorem 5.4
factor-codomain-set : {X Y : Type} → (f : X → Y) → const f → is-set Y → factors f
factor-codomain-set {X} {Y} f c h = factor-helper f P (λ _ → pp) fact-through-p where
  P : Type
  P = Σ Y λ y → Trunc(Σ X λ x → f x == y)

  pp : is-prop P
  pp = all-paths-is-prop all-paths where
    all-paths : has-all-paths P
    all-paths (y₁ , t₁) (y₂ , t₂) = pair= ys ts where
      ys = double-rec {P = y₁ == y₂} (h _ _) (λ {(x₁ , p₁) (x₂ , p₂) → ! p₁ ∙ c _ _ ∙ p₂}) t₁ t₂
      ts = from-transp _ ys (prop-has-all-paths (h-tr _) _ _)

  fact-through-p : factors-through P f
  fact-through-p = f₁ , f₂ , q where
    f₁ : X → P
    f₁ x = f x , ∣ x , idp ∣ 
    f₂ : P → Y
    f₂ = fst
    q : (x : X) → f₂ (f₁ x) == f x
    q x = idp

-- Theorem 5.5
-- Note that this lemma requires function extensionality (hidden in the use of the library.types.Pi library: 
-- at one point, we use that Π X Y is propositional as soon as Y x is (for all x)).

open import library.types.Pi

-- a general auxiliary function which switches the second and third component of a Σ-type with four components
-- (provided that it is possible)
-- we formulate this explicitly as we will need it several times
switch23 : {X : Type} → {Y Z : X → Type} → {W : (x : X) → (Y x) → (Z x) → Type} → 
  (Σ X λ x → Σ (Y x) λ y → Σ (Z x) λ z → (W x y z)) ≃ 
  (Σ X λ x → Σ (Z x) λ z → Σ (Y x) λ y → (W x y z))
switch23 = equiv (λ {(y , s , t , coh) → (y , t , s , coh)}) (λ {(y , t , s , coh) → (y , s , t , coh)}) (λ _ → idp) (λ _ → idp)

module thm55aux {P : Type} {Y : P → Type} (pp : is-prop P) (x₀ : P) where 
  neutral-contr-base-space : Σ P Y ≃ Y x₀
  neutral-contr-base-space =
    Σ P Y               ≃⟨ (equiv-Σ-fst {A = Unit} {B = P} Y 
                             {λ _ → x₀} 
                             (is-eq _ (λ _ → unit) (λ _ → prop-has-all-paths pp _ _) (λ _ → idp))) ⁻¹  ⟩ 
    Σ Unit (λ _ → Y x₀) ≃⟨ Σ₁-Unit ⟩
    Y x₀                ≃∎

  neutral-contr-exp : Π P Y ≃ Y x₀
  neutral-contr-exp = 
    Π P Y               ≃⟨ (equiv-Π-l {A = Unit} {B = P} Y
                             {λ _ → x₀}
                             (is-eq _ (λ _ → unit) (λ _ → prop-has-all-paths pp _ _) (λ _ → idp))) ⁻¹ ⟩
    Π Unit (λ _ → Y x₀) ≃⟨ Π₁-Unit ⟩
    Y x₀                ≃∎



module thm55 {Q R Y : Type} (qq : is-prop Q) (rr : is-prop R) (f : Q + R → Y) (c : const f) where

  P : Type
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

                         ≃⟨ equiv-Σ-snd (λ y → equiv-Σ-snd (λ t → thm55aux.neutral-contr-exp qq q₀)) ⟩

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

                         ≃⟨ thm55aux.neutral-contr-base-space (contr-is-prop (pathto-is-contr _)) (f(inl q₀) , idp) ⟩ 

    ((r : R) → Σ (f(inl q₀) == f(inr r)) λ t-reduced →
                 idp ∙ t-reduced == c (inl q₀) (inr r))

                         ≃⟨ neutral-codomain (λ r → pathto-is-contr _) ⟩ 

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


                         ≃⟨ equiv-Σ-snd (λ y → equiv-Σ-snd (λ t → thm55aux.neutral-contr-exp rr r₀)) ⟩

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

                         ≃⟨ thm55aux.neutral-contr-base-space (contr-is-prop (pathto-is-contr _)) (f(inr r₀) , idp) ⟩ 

    ((q : Q) → Σ (f(inr r₀) == f(inl q)) λ s-reduced → 
                  ! s-reduced ∙ idp == c (inl q) (inr r₀))

                         ≃⟨ equiv-Π-r (λ q → equiv-Σ-snd (λ proof → 
                              ! proof ∙ idp == c (inl q) (inr r₀) ≃⟨ delete-idp _ _ ⟩
                              ! proof == c (inl q) (inr r₀) ≃⟨ reverse-paths _ _ ⟩
                              proof == ! (c (inl q) (inr r₀))   ≃∎
                         )) ⟩

    ((q : Q) → Σ (f(inr r₀) == f(inl q)) λ s-reduced → 
                  s-reduced == ! (c (inl q) (inr r₀)))

                         ≃⟨  neutral-codomain (λ q → pathto-is-contr _) ⟩ 

    Unit                 ≃∎



  given-q+r-reduce-P : Q + R → P ≃ Unit
  given-q+r-reduce-P (inl q) = given-q-reduce-P q
  given-q+r-reduce-P (inr r) = given-r-reduce-P r

  Q+R→P : Q + R → P
  Q+R→P x = <– (given-q+r-reduce-P x) _ 

  P→Y : P → Y
  P→Y = fst

  open import library.types.Unit

  -- Finally : the statement of Theorem 5.5
  factor-f : factors f
  factor-f = factor-helper f P (λ x → equiv-preserves-level ((given-q+r-reduce-P x) ⁻¹) Unit-is-prop) (Q+R→P , P→Y , proof) where
    proof : (x : Q + R) → P→Y (Q+R→P x) == f x
    proof (inl q) = idp
    proof (inr r) = idp

-- and Theorem 5.5 again (outside of a specialized module)
Theorem55 : {Q R Y : Type} → (is-prop Q) → (is-prop R) → (f : Q + R → Y) → (const f) → factors f
Theorem55 = thm55.factor-f 
