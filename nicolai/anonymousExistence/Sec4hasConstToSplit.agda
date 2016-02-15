{-# OPTIONS --without-K #-}

open import library.Basics hiding (Type ; Σ)
open import library.types.Sigma
open import library.NType2

open import Sec2preliminaries 
open import Sec3hedberg

module Sec4hasConstToSplit where

-- Auxiliary Lemma 4.2
transport-is-comp : {X Y : Type} → {x₁ x₂ : X} 
  → (h k : X → Y) → (t : x₁ == x₂) → (p : h x₁ == k x₁)
  → (transport _ t p) == ! (ap h t) ∙ p ∙ ap k t
transport-is-comp h k idp p = ! (∙-unit-r _)

-- Auxiliary Lemma 4.3, part 1
wconstant-implies-path-wconstant : {X Y : Type} → (f : X → Y) → (const f) 
  → (x₁ x₂ : X) → const (ap f {x = x₁} {y = x₂})
wconstant-implies-path-wconstant {X} f c x₁ x₂ p₁ p₂ = claim-cor where
  claim : {x₃ x₄ : X} → {p : x₃ == x₄} → (ap f p) == ! (c x₃ x₃) ∙ (c x₃ x₄)
  claim {x₃} {p = idp} = ! (!-inv-l (c x₃ x₃))
  claim-cor : ap f p₁ == ap f p₂
  claim-cor = 
    ap f p₁                 =⟨ claim ⟩
    ! (c x₁ x₁) ∙ (c x₁ x₂) =⟨ ! claim ⟩
    ap f p₂                 ∎ 

-- Auxiliary Lemma 4.3, part 2
wconstant-refl : {X Y : Type} → (f : X → Y) → (const f) 
  → (x : X) → (p : x == x) → ap f p == idp
wconstant-refl f c x p = wconstant-implies-path-wconstant f c x x p idp

-- We also need the following very simple lemma:
ap-id-trivial : {X : Type} → {x₁ x₂ : X} → (p : x₁ == x₂) → ap (idf X) p == p
ap-id-trivial idp = idp

-- Lemma 4.1 needs a bit of preparation.
fix : {X : Type} → (f : X → X) → Type
fix {X} f = Σ X λ x → x == f x

-- let us give a name to the map X → fix f:
to-fix : {X : Type} → (f : X → X) → (const f) → X → fix f
to-fix f c x₀ = f x₀ , c _ _

-- the other direction is just projection:
from-fix : {X : Type} → (f : X → X) → fix f → X
from-fix f (x₀ , p₀) = x₀

-- let us structure the proof of the fixed point lemma a bit:
module fixedpoint {X : Type} (f : X → X) (c : const f) where

  -- let us show that (x , p) == (x , q) first
  module _ (x : X) (p q : x == f x) where
    t : x == x
    t = p ∙ ! q

    r : f x == f x
    r = ap f t
    
    r-is-triv : r == idp
    r-is-triv = wconstant-refl f c x t

    t' : x == x
    t' = ap (idf X) t

    t'-is-t : t' == t
    t'-is-t = ap-id-trivial t

    trans-t-p-is-q : transport (λ y → y == f y) t p == q
    trans-t-p-is-q = 
      transport (λ y → y == f y) t p   =⟨  transport-is-comp (idf X) f t p  ⟩
      ! t' ∙ p ∙ r                     =⟨ ap (λ s → ! s ∙ p ∙ r) t'-is-t ⟩
      ! t ∙ p ∙ r                      =⟨ ! (∙-assoc (! t) _ _) ⟩
      (! t ∙ p) ∙ r                    =⟨ ap (λ s → (! t ∙ p) ∙ s) r-is-triv ⟩
      (! t ∙ p) ∙ idp                  =⟨ ∙-unit-r _ ⟩
      ! t ∙ p                          =⟨ ap (λ s → s ∙ p) (!-∙ p (! q)) ⟩
      (! (! q) ∙ ! p) ∙ p              =⟨ ∙-assoc (! (! q)) _ _ ⟩
      ! (! q) ∙ ! p ∙ p                =⟨ ap (λ s → ! (! q) ∙ s) (!-inv-l p) ⟩
      ! (! q) ∙ idp                    =⟨ ∙-unit-r _ ⟩
      ! (! q)                          =⟨ !-! _ ⟩
      q                                ∎

    single-x-claim : (x , p) == (x , q)
    single-x-claim = pair= t (from-transp _ _ trans-t-p-is-q)

  -- Now, we can prove that (x₁ , p₁) and (x₂ , p₂) are always equal:
  fix-paths : has-all-paths (fix f)
  fix-paths (x₁ , p₁) (x₂ , p₂) =
    (x₁ , p₁) =⟨ pair= (p₁ ∙ c x₁ x₂ ∙ ! p₂) (from-transp _ (p₁ ∙ c x₁ x₂ ∙ ! p₂) idp) ⟩
    (x₂ , _)  =⟨ single-x-claim x₂ _ _ ⟩ 
    (x₂ , p₂) ∎

-- finally, the proof of the fixed point lemma
fixed-point : {X : Type} → (f : X → X) → (const f) → is-prop (fix f)
fixed-point {X} f c = all-paths-is-prop (fixedpoint.fix-paths f c)

-- Sattler's argument
fixed-point-alt : {X : Type} → (f : X → X) → (const f) → is-prop (fix f)
fixed-point-alt {X} f c = inhab-to-contr-is-prop inh→contr where
  inh→contr : fix f → is-contr (fix f)
  inh→contr (x₀ , p₀) = equiv-preserves-level {A = Σ X λ x → x == f x₀} {B = fix f} claim-Σ (pathto-is-contr _) where
    claim : (x : X) → (x == f x₀) ≃ (x == f x)
    claim x = (λ p → p ∙ c x₀ x) , post∙-is-equiv _
    claim-Σ : (Σ X λ x → x == f x₀) ≃ fix f
    claim-Σ = equiv-Σ-snd claim

-- Corollary 4.4
-- let us define the following map:
trunc-to-fix : {X : Type} → (fc : hasConst X) → Trunc X → fix (fst fc)
trunc-to-fix (f , c) z = rec (fixed-point f c) (to-fix f c) z

hasConst→splitSup : {X : Type} → hasConst X → splitSup X
hasConst→splitSup (f , c) = (from-fix f) ∘ trunc-to-fix (f , c)

-- Theorem 4.5
hasConst↔splitSup : {X : Type} → hasConst X ↔ splitSup X
hasConst↔splitSup {X} = hasConst→splitSup , splitSup→hasConst where
  splitSup→hasConst : splitSup X → hasConst X
  splitSup→hasConst hst = f , c where
    f = hst ∘ ∣_∣
    c : const f
    c x₁ x₂ = 
      f x₁      =⟨ idp ⟩ 
      hst ∣ x₁ ∣ =⟨ ap hst (prop-has-all-paths (h-tr _) _ _) ⟩ 
      hst ∣ x₂ ∣ =⟨ idp ⟩ 
      f x₂      ∎

-- preparation for Theorem 4.6 - we need to prove that
-- f : X → X with an inhabitant of Trunc (wconst f) is enough
-- to show that fix f is propositional.
fixed-point-strong : {X : Type} → (f : X → X) → (Trunc (const f)) → is-prop (fix f)
fixed-point-strong {X} f = rec {X = const f} {P = is-prop(fix f)} is-prop-is-prop (fixed-point f) 

-- Theorem 4.6 (we exclude the part which is already included in 4.5)
-- to get an easy proof of the addendum, we structure it in the following way:
module thm46 {X : Type} where
  module _ (fhc : Σ (X → X) (Trunc ∘ const))  where
    f = fst fhc
    hc = snd fhc
    trunc-wconst-fix : Trunc X → Trunc(const f) → fix f
    trunc-wconst-fix z = rec {X = const f} {P = fix f} (fixed-point-strong f hc) (λ c → trunc-to-fix (f , c) z)
    trunc-fix : Trunc X → fix f
    trunc-fix z = trunc-wconst-fix z hc
    g : X → X
    g = fst ∘ trunc-fix ∘ ∣_∣
    g-wconst : const g
    g-wconst x₁ x₂ = ap (fst ∘ trunc-fix) (prop-has-all-paths (h-tr _) _ _)

hasConst↔hideProof : {X : Type} → hasConst X ↔ Σ (X → X) (Trunc ∘ const)
hasConst↔hideProof {X} = one , two where
  one : hasConst X → Σ (X → X) (Trunc ∘ const)
  one (f , c) = f , ∣ c ∣
  two : (Σ (X → X) (Trunc ∘ const)) → hasConst X
  two fhc = thm46.g fhc , thm46.g-wconst fhc

-- Theorem 4.6 addendum
merely-equal : {X : Type} → (fhc : Σ (X → X) (Trunc ∘ const)) → Trunc ((x : X) → fst fhc x == thm46.g fhc x)
merely-equal {X} (f , hc) = rec (h-tr _) (∣_∣ ∘ wconst-equal) hc where
  open thm46 hiding (f ; hc)
  wconst-equal : const f → (x : X) → f x == thm46.g (f , hc) x
  wconst-equal c x = 
    f x                                     =⟨ idp ⟩
    fst (to-fix f c x)                      =⟨ ap fst (! (trunc-β _ _ x)) ⟩ 
    fst (trunc-to-fix (f , c) ∣ x ∣)          =⟨ ap fst (! (trunc-β _ _ c)) ⟩ 
    fst (trunc-wconst-fix (f , hc) ∣ x ∣ ∣ c ∣) =⟨ ap (λ hc' → fst (trunc-wconst-fix (f , hc) ∣ x ∣ hc')) (prop-has-all-paths (h-tr _) _ _) ⟩ 
    fst (trunc-wconst-fix (f , hc) ∣ x ∣ hc)   =⟨ idp ⟩ 
    fst (trunc-fix (f , hc) ∣ x ∣)            =⟨ idp ⟩ 
    g (f , hc) x                             ∎
