{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.NType2


open import Preliminaries
open import Truncation_Level_Criteria

module Anonymous_Existence_CollSplit where

-- CHAPTER 4
-- SECTION 4.1

-- Lemma 4.1.2, part 1
constant-implies-path-constant : ∀ {i j} {X : Type i} {Y : Type j} → (f : X → Y) → (const f) 
  → (x₁ x₂ : X) → const (ap f {x = x₁} {y = x₂})
constant-implies-path-constant {X = X} f c x₁ x₂ p₁ p₂ = claim-cor where
  claim : {x₃ x₄ : X} → {p : x₃ == x₄} → (ap f p) == ! (c x₃ x₃) ∙ (c x₃ x₄)
  claim {x₃} {p = idp} = ! (!-inv-l (c x₃ x₃))
  claim-cor : ap f p₁ == ap f p₂
  claim-cor = 
    ap f p₁                 =⟨ claim ⟩
    ! (c x₁ x₁) ∙ (c x₁ x₂) =⟨ ! claim ⟩
    ap f p₂                 ∎ 

-- Lemma 4.1.2, part 2
constant-refl :  ∀ {i j} {X : Type i} {Y : Type j} → (f : X → Y) → (const f) 
  → (x : X) → (p : x == x) → ap f p == idp
constant-refl f c x p = constant-implies-path-constant f c x x p idp

-- todo: this is not in the library?
-- We also need the following very simple lemma:
ap-id-trivial : ∀ {i} {X : Type i} → {x₁ x₂ : X} → (p : x₁ == x₂) → ap (idf X) p == p
ap-id-trivial idp = idp

-- Main Lemma 4.1.1 needs a bit of preparation.
fix : ∀ {i} {X : Type i} → (f : X → X) → Type i
fix {X = X} f = Σ X λ x → x == f x

-- let us give a name to the map X → fix f:
to-fix : ∀ {i} {X : Type i} → (f : X → X) → (const f) → X → fix f
to-fix f c x₀ = f x₀ , c _ _

-- the other direction is just projection:
from-fix : ∀ {i} {X : Type i} → (f : X → X) → fix f → X
from-fix f (x₀ , p₀) = x₀

-- let us structure the proof of the fixed point lemma a bit:
module fixedpoint {i : ULevel} {X : Type i}  (f : X → X) (c : const f) where

  -- let us show that (x , p) == (x , q) first
  module _ (x : X) (p q : x == f x) where
    t : x == x
    t = p ∙ ! q

    r : f x == f x
    r = ap f t
    
    r-is-triv : r == idp
    r-is-triv = constant-refl f c x t

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
fixed-point : ∀ {i} {X : Type i} → (f : X → X) → (const f) → is-prop (fix f)
fixed-point {X = X} f c = all-paths-is-prop (fixedpoint.fix-paths f c)

-- Sattler's argument
fixed-point-alt :  ∀ {i} {X : Type i} → (f : X → X) → (const f) → is-prop (fix f)
fixed-point-alt {X = X} f c = inhab-to-contr-is-prop inh→contr where
  inh→contr : fix f → is-contr (fix f)
  inh→contr (x₀ , p₀) = equiv-preserves-level {A = Σ X λ x → x == f x₀} {B = fix f} claim-Σ (pathto-is-contr _) where
    claim : (x : X) → (x == f x₀) ≃ (x == f x)
    claim x = (λ p → p ∙ c x₀ x) , post∙-is-equiv _
    claim-Σ : (Σ X λ x → x == f x₀) ≃ fix f
    claim-Σ = equiv-Σ-snd claim

--from here, we need truncation
module with-weak-trunc where
  open wtrunc

  -- Corollary 4.1.3
  -- let us define the following map:
  trunc-to-fix : ∀ {i} {X : Type i} → (fc : coll X) → ∣∣ X ∣∣ → fix (fst fc)
  trunc-to-fix (f , c) z = tr-rec (fixed-point f c) (to-fix f c) z
  
  coll→splitSup : ∀ {i} {X : Type i} → coll X → splitSup X
  coll→splitSup (f , c) = (from-fix f) ∘ trunc-to-fix (f , c)
  
  -- Theorem 4.1.4
  coll↔splitSup : ∀ {i} {X : Type i} → coll X ↔ splitSup X
  coll↔splitSup {X = X} = coll→splitSup , splitSup→coll where
    splitSup→coll : splitSup X → coll X
    splitSup→coll hst = f , c where
      f = hst ∘ ∣_∣
      c : const f
      c x₁ x₂ = 
        f x₁      =⟨ idp ⟩ 
        hst ∣ x₁ ∣ =⟨ ap hst (prop-has-all-paths tr-is-prop _ _) ⟩ 
        hst ∣ x₂ ∣ =⟨ idp ⟩ 
        f x₂      ∎
  
  -- preparation for Statement 4.1.5 - we need to prove that
  -- f : X → X with an inhabitant of ∣∣ const f ∣∣ is enough
  -- to show that fix f is propositional.
  fixed-point-strong : ∀ {i} {X : Type i} → (f : X → X) → ∣∣ const f ∣∣ → is-prop (fix f)
  fixed-point-strong {X = X} f = tr-rec {X = const f} {P = is-prop(fix f)} is-prop-is-prop (fixed-point f) 
  
  -- Statement 4.1.5 (we exclude the part which is already included in Theorem 4.1.4)
  -- to get an easy proof of the addendum, we structure it in the following way:
  module thm46 {i : ULevel} {X : Type i}  where
    module _ (fhc : Σ (X → X) (λ f → ∣∣ const f ∣∣))  where
      f = fst fhc
      hc = snd fhc
      trunc-const-fix : ∣∣ X ∣∣ → ∣∣ const f ∣∣ → fix f
      trunc-const-fix z = tr-rec {X = const f} {P = fix f} (fixed-point-strong f hc) (λ c → trunc-to-fix (f , c) z)
      trunc-fix : ∣∣ X ∣∣ → fix f
      trunc-fix z = trunc-const-fix z hc
      g : X → X
      g = fst ∘ trunc-fix ∘ ∣_∣
      g-const : const g
      g-const x₁ x₂ = ap (fst ∘ trunc-fix) (prop-has-all-paths tr-is-prop _ _)
  
  coll↔hideProof : ∀ {i} {X : Type i} → coll X ↔ Σ (X → X) (λ f → ∣∣ const f ∣∣)
  coll↔hideProof {X = X} = one , two where
    one : coll X → Σ (X → X) (λ f → ∣∣ const f ∣∣)
    one (f , c) = f , ∣ c ∣
    two : (Σ (X → X) (λ f → ∣∣ const f ∣∣)) → coll X
    two fhc = thm46.g fhc , thm46.g-const fhc
  


  -- Statement 4.1.5 addendum
  merely-equal : ∀ {i} {X : Type i} → (fhc : Σ (X → X) (λ f → ∣∣ const f ∣∣)) → ∣∣ ((x : X) → fst fhc x == thm46.g fhc x) ∣∣
  merely-equal {X = X} (f , hc) = tr-rec tr-is-prop (∣_∣ ∘ const-equal) hc where
    open thm46 
    const-equal : const f → (x : X) → f x == thm46.g (f , hc) x
    const-equal c x = 
      f x                                     =⟨ idp ⟩
      fst (to-fix f c x)                      =⟨ ap fst (! (trunc-β _ _ x)) ⟩ 
      fst (trunc-to-fix (f , c) ∣ x ∣)          =⟨ ap fst (! (trunc-β _ _ c)) ⟩ 
      fst (trunc-const-fix (f , hc) ∣ x ∣ ∣ c ∣) =⟨ ap (λ hc' → fst (trunc-const-fix (f , hc) ∣ x ∣ hc')) (prop-has-all-paths tr-is-prop _ _) ⟩ 
      fst (trunc-const-fix (f , hc) ∣ x ∣ hc)   =⟨ idp ⟩ 
      fst (trunc-fix (f , hc) ∣ x ∣)            =⟨ idp ⟩ 
      g (f , hc) x                             ∎

