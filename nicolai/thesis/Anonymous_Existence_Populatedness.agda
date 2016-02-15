{-# OPTIONS --without-K #-}

open import lib.Basics 
open import lib.types.Sigma


open import Preliminaries
open import Truncation_Level_Criteria
open import Anonymous_Existence_CollSplit

open wtrunc
open with-weak-trunc


module Anonymous_Existence_Populatedness where

-- Definition 4.2.1
⟪_⟫ : ∀ {i} → Type i → Type i
⟪ X ⟫ = (f : X → X) → const f → fix f

-- Proposition 4.2.2
Trunc→Pop : ∀ {i} {X : Type i} → ∣∣ X ∣∣ → ⟪ X ⟫
Trunc→Pop z f c = tr-rec {P = fix f} (fixed-point f c) (to-fix f c) z

-- Corollary 4.2.3: We show pairwise logical equivalence as it is easy
-- (of course, some directions are redundant)
coll-characterizations : ∀ {i} {X : Type i} 
  → (coll X ↔ splitSup X) 
   × ((coll X ↔ (⟪ X ⟫ → X)) 
   × ((⟪ X ⟫ → X) ↔ splitSup X))
coll-characterizations {X = X} = coll↔splitSup , 
                                 (coll→pop→X , reverse₁) , 
                                 (pop→X→splitSup , reverse₂) where

  coll→pop→X : coll X → ⟪ X ⟫ → X
  coll→pop→X (f , c) pop = fst (pop f c) 

  pop→X→splitSup : (⟪ X ⟫ → X) → splitSup X
  pop→X→splitSup g = g ∘ Trunc→Pop

  reverse₁ = snd coll↔splitSup ∘ pop→X→splitSup
  reverse₂ = coll→pop→X ∘ snd coll↔splitSup

-- Addendum of Corollary 4.2.3
prop-pop : ∀ {i} {P : Type i} → is-prop P → ⟪ P ⟫ → P
prop-pop {P = P} pp = snd (snd (snd coll-characterizations)) (tr-rec pp (idf _)) 

-- Lemma 4.2.4
module _ {i : ULevel} {X : Type i} where

  pop→splitSup→X : ⟪ X ⟫ → splitSup X → X
  pop→splitSup→X pop = λ hst → snd (snd (snd (coll-characterizations {X = X}))) hst pop

  use-funct : (splitSup X → X) → ∣∣ splitSup X ∣∣ → ∣∣ X ∣∣
  use-funct f = trunc-functorial f

  tr-hst-X→pop : (∣∣ splitSup X ∣∣ → ∣∣ X ∣∣) → ⟪ X ⟫
  tr-hst-X→pop g f c = tr-rec (fixed-point f c) (to-fix f c) (g ∣ coll→splitSup (f , c) ∣) 

  -- we formulate the two logical equivalence that we will need explicitly:
  pop-alt : ⟪ X ⟫ ↔ (∣∣ splitSup X ∣∣ → ∣∣ X ∣∣)
  pop-alt = use-funct ∘ pop→splitSup→X , tr-hst-X→pop

  pop-alt' : ⟪ X ⟫ ↔ (splitSup X → X)
  pop-alt' = pop→splitSup→X , tr-hst-X→pop ∘ use-funct

  
-- Proposition 4.2.5
pop-alt₂ : ∀ {i} {X : Type i} → ⟪ X ⟫ ↔ ((P : Type i) → (is-prop P) → (X ↔ P) → P)
pop-alt₂ {i} {X} = one , two where

  one : ⟪ X ⟫ → (P : Type i) → is-prop P → (X ↔ P) → P
  one pop P pp (xp , px) = xp (fst (pop f c)) where
    f : X → X
    f = px ∘ xp
    c : const f
    c x₁ x₂ = ap px (prop-has-all-paths pp _ _)

  two : ((P : Type i) → is-prop P → (X ↔ P) → P) → ⟪ X ⟫
  two rest f c = rest (fix f) (fixed-point f c) (to-fix f c , from-fix f)

-- Proposition 4.2.6, part 1
pop-property₁ : ∀ {i} {X : Type i} → X → ⟪ X ⟫
pop-property₁ = Trunc→Pop ∘ ∣_∣

-- Proposition 4.2.6, part 2: this needs function extensionality.
-- We import the library file with the consequence of funext that we need.
open import lib.types.Pi
pop-property₂ : ∀ {i} {X : Type i} → is-prop ⟪ X ⟫
pop-property₂ = Π-is-prop (λ f → Π-is-prop (λ c → fixed-point f c))
