{-# OPTIONS --without-K #-}

open import library.Basics hiding (Type ; Σ)
open import library.types.Sigma

open import Sec2preliminaries 
open import Sec3hedberg
open import Sec4hasConstToSplit


-- In this section, we require function extensionality again.

module Sec6populatedness where

-- Definition 6.1
Pop : Type → Type
Pop X = (f : X → X) → const f → fix f

-- Theorem 6.2
Trunc→Pop : {X : Type} → Trunc X → Pop X
Trunc→Pop z f c = rec {P = fix f} (fixed-point f c) (to-fix f c) z


-- Lemma 6.3
module _ {X : Type} where

  pop→splitSup→X : Pop X → splitSup X → X
  pop→splitSup→X pop sps = fst (pop (fst fc) (snd fc)) where
                             fc = (snd hasConst↔splitSup sps) 

  use-funct : (splitSup X → X) → Trunc (splitSup X) → Trunc X
  use-funct f = trunc-functorial f

  tr-hst-X→pop : (Trunc (splitSup X) → Trunc X) → Pop X
  tr-hst-X→pop g f c = rec (fixed-point f c) (to-fix f c) (g ∣ hasConst→splitSup (f , c) ∣) 

  -- we formulate the two logical equivalence that we will need explicitly:
  pop-alt : Pop X ↔ (Trunc (splitSup X) → Trunc X)
  pop-alt = use-funct ∘ pop→splitSup→X , tr-hst-X→pop

  pop-alt' : Pop X ↔ (splitSup X → X)
  pop-alt' = pop→splitSup→X , tr-hst-X→pop ∘ use-funct

  
-- Theorem 6.4
pop-alt₂ : {X : Type} → Pop X ↔₀₁ ((P : Type) → (is-prop P) → (X ↔ P) → P)
pop-alt₂ {X} = one , two where

  one : Pop X → (P : Type) → is-prop P → (X ↔ P) → P
  one pop P pp (xp , px) = xp (fst (pop f c)) where
    f : X → X
    f = px ∘ xp
    c : const f
    c x₁ x₂ = ap px (prop-has-all-paths pp _ _)

  two : ((P : Type) → is-prop P → (X ↔ P) → P) → Pop X
  two rest f c = rest (fix f) (fixed-point f c) (to-fix f c , from-fix f)



-- Theorem 6.5
pop-property₁ : {X : Type} → X → Pop X
pop-property₁ = Trunc→Pop ∘ ∣_∣

-- this (and the following results of this section) needs function extensionality
open import library.types.Pi

pop-property₂ : {X : Type} → is-prop (Pop X)
pop-property₂ = Π-is-prop (λ f → Π-is-prop (λ c → fixed-point f c))


-- Theorem 6.6
hasConst↔PopX→X : {X : Type} → (hasConst X) ↔ (Pop X → X)
hasConst↔PopX→X {X} = hasConst→PopX→X , rev where

  hasConst→PopX→X : hasConst X → Pop X → X
  hasConst→PopX→X (f , c) pop = fst (pop f c)

  rev : (Pop X → X) → hasConst X
  rev pp = (pp ∘ pop-property₁) ,
           (λ x₁ x₂ → ap pp (prop-has-all-paths pop-property₂ _ _))

-- Theorem 6.6, second part
prop→hasConst×PopX→X : {X : Type} → (is-prop X) → (hasConst X) × (Pop X → X)
prop→hasConst×PopX→X p = fc , fst hasConst↔PopX→X fc where

  fc = idf _ , prop-has-all-paths p


-- Theorem 6.7
pop-idem : {X : Type} → (Pop (Pop X)) ≃ (Pop X)
pop-idem {X} = equiv f g auto₁ auto₂ where

  f = snd (prop→hasConst×PopX→X pop-property₂)
  g = pop-property₁

  auto₁ = λ _ → prop-has-all-paths pop-property₂ _ _
  auto₂ = λ _ → prop-has-all-paths pop-property₂ _ _
