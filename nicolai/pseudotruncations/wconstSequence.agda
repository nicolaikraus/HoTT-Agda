{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.NType2

open import nicolai.pseudotruncations.Liblemmas
open import nicolai.pseudotruncations.SeqColim


module nicolai.pseudotruncations.wconstSequence where

wconst-chain : ∀ {i} → Chain {i} → Type i
wconst-chain (A , f) = (n : ℕ) → wconst (f n)

-- first, we show that a weakly constant sequence for which we have an a₀ : A₀ is contractible
module wconst-init {i} {C : Chain {i}} (wc : wconst-chain C) (a₀ : fst C O) where

  A = fst C
  f = snd C
  SC = SeqCo C

  -- first, we show that [ins] is weakly constant
  ins-wconst : (n : ℕ) → wconst (ins {C = C} n)
  ins-wconst n a₁ a₂ = 
    ins n a₁           =⟨ glue n a₁ ⟩
    ins (S n) (f n a₁) =⟨ ap (ins (S n)) (wc n a₁ a₂) ⟩
    ins (S n) (f n a₂) =⟨ ! (glue n a₂) ⟩
    ins n a₂           ∎

  -- iterate. Care: f-iter n is only f₀ⁿ⁻¹ !
  f-iter : (n : ℕ) → A n
  f-iter O = a₀
  f-iter (S n) = f n (f-iter n)

  -- iterated glue.
  g-iter : (n : ℕ) → ins {C = C} n (f-iter n) == ins O a₀
  g-iter O = idp
  g-iter (S n) = ! (glue n (f-iter n)) ∙ g-iter n

  -- aux lemma: g-iter can cancel out itself
  -- g-iter-cancel : (n : ℕ) → 

  -- note that this replicates ins-const.
  ins-n-O : (n : ℕ) → (a : A n) → ins {C = C} n a == ins O a₀
  ins-n-O n a = 
    ins n a
      =⟨ glue n a ⟩
    ins (S n) (f n a)
      =⟨ ap (ins (S n)) (wc n _ _) ⟩
    ins (S n) (f-iter (S n))
      =⟨ g-iter (S n) ⟩
    ins O a₀
      ∎

{- it does not work like this. Look at the paper, it need to be done clever (first get rid of the stuff which prevents path induction)!
  glue-n-O-aux : (n : ℕ) → (a : A n) → (p : _)
    ((glue n a) ∙ (ap (ins (S n)) p) ∙ (g-iter (S n)))
    ==
    ((glue n a) ∙ (glue (S n) (f n a)) ∙ (ap (ins (S (S n))) p) ∙ (g-iter (S (S n))))
  
  glue-n-O-aux n a = {!!}
-}


  -- TODO TODO TODO
  postulate  
    glue-calculate : (n : ℕ) → (a : A n) → ! (glue n a) ∙ ins-n-O n a == ins-n-O (S n) (f n a)
{-  glue-calculate n a = {!!} where
    calc-first =
      ins-n-O n a
        =⟨ {!idp!} ⟩
      glue n a ∙ (ap (ins (S n)) (wc n _ _)) ∙ (g-iter (S n)) ∙ idp
        =⟨ {!∙-unit-r !} ⟩
      glue n a ∙ ((ap (ins (S n)) (wc n _ _)) ∙ (g-iter (S n)))
        ∎ 
-}



  glue-n-O : (n : ℕ) → (a : A n) → (ins-n-O n a) == (ins-n-O (S n) (f n a)) [ (λ w → w == ins O a₀) ↓ glue n a ]
  glue-n-O n a = from-transp _ (glue n a)
    (transport (λ w → w == ins O a₀) (glue n a) (ins-n-O n a)
      =⟨  trans-ap (idf _) (λ w → ins O a₀) (glue n a) (ins-n-O n a) ⟩
    ! (ap (idf _) (glue n a)) ∙ (ins-n-O n a) ∙ ap (λ _ → ins O a₀) (glue n a) 
      =⟨ ap (λ p → ! p ∙ (ins-n-O n a) ∙ ap (λ _ → ins O a₀) (glue n a)) (ap-idf (glue n a)) ⟩
    ! (glue n a) ∙ (ins-n-O n a) ∙ ap (λ _ → ins O a₀) (glue n a) 
      =⟨ ! (∙-assoc (! (glue n a)) ((ins-n-O n a)) _) ⟩
    (! (glue n a) ∙ (ins-n-O n a)) ∙ ap (λ _ → ins O a₀) (glue {C = C} n a) 
      =⟨ ap (λ p → (! (glue n a) ∙ (ins-n-O n a)) ∙ p) (ap-const-at-point (ins O a₀) (glue n a)) ⟩
    (! (glue n a) ∙ (ins-n-O n a)) ∙ idp 
      =⟨ ∙-unit-r _ ⟩
    ! (glue n a) ∙ ins-n-O n a
      =⟨ glue-calculate n a ⟩ -- maybe should be done here, NOT as an extra lemma!
    ins-n-O (S n) (f n a)
      ∎)

  equal-n-O : (w : SC) → w == ins O a₀
  equal-n-O = SeqCo-ind ins-n-O glue-n-O

  SC-contr : is-contr SC
  SC-contr = ins O a₀ , (λ w → ! (equal-n-O w))



removeFst-preserves-wconst : ∀ {i} → (C : Chain {i}) → wconst-chain C → wconst-chain (removeFst C)
removeFst-preserves-wconst C wc n = wc (S n)

removeInit-preserves-wconst : ∀ {i} → (C : Chain {i}) → (n : ℕ) → wconst-chain C → wconst-chain (removeInit C n)
removeInit-preserves-wconst C O wc = wc
removeInit-preserves-wconst C (S n) wc =
  removeInit-preserves-wconst (removeFst C) n
    (removeFst-preserves-wconst C wc)


-- first main lemma !
wconst-prop : ∀ {i} → (C : Chain {i}) → wconst-chain C → is-prop (SeqCo C)
wconst-prop C wc = inhab-to-contr-is-prop (SeqCo-rec wc-prp-ins automatic) where

  A = fst C
  f = snd C
  
  wc-prp-ins : (n : ℕ) → A n → is-contr (SeqCo C)
  wc-prp-ins n a = equiv-preserves-level {n = ⟨-2⟩} (ignore-init C n ⁻¹) C'-contr where

    C' = removeInit C n
    A' = fst C'
    f' = snd C'

    a₀' : A' O
    a₀' = new-initial C n a

    wc' : wconst-chain C'
    wc' = removeInit-preserves-wconst C n wc

    C'-contr : is-contr (SeqCo C')
    C'-contr = wconst-init.SC-contr wc' a₀'

  automatic : (n : ℕ) (a : fst C n) → wc-prp-ins n a == wc-prp-ins (S n) (snd C n a)
  automatic n a = prop-has-all-paths (has-level-is-prop {n = ⟨-2⟩} {A = SeqCo C}) _ _
