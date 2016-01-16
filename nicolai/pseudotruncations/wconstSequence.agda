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

{- weak constancy is defined in the 'Liblemmas' file. 
   We just define weak constancy for sequences here. -} 
wconst-chain : ∀ {i} → Sequence {i} → Type i
wconst-chain (A , f) = (n : ℕ) → wconst (f n)

{- first, we show that a weakly constant sequence for 
   which we have an a₀ : A₀ is contractible.
   We proceed step-wise. -}
module wconst-init {i} {C : Sequence {i}} (wc : wconst-chain C) (a₀ : fst C O) where

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


  
  {- This is overline(i) from the text:
     any a : A n is, in A ω , equal to a₀.
     note that this intentially replicates ins-const. -}
  ins-n-O : (n : ℕ) → (a : A n) → ins {C = C} n a == ins O a₀
  ins-n-O n a = 
    ins n a
      =⟨ glue n a ⟩
    ins (S n) (f n a)
      =⟨ ap (ins (S n)) (wc n _ _) ⟩
    ins (S n) (lift-point C a₀ (S n))
      =⟨ ! (lift-point-= C a₀ (S n)) ⟩
    ins O a₀
      ∎


  -- TODO TODO TODO
  postulate  
    glue-calculate : (n : ℕ) (a : A n) →
                     ! (glue n a) ∙ ins-n-O n a
                      ==
                     ins-n-O (S n) (f n a)
{-  glue-calculate n a = {!!} where
    calc-first =
      ins-n-O n a
        =⟨ {!idp!} ⟩
      glue n a ∙ (ap (ins (S n)) (wc n _ _)) ∙ (g-iter (S n)) ∙ idp
        =⟨ {!∙-unit-r !} ⟩
      glue n a ∙ ((ap (ins (S n)) (wc n _ _)) ∙ (g-iter (S n)))
        ∎ 
-}


  {- Now, we define overline(g) from the text;
     not much happens here!
     All we are doing is showing that commutativity of the 'triangle'
     is really enough. The hard part is the commutativity of the 
     'triangle' which, is shown via commutativity of the 'heptagon',
     which we have already done! -}
  glue-n-O : (n : ℕ) (a : A n)
             → (ins-n-O n a)
                ==
               (ins-n-O (S n) (f n a)) [ (λ w → w == ins O a₀) ↓ glue n a ]
               
  glue-n-O n a = from-transp _ (glue n a)
    -- now, let use calculate...
    (transport (λ w → w == ins O a₀) (glue n a) (ins-n-O n a)
      -- we use the version of trans-ap where the second function is constant
      =⟨ trans-ap₁ (idf _) (ins O a₀) (glue n a) (ins-n-O n a) ⟩
    ! (ap (idf _) (glue n a)) ∙ (ins-n-O n a)  
      =⟨ ap (λ p → (! p) ∙ (ins-n-O n a)) (ap-idf (glue n a)) ⟩ 
    ! (glue n a) ∙ (ins-n-O n a)
      =⟨ glue-calculate n a ⟩ -- maybe should be done here, NOT as an extra lemma!
    ins-n-O (S n) (f n a)
      ∎)

  -- We combine 'overline(i)' and 'overline(g)' to conclude:
  equal-n-O : (w : SC) → w == ins O a₀
  equal-n-O = SeqCo-ind ins-n-O glue-n-O

  -- Thus, the sequential colimit is contractible:
  SC-contr : is-contr SC
  SC-contr = ins O a₀ , (λ w → ! (equal-n-O w))


{- Let us now show that removing the first map from a weakly constant sequence 
   gives a weakly constant sequence. 
   Then, we show that we can remove any finite initial sequence.
   Of course, this is trivial; the conclusion of the statement asks for weak 
   constancy of nearly all of the maps, while the assumption gives weak constancy
   of all maps. -}  
removeFst-preserves-wconst : ∀ {i} → (C : Sequence {i}) → wconst-chain C → wconst-chain (removeFst C)
removeFst-preserves-wconst C wc n = wc (S n)

removeInit-preserves-wconst : ∀ {i} → (C : Sequence {i}) → (n : ℕ) → wconst-chain C → wconst-chain (removeInit C n)
removeInit-preserves-wconst C O wc = wc
removeInit-preserves-wconst C (S n) wc =
  removeInit-preserves-wconst (removeFst C) n
    (removeFst-preserves-wconst C wc)


{- The first main result: the colimit of a weakly constant sequence is propositional. -}
wconst-prop : ∀ {i} → (C : Sequence {i}) → wconst-chain C → is-prop (SeqCo C)
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

-- TODO sample applications??
