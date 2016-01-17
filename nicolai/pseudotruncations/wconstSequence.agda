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
open import lib.types.PathSeq

open import nicolai.pseudotruncations.Liblemmas
open import nicolai.pseudotruncations.SeqColim



{- The main work is done in two separate files. 

   The first defines some general lemmas
   and constructs what is overline(i) in the paper. 

   The second is the 'heptagon-argument', a very 
   tedious calculation with paths, which constructs
   what is overline(g) in the paper -- the coherence
   laws for overline (i). -}
open import nicolai.pseudotruncations.wconst-preparation
open import nicolai.pseudotruncations.heptagon


module nicolai.pseudotruncations.wconstSequence where


  {- As a first step, assume we are given a weakly constant
     sequence with an inhabitant of the first type. -}
  module _ {i} {C : Sequence {i}} (wc : wconst-chain C) (a₀ : fst C O) where

    {- We want to show that the colimit of this sequence is 
       contractible.
       The heart of the argument are the definitions of the data
       that is needed in order to apply the induction principle
       of the sequential colimit.
       We call these î and ĝ. They are not constructed here, but
       in two separate files; the construction of ĝ is very tedious.
       Here, we just load them from the files where they are defined.
    -}

    {- First, some preliminary lemmas and the definition of î,
       defined in the following module: -}
    open wconst-init {i} {C} wc a₀ 

    î : (n : ℕ) → (a : A n) → (ins {C = C} n a) =-= (ins O a₀)
    î = î-def

    {- from î, we get the 'real' overline(i) just by applying ↯,
       i.e. by getting the path out of the sequence î -}
    ins-n-O : (n : ℕ) → (a : A n) → ins {C = C} n a == ins O a₀
    ins-n-O n a = ↯ (î-def n a)


    {- The difficult part is ĝ, in the paper called 'overline(g)'. 
       It is defined in heptagon.agda and just loaded here. -}
    
    ĝ : (n : ℕ) → (a : A n)
        → (↯ ((î (S n) (f n a)) ⋯ (‼ (î n a) ⋯ toSeq (glue n a)))) == idp
    ĝ n a = ĝ-def wc a₀ n a


    -- from ĝ, we should be able to get this postulate:
    postulate
      ins-glue-coh : (n : ℕ) (a : A n)
                     → ins-n-O (S n) (f n a) ∙ ! (ins-n-O n a) ∙ glue n a == idp
    -- ins-glue-coh n a = {!ins-n-O n a !} --  {!ĝ n a!}



    {- Now, we define the 'real' overline(g) from the text;
       this is just the 'unwrapped' version of ĝ, and not much happens
       here!
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
        -- we use the adhoc lemma to 're-order' paths
        =⟨ ! (adhoc-lemma (ins-n-O (S n) (f n a)) (ins-n-O n a) (glue n a) (ins-glue-coh n a)) ⟩ 
      ins-n-O (S n) (f n a)
        ∎)

    -- We combine 'overline(i)' and 'overline(g)' to conclude:
    equal-n-O : (w : SC) → w == ins O a₀
    equal-n-O = SeqCo-ind ins-n-O glue-n-O

    -- Thus, the sequential colimit is contractible:
    SC-contr : is-contr SC
    SC-contr = ins O a₀ , (λ w → ! (equal-n-O w))

{- This completes the proof that the sequential colimit of a weakly constant 
   sequence with *inhabited first type* is contractible.
   Let us now work with general weakly constant sequences again.

   First, let us now show that removing the first map from a weakly constant sequence 
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



{- THE FIRST MAIN RESULT: 
   the colimit of a weakly constant sequence is propositional. -}

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
    C'-contr = SC-contr wc' a₀'

  automatic : (n : ℕ) (a : fst C n) → wc-prp-ins n a == wc-prp-ins (S n) (snd C n a)
  automatic n a = prop-has-all-paths (has-level-is-prop {n = ⟨-2⟩} {A = SeqCo C}) _ _

-- TODO sample applications??




