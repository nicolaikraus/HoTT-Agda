{-# OPTIONS --without-K #-}

{- INDEX: Some constructions with non-recursive HITs,
   and related results.

   This formalization covers the hardest results of my
   paper titled "Constructions with non-recursive HITs".
   To be precise: I have formalized the result that all 
   functions in the sequence of approximations (see Section 6)
   are weakly constant, and that the colimit is thus 
   propositional. This requires a lot of lemmas. Some of 
   these lemmas are trivial on paper and only tedious in Agda,
   but many lemmas are (at least for me) even on paper far 
   from trivial. 

   Formalized are Section 2, Section 3 (without the example
   applications), especially the first main result; all of 
   Section 4 except Lemma 4.9, the definitions and principles 
   of Section 5, all of Section 6 expect the last corollaries.

   The parts of the paper that are not formalized are
   (A) the examples in Section 3
   (B) the statements of remarks
   (C) Lemma 4.9, 5.4, 5.5, and 5.6 
   (D) Theorem 5.7, Corollary 5.8, Theorem 6.2
   (E) the discussions and results in the concluding Section 7

   All of these are relatively easy compared with the results
   that are formalized. The items in (C) could be implemented
   easily, but are not very interesting on their own.
   The same is true for the second and third item in (D),
   which however depend on Theorem 5.7.
   Theorem 5.7 itself could be interesting to formalize. 
   However, it relies on the main result of 
       Capriotti, Kraus, Vezzosi,
       "Functions out of Higher Truncations".
   This result is formalized, but unfortunately in another
   library; thus, we omit Theorem 5.7 (for now) in the current 
   formalization. (E) would require (D) first.
   
   This development type-checks with Agda 2.4.2.5 and similar 
   versions (I assume with 2.4.2.x in general; same as the 
   HoTT library).
-}

module nicolai.pseudotruncations.NONRECURSIVE-INDEX where

{- Some preliminary definitions/lemmas, and an explanation
   why we need to work with the spheres defined by suspension-
   iteration of the form
   Σ¹⁺ⁿ :≡ Σⁿ ∘ Σ -}
open import nicolai.pseudotruncations.Preliminary-definitions
open import nicolai.pseudotruncations.Liblemmas

{- SECTION 2
   The Sequential colimit. I am aware that there is some
   overlap with lib/types/NatColim.agda -}
open import nicolai.pseudotruncations.SeqColim

{- Here is some prepartion for Section 3 -}
open import nicolai.pseudotruncations.wconst-preparation

{- The rather lengthy argument that some heptagon commutes;
   very tedious; this is still preparation for Section 3 -}
open import nicolai.pseudotruncations.heptagon

{- SECTION 3 (without the sample applications)
   One result of the paper: If we have a sequence of weakly 
   constant functions, then the colimit is propositional -}
open import nicolai.pseudotruncations.wconstSequence

{- SECTION 4
   The correspondance between loops and maps from spheres:
   a lot of tedious technical content. This was hard work for me!
   The results are in two files; first, essentially the fact that
   the 'pointed' 0-sphere [i.e. (bool, true)] is "as good as"
   the unit type if we consider pointed maps out of it.
   Second, the main lemmas. -}
open import nicolai.pseudotruncations.pointed-O-Sphere
open import nicolai.pseudotruncations.LoopsAndSpheres

{- SECTION 5 (mainly the definition and some auxiliary lemmas)
   Definition of pseudo-truncations -}
open import nicolai.pseudotruncations.PseudoTruncs

{- SECTION 6
   The sequence of approximations with increasing "connectedness-
   level", and the proof that every map is weakly constant,
   and the corollary that its colimit is propositional. -}
open import nicolai.pseudotruncations.PseudoTruncs-wconst-seq 
