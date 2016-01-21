{-# OPTIONS --without-K #-}

-- INDEX: Some constructions with non-recursive HITs,
-- and related results.

{- Currently under construction! 
   Please check again in a few days to find a more 
   complete formalization.
   Thanks :-)

   Only the completed results are imported here.
   Some further results in files of this repository 
   are 'mostly' formalized but have some gaps and 
   are thus not imported here.

   Type-checks with Agda 2.4.2.5 and similar versions
   (I assume with 2.4.2.x in general; same as the library).
-}



{- Some preliminary definitions/lemmas, nothing interesting -}
open import nicolai.pseudotruncations.Preliminary-definitions
open import nicolai.pseudotruncations.Liblemmas

{- The Sequential colimit. I am aware that there is some
   overlap with lib/types/NatColim.agda -}
open import nicolai.pseudotruncations.SeqColim

{- Here is some 'prepartion' -}
open import nicolai.pseudotruncations.wconst-preparation

{- The rather lengthy argument that some heptagon commutes;
   very tedious -}
open import nicolai.pseudotruncations.heptagon

{- Main result: If we have a sequence of weakly constant 
   functions, then the colimit is propositional -}
open import nicolai.pseudotruncations.wconstSequence

{- The correspondance between loops and maps from spheres:
   a lot of tedious technical content. This was hard work for me!
   The results are in two files; first, essentially the fact that
   the 'pointed' 0-sphere [i.e. (bool, true)] is "as good as"
   the unit type if we consider pointed maps out of it.
   Second, the main lemmas. -}
open import nicolai.pseudotruncations.pointed-O-Sphere
open import nicolai.pseudotruncations.LoopsAndSpheres
