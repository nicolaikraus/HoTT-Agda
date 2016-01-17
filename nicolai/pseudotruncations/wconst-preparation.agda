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


module nicolai.pseudotruncations.wconst-preparation where


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

  
  {- Now, we want to define what is overline(i) is the paper
     (here, we call it î-def); that is:
     any a : A n is, if moved to A ω , equal to a₀.

     It is easy to define this, but the tricky part is that
     afterwards, we need to be able to reason about it.
     The 'equational reasoning' combinators are not suitable 
     at all for this.

     What we use are the 'reified equational reasoning combinators',
     which allow this sort of thing. These are in the HoTT library,
     implemented by Guillaume Brunerie [I have extended it a bit
     in order to make it useable in my situation]. 
     
     For an introduction to the concept, see the file

                   lib.types.PathSeq.

     -}

  î-def : (n : ℕ) → (a : A n) → (ins {C = C} n a) =-= (ins O a₀)
  î-def n a = 
    ins n a
      =⟪ glue n a ⟫
    ins (S n) (f n a)
      =⟪ ap (ins (S n)) (wc n _ _) ⟫
    ins (S n) (lift-point C a₀ (S n))
      =⟪ ! (lift-point-= C a₀ (S n)) ⟫
    ins O a₀
      ∎∎ 
  
  {- It was easy to define î; it is more difficult to show that it satisfied
     the required coherence.
     This is the 'heptagon-proof'; we present it in 
     nicolai.pseudotruncations.heptagon.agda.
  -}
