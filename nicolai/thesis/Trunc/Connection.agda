{-# OPTIONS --without-K #-}

{- This module defines our notion of connectedness not requiring HITs.
   We define the generic n-connected version of a type, show that it is
   n-connected, and that it behaves like the original type above level n.
   We conclude by shoing this notion coincides with the usual notion.
   of connectedness in the presence of HITs. -}
module Trunc.Connection where

open import lib.Basics hiding (_⊔_)
open import lib.NType2
open import lib.Equivalences2
open import lib.types.Unit
open import lib.types.Nat hiding (_+_)
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Paths
open import lib.types.TLevel

open import Preliminaries
open import Pointed
open import UniverseOfNTypes

open import Trunc.Universal
open import Trunc.Basics
open import Trunc.TypeConstructors

open import HHHUU-ComplicatedTypes

-- Definition 7.6.1 is in the library:
-- lib.NConnected.is-connected

-- In this file, our own notion of connectedness is discussed.

open trunc-ty
open trunc-props

-- Definition 7.6.13
{- Our plain MLTT connectedness predicate.
   Because of predicativity issues, it has to live in one universe higher
   than its argument type C. Internally, we really want to quantify over
   truncation operators not only at the level of C, but also at levels below C.
   This would be the same in a theory with cumulative universes, but we are
   working in Agda. Since we are only going to actually use the truncation
   operator at one level lower than C, we restrict ourselves to this specific
   assumption in this particular development for no particular reason other
   than brevity of presentation. The reason for this difference of one level
   will become apparent in the definition of 'connection'. -}
module _ {i} (n : ℕ₋₂) (C : Type (lsucc i)) where
  is-connected⋆ : Type (lsucc (lsucc i))
  is-connected⋆ = (Tr : (X : Type i) → trunc-ty n X (lsucc i))
                  (TrC : trunc-ty n C (lsucc i))
                → is-contr ⟦ type TrC ⟧

{- The (n+1)-connected version, or n-connection of some pointed type A.
   Since we internally quantify over the type of truncations of a path space
   from a before being able to require an element in the truncation,
   predicativity issues force 'connection' to live in a universe one level
   higher than A.
   
   Take particular care in noting that the parameter n is in fact one-off,
   for example, The type 'connection (-2)' denotes the (-1)-connection. -}
module _ {i} (A : Type• i) where
  module con (n : ℕ₋₂) where
    -- Definition 7.6.11
    connection• : Type• (lsucc i)
    connection• =
      Σ• (A
        , ((λ b → (TrP : trunc-ty n (pt A == b) i) → ⟦ type TrP ⟧)
         , (λ TrP → cons TrP idp)))

    {- The base type of the (n+1)-connection:
      Σ A (λ b → (TrP : trunc-ty n (a == b) i) → ⟦ type TrP ⟧. -}
    connection : Type (lsucc i)
    connection = base connection•

    -- Lemma 7.6.14
    connection-is-connected : is-connected⋆ (S n) connection
    connection-is-connected Tr TrC = equiv-preserves-level (e ⁻¹) h where

      -- The supplied generic truncation operator is used only to truncate A.
      TrA : trunc-ty (S n) (base A) (lsucc i)
      TrA = Tr (base A)

      TrP : (b : base A) → trunc-ty n (pt A == b) i
      TrP = trunc-path.trunc {j = i} TrA (pt A)

      {- This definition typechecks since
              Σ A (λ b → ⟦ type (TrP b) ⟧
           ≡  Σ A (λ a → cons TrA (pt A) == cons TrA b)
         by construction of trunc-path.trunc. -}
      TrD : trunc-ty (S n) (Σ (base A) (λ b → ⟦ type (TrP b) ⟧)) (lsucc i)
      TrD = trunc-Σ.trunc {j = lsucc i} TrA
              (λ b → trunc-self.trunc (Path-≤ (type TrA) (cons TrA (pt A)) b))

      u : connection ≃ Σ (base A) (λ b → ⟦ type (TrP b) ⟧)
      u = equiv-Σ-snd {B = λ _ → Π _ _}  -- No idea why Agda wants this.
                      (λ b → Π₁-contr (trunc-inhab-contr {j = i} (TrP b)))

      e : ⟦ type TrC ⟧ ≃ ⟦ type TrD ⟧
      e = trunc-functor.fmap-equiv {j = lsucc i} TrC TrD u

      {- Note that
           ⟦ type TrD ⟧  ≡  Σ ⟦ type TrA ⟧ (λ tb → cons TrA (pt A) == tb)
         by construction of trunc-Σ.trunc. -}
      h : is-contr ⟦ type TrD ⟧
      h = pathfrom-is-contr (cons TrA (pt A))

  module con2 (n : ℕ) where
    open con (n -2)

    -- Lemma 7.6.12
    -- The (n+1)-connection of A coincides with A on dimension n+2 and above.
    connection-higher-dim : (Ω ^ n) connection• ≃• (Ω ^ n) A
    connection-higher-dim =
      forget-Ω^-Σ•₂ _ n (λ _ → Π-level (λ Tr → snd (type Tr)))

  open con public
  open con2 public

-- For the first time in the dependency chain, we assume HITs.
module with-hits where
  open import lib.types.Truncation
  open import lib.NConnected
  
  {- With the truncations of the HoTT community's library,
     our truncation types are always inhabited, and hence contractible. -}
  module _ {i j} where
    trunc : (n : ℕ₋₂) (A : Type i) → trunc-ty n A (i ⊔ j)
    trunc n A = record
      { type = (Trunc n A , Trunc-level)
      ; cons = [_]
      ; univ = λ U → is-eq
        (λ f → f ∘ [_]) (Trunc-rec (snd U)) (λ f → idp)
        (λ f → λ= (Trunc-elim (λ _ → =-preserves-level _ (snd U))
                              (λ a → idp)))}
      
    trunc-contr : {n : ℕ₋₂} {A : Type i} → is-contr (trunc-ty n A (i ⊔ j))
    trunc-contr = trunc-inhab-contr {j = j} (trunc _ _)

  -- Lemma 7.6.15
  -- Our connectedness⋆ is equivalent to HIT connectedness.
  module _ {i} {n : ℕ₋₂} {A : Type (lsucc i)} where
    conn⋆-conn : is-connected⋆ n A ≃ is-connected n A
    conn⋆-conn = Π₁-contr (trunc-contr {j = lsucc i})
              ∘e Π₁-contr (Π-level (λ _ → trunc-contr {j = lsucc i}))


-- Theorem 7.7.1
module _ (n : ℕ) where
  M• : Type• ｢ n + 2 ｣
  M• = connection• (_ , Loop n) (n -1)

  assertion-0 : has-level ⟨ n + 1 ⟩ (base M•)
  assertion-0 = snd (Σ-≤ (⟨ n ⟩ -Type-≤ ｢ n ｣)
                    (λ b → Π-≤ (trunc-ty _ (_ == b) _)
                               (λ tr → raise (raise (type tr)))))

  assertion-1 : ¬ (has-level ⟨ n ⟩ (base M•))
  assertion-1 =
      main' n
    ∘ –> (equiv-is-contr• (connection-higher-dim _ (n + 1)))
    ∘ (λ z → z (pt M•))
    ∘ –> has-level-equiv-contr-loops

  assertion-2 : is-connected⋆ ⟨ n ⟩ (base M•)
  assertion-2 = connection-is-connected _ _
