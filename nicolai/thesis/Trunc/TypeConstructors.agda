{-# OPTIONS --without-K #-}

{- In this module, we derive the truncations of
  * a truncated type,
  * the unit type,
  * dependent sums (and product types),
  * path spaces
  given truncations of their components.

  More commonly later on, we will be given a truncation operator Tr
  that returns a truncation for any given input type (at a fixed level).
  Instead of trying to show, say,

    Tr (Σ A (B ∘ cons (Tr A))) ≃ Σ (Tr A) (Tr ∘ B),

  directly, it turns out to be much easier to just *derive* the truncation on
  the left-hand side from Tr A and Tr ∘ B and then use unicity of truncation to
  deduce the above equivalence. Significant parts of the unicity proof would be
  duplicated in any direct proof of equivalence, while this approach allows us
  to avoid a number of manual elimination and propositional reduction steps. -}
module Trunc.TypeConstructors where

open import lib.Basics hiding (_⊔_)
open import lib.NType2
open import lib.Equivalences2
open import lib.types.Unit
open import lib.types.Nat hiding (_+_)
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Paths

open import Preliminaries
open import Pointed
open import UniverseOfNTypes

open import Trunc.Universal
open import Trunc.Basics


open trunc-ty
open trunc-props

module trunc-self {i} {n : ℕ₋₂} (A : n -Type i) where
  trunc : ∀ {j} → trunc-ty n ⟦ A ⟧ j
  trunc = record
    { type = A
    ; cons = idf _
    ; univ = λ _ → snd (ide _) }

module trunc-⊤ {n : ℕ₋₂} = trunc-self {n = n} ⊤-≤

-- *** Lemma 6.9 ***
{- The truncation of a dependent sum type (where the family depends
   only on the truncation of the first component) is the dependent sums
   of the truncations. -}
module trunc-Σ {ia ib j} {n : ℕ₋₂} {A : Type ia}
               (TrA : trunc-ty n A (ia ⊔ ib ⊔ j))
               {B : ⟦ type TrA ⟧ → Type ib}
               (TrB : (ta : ⟦ type TrA ⟧) → trunc-ty n (B ta) (ib ⊔ j)) where

  trunc : trunc-ty n (Σ A (B ∘ cons TrA)) (ib ⊔ j)
  trunc = record
    { type = Σ-≤ (type TrA) (type ∘ TrB)
    ; cons = λ {(a , b) → (cons TrA a , cons (TrB (cons TrA a)) b)}
    ; univ = snd ∘ e } where

    e : (U : n -Type _) → _
    e U =
      (⟦ Σ-≤ (type TrA) (type ∘ TrB) ⟧         → ⟦ U ⟧)  ≃⟨ curry-equiv ⟩
      ((ta : ⟦ type TrA ⟧) → ⟦ type (TrB ta) ⟧ → ⟦ U ⟧)  ≃⟨ equiv-Π-r eb ⟩
      ((ta : ⟦ type TrA ⟧) → B ta              → ⟦ U ⟧)  ≃⟨ ea ⟩
      ((a : A)             → B (cons TrA a)    → ⟦ U ⟧)  ≃⟨ curry-equiv ⁻¹ ⟩
      (Σ A (B ∘ cons TrA)                      → ⟦ U ⟧)  ≃∎ where
   
      ea = dup {j = ib ⊔ j} TrA (λ ta → B ta →-≤ U)
      eb = λ ta → up {j = ib ⊔ j} (TrB ta) U

-- Products are a special case of dependent sums.
module trunc-× {ia ib j} {n : ℕ₋₂} {A : Type ia} {B : Type ib}
               (TrA : trunc-ty n A (ia ⊔ ib ⊔ j))
               (TrB : trunc-ty n B (ib ⊔ j)) =
  trunc-Σ {j = j} TrA (λ _ → TrB)

-- Lemma 7.6.9
{- The n-truncation of a path space is the path space of the (n+1)-truncation.
   The use of the encode-decode method is the reason why we have to assume
   elimination into Type (lsucc i): large recursion is used to define
   the type of codes. -}
module trunc-path {i j} {n : ℕ₋₂} {A : Type i} (TrA : trunc-ty (S n) A (lsucc (i ⊔ j))) where
  private
    l : ULevel
    l = i ⊔ j

    TrAA : trunc-ty (S n) (A × A) (lsucc l)
    TrAA = trunc-×.trunc {j = lsucc l} TrA TrA

    module MA  = trunc-props {j = lsucc l} {k = l} TrA
    module MAA = trunc-props {j = lsucc l} {k = l} TrAA
--    module MAL = trunc-elim {j = _} TrAA

  {- There is some Yoneda hidden here that would enable us to express the final
     equivalence e neatly as a sequence of trivial steps like in trunc-Σ;
     unfortunately we lack the necessary category theoretic framework
     in this code base. -} 
  module code (U : n -Type l) where
    abstract
      {- Large recursion used here.
         Since we cannot talk about the truncation of a₀ == a₁ yet,
         we instead talk about the continuation type (a₀ == a₁ → U) → U
         for any n-type U instead. -}
      code : ⟦ type TrAA ⟧ → n -Type l
      code = rec {j = lsucc l} TrAA (n -Type-≤ l)
                 (λ {(a₀ , a₁) → (a₀ == a₁ → ⟦ U ⟧) →-≤ U})

      code-β : {a₀ a₁ : A} → ⟦ code (cons TrAA (a₀ , a₁)) ⟧
                           ≃ ((a₀ == a₁ → ⟦ U ⟧) → ⟦ U ⟧)
      code-β = coe-equiv (ap ⟦_⟧ (rec-β TrAA _))

    -- We can encode a path in the truncation, ...
    encode : {ta₀ ta₁ : ⟦ type TrA ⟧} → ta₀ == ta₁ → ⟦ code (ta₀ , ta₁) ⟧
    encode idp = MA.elim (λ ta → raise (code (ta , ta)))
                         (λ _ → <– code-β (λ f → f idp)) _

    --- ...reducing when coming from a path in the original type.
    encode-β : {a₀ a₁ : A} (p : a₀ == a₁) (f : a₀ == a₁ → ⟦ U ⟧)
             → –> code-β (encode (ap (cons TrA) p)) f == f p
    encode-β idp = app= (ap (–> code-β) (MA.elim-β _) ∙ <–-inv-r code-β _)

    -- We can decode into the U-continuation of a path in the truncation, ...
    decode : {ta₀ ta₁ : ⟦ type TrA ⟧}
           → ⟦ code (ta₀ , ta₁) ⟧ → (ta₀ == ta₁ → ⟦ U ⟧) → ⟦ U ⟧
    decode = MAA.elim
      (λ {(ta₀ , ta₁) → _ →-≤ (ta₀ == ta₁ → ⟦ U ⟧) →-≤ raise U})
      (λ _ c g → –> code-β c (g ∘ ap (cons TrA))) _ where

    -- ...reducing 
    decode-β : {a₀ a₁ : A} (c : ⟦ code (cons TrAA (a₀ , a₁)) ⟧)
               (g : cons TrA a₀ == cons TrA a₁ → ⟦ U ⟧)
             → decode c g == –> code-β c (g ∘ ap (cons TrA))
    decode-β = app= ∘ app= (MAA.elim-β _)

    -- encoding followed by decoding produces the expected continuation
    decode-encode : {ta₀ ta₁ : ⟦ type TrA ⟧} (q : ta₀ == ta₁)
                    (g : ta₀ == ta₁ → ⟦ U ⟧) → decode (encode q) g == g q
    decode-encode idp = MA.elim
      (λ ta → Π-≤ (ta == ta → ⟦ U ⟧)
                  (λ g → Path-≤ (raise U) (decode (encode idp) g) (g idp)))
      (λ _ g → decode-β (encode idp) g ∙ encode-β idp (g ∘ ap (cons TrA))) _

  {- This is a stronger form of Lemma 7.6.10: 
     we do not need to assume that the (n+1)-truncation of a₀ == a₁ existes,
     is can be *defined* in the way stated in the lemma.
     That means that, if it exists, it is exactly what we want it to be. -}
  trunc : (a₀ a₁ : A) → trunc-ty n (a₀ == a₁) l
  trunc a₀ a₁ = record
    { type = Path-< (type TrA) (cons TrA a₀) (cons TrA a₁)
    ; cons = ap (cons TrA)
    ; univ = snd ∘ e } where

    e : (U : _) → (cons TrA a₀ == cons TrA a₁ → ⟦ U ⟧) ≃ (a₀ == a₁ → ⟦ U ⟧)
    e U = equiv u v u-v v-u where
      open code U

      u : (cons TrA a₀ == cons TrA a₁ → ⟦ U ⟧) → a₀ == a₁ → ⟦ U ⟧
      u g = g ∘ ap (cons TrA)

      v : (a₀ == a₁ → ⟦ U ⟧) → cons TrA a₀ == cons TrA a₁ → ⟦ U ⟧
      v f q = –> code-β (encode q) f

      u-v : (f : a₀ == a₁ → ⟦ U ⟧) → u (v f) == f
      u-v f = λ= (λ p → encode-β p f)

      v-u : (g : cons TrA a₀ == cons TrA a₁ → ⟦ U ⟧) → v (u g) == g
      v-u g = λ= (λ q → ! (decode-β (encode q) g) ∙ decode-encode q g)
