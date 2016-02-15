{-# OPTIONS --without-K #-}

{- Here, truncations with propositional computational behaviour are defined.
   This lack of a definitional β-rule enabled us to talk about this notion
   inside type theory without truncations, albeit complicating setup and proofs.

   After definition and basic accessories concerning universal properties,
   recursion and elimination, we prove that truncation is functorial.
   With this, we turn our attention to the problem of uniqueness of truncation,
   i.e. the type of truncations of a given type being propositional. -}
module Trunc.Basics where

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

-- Definition 7.6.4
record trunc-ty {i} (n : ℕ₋₂) (A : Type i)
                (j : ULevel) : Type (lsucc (i ⊔ j)) where
  constructor ty-cons
  field
    type : n -Type i
    cons : A → ⟦ type ⟧
    univ : univ-Type type cons j

module _ {i} {n : ℕ₋₂} {A : Type i} where
  trunc-ty-lower : ∀ {j₀} (j₁ : ULevel) → trunc-ty n A (j₀ ⊔ j₁) → trunc-ty n A j₀
  trunc-ty-lower {j₀} j₁ (ty-cons t c u) = ty-cons t c (univ-lower t c (j₀ ⊔ j₁) u)

{- Since Agda does not support specifying ordering relations on universe levels,
   we encounter an awkward dependency inversion: the index k needs to be
   specified in the module arguments, since the truncation type depends on it,
   even though we would rather have it at each individual definition.
   This shortcoming will be the source of many explicitely specified levels. -}
module trunc-props {i} {n : ℕ₋₂} {A : Type i} {j k} (tr : trunc-ty n A (i ⊔ j ⊔ k)) where
  open trunc-ty tr

  up : (U : n -Type k) → (⟦ type ⟧ → ⟦ U ⟧) ≃ (A → ⟦ U ⟧)
  up U = ((λ f → f ∘ cons) , univ-lower type cons (i ⊔ j ⊔ k) univ U)

  dup : (U : ⟦ type ⟧ → n -Type k) → ((ta : ⟦ type ⟧) → ⟦ U ta ⟧) ≃ ((a : A) → ⟦ U (cons a) ⟧)
  dup U = ((λ f → f ∘ cons) , with-univ.duniv type cons (univ-lower type cons (i ⊔ j ⊔ k) univ) U)

  abstract
    rec : (U : n -Type k) → (A → ⟦ U ⟧) → ⟦ type ⟧ → ⟦ U ⟧
    rec U = <– (up U)

    elim : (U : ⟦ type ⟧ → n -Type k) → ((a : A) → ⟦ U (cons a) ⟧) → (ta : ⟦ type ⟧) → ⟦ U ta ⟧
    elim U = <– (dup U)

    rec-β : {U : n -Type k} {f : A → ⟦ U ⟧} (a : A) → rec U f (cons a) == f a
    rec-β {U} {f} a = app= (<–-inv-r (up U) f) a

    elim-β : {U : ⟦ type ⟧ → n -Type k} {f : (a : A) → ⟦ U (cons a) ⟧} (a : A) → elim U f (cons a) == f a
    elim-β {U} {f} a = app= (<–-inv-r (dup U) f) a

{- Truncation acts as a functor.
   While tedious, we state all lemmata in their most general form.
   Instead of assuming an n-truncation operator, we individually assume
   a truncation for each type we need. While seeming overly convoluted
   at first, this generality will actually pay off with an unconventional
   use of fmap-equiv in showing that trunc-ty is propositional. -}
module trunc-functor {n : ℕ₋₂} where
  open trunc-ty
  open trunc-props

  -- The functorial action of truncation (truncation preserves maps).
  module _ {ia ib j} where
    module fmap {A : Type ia} {B : Type ib}
                (TrA : trunc-ty n A (ia ⊔ ib ⊔ j))
                (TrB : trunc-ty n B (ia ⊔ ib ⊔ j))
                (f : A → B) where
      map : ⟦ type TrA ⟧ → ⟦ type TrB ⟧
      map = rec {j = ia ⊔ ib ⊔ j} TrA (type TrB) (cons TrB ∘ f)

      β : (a : A) → map (cons TrA a) == cons TrB (f a)
      β = rec-β TrA {type TrB}

  -- The functorial action preserves the identity.
  module _ {i j} {A : Type i} (TrA : trunc-ty n A (i ⊔ j)) where
    private
      module I  = fmap {j = i ⊔ j} TrA TrA (idf _)
      
    fmap-fuse-id : (ta : ⟦ type TrA ⟧) → I.map ta == ta
    fmap-fuse-id = elim {j = i ⊔ j} TrA (λ ta → Path-≤ (type TrA) (I.map ta) ta) I.β

  -- The functorial action preserves composition.
  module _ {ia ib ic j} where
    private
      l : ULevel
      l = ia ⊔ ib ⊔ ic ⊔ j

    module _ {A : Type ia} {B : Type ib} {C : Type ic}
             (TrA : trunc-ty n A l)
             (TrB : trunc-ty n B l)
             (TrC : trunc-ty n C l)
             (f : A → B) (g : B → C) where
      private
        module F  = fmap {j = l} TrA TrB f
        module G  = fmap {j = l} TrB TrC g
        module GF = fmap {j = l} TrA TrC (g ∘ f)

      open trunc-props

      fmap-fuse-∘ : (ta : ⟦ type TrA ⟧) → GF.map ta == G.map (F.map ta)
      fmap-fuse-∘ = elim {j = l} TrA (λ ta →
                      Path-≤ (type TrC) (GF.map ta) (G.map (F.map ta))) $ λ a →
        GF.map (cons TrA a)        =⟨ GF.β a ⟩
        cons TrC (g (f a))         =⟨ ! (G.β (f a)) ⟩
        G.map (cons TrB (f a))     =⟨ ap G.map (! (F.β a)) ⟩
        G.map (F.map (cons TrA a)) ∎

  {- Corollary: truncation preserves equivalences.
     The below general form produces a unexpected benefit: the underlying
     type of a truncation is unique up to constructor-preserving equivalence. -}
  module _ where
    private
      module _ {ia ib j} where
        private
          l : ULevel
          l = ia ⊔ ib ⊔ j

        module half {A : Type ia} {B : Type ib}
                    (TrA : trunc-ty n A l)
                    (TrB : trunc-ty n B l)
                    (e : A ≃ B) where
          module F  = fmap {j = l} TrA TrB (–> e)
          module G  = fmap {j = l} TrB TrA (<– e)
          module BB = fmap {j = l} TrB TrB

          f-g : (tb : ⟦ type TrB ⟧) → F.map (G.map tb) == tb
          f-g tb =
              F.map (G.map tb)
            =⟨ ! (fmap-fuse-∘ {j = l} TrB TrA TrB (<– e) (–> e) tb) ⟩
              BB.map (–> e ∘ <– e) tb
            =⟨ app= (ap BB.map (λ= (<–-inv-r e))) tb ⟩
              BB.map (idf _) tb
            =⟨ fmap-fuse-id {j = l} TrB tb ⟩
              tb
            ∎
    
    module _ {ia ib j} where
      module _ {A : Type ia} {B : Type ib}
               (TrA : trunc-ty n A (ia ⊔ ib ⊔ j))
               (TrB : trunc-ty n B (ia ⊔ ib ⊔ j))
               (e : A ≃ B) where
        private
          module H = half {j = j} TrA TrB e
          module K = half {j = j} TrB TrA (e ⁻¹)

        fmap-equiv : ⟦ type TrA ≃-≤ type TrB ⟧
        fmap-equiv = equiv H.F.map K.F.map H.f-g K.f-g

{- The type of n-truncations of A is propositional:
   truncations are unique if existent. -}
module _ {i} {n : ℕ₋₂} {A : Type i} where
  open trunc-ty
  open trunc-functor

  {- For the purpose of this module, it will be easier
     for us to regard trunc-ty as a left-associatived Σ-type.
     In this way, we may examine the equality on the first component
     while disregarding the second one, which is a proposition. -}
  private
    e : ∀ {j} → trunc-ty n A j ≃ Σ (Σ _ _) _
    e = equiv (λ {(ty-cons t c u) → ((t , c) , u)})
              (λ {((t , c) , u) → ty-cons t c u})
              (λ _ → idp) (λ _ → idp)

    {- First, let us structurally decompose the combined equality
      over the type and cons record fields of trunc-ty.
      Note that this kind of lemma would be superfluous in
      a proof assistant fully supporting univalent foundations. -}
    path : (U V : Σ (n -Type i) (λ ty → A → ⟦ ty ⟧))
         → (U == V) ≃ Σ (⟦ fst U ⟧ ≃ ⟦ fst V ⟧) (λ e → –> e ∘ snd U == snd V)
    path ((X , u) , f) ((Y , v) , g) = equiv-Σ eq₁ (_⁻¹ ∘ eq₂)
                                     ∘e =Σ-eqv _ _ ⁻¹ where
      eq₁ : ((X , u) == (Y , v)) ≃ (X ≃ Y)
      eq₁ =
        (X , u) == (Y , v)                   ≃⟨ =Σ-eqv _ _ ⁻¹ ⟩
        Σ (X == Y) (λ p → u == v [ _ ↓ p ])  ≃⟨ Σ₂-contr h ⟩ 
        X == Y                               ≃⟨ ua-equiv ⁻¹ ⟩
        X ≃ Y                                ≃∎ where

        h : (p : X == Y) → is-contr (u == v [ _ ↓ p ])
        h _ = ↓-level (λ _ → has-level-is-prop)

      eq₂ : (e : X ≃ Y) → (–> e ∘ f == g) ≃ (f == g [ _ ↓ <– eq₁ e ])
      eq₂ = λ e →
        –> e ∘ f == g                    ≃⟨ app=-equiv ⟩
        (∀ a → –> e (f a) == g a)        ≃⟨ equiv-Π-r (λ a → ↓-idf-ua-equiv e) ⟩
        (∀ a → f a == g a [ _ ↓ ua e ])  ≃⟨ ↓-cst→app-equiv ⟩
        (f == g [ _ ↓ ua e ])            ≃⟨ ↓-cst2-equiv _ _ ⟩
        (f == g [ _ ↓ <– eq₁ e ])        ≃∎

  module _ {j} where
    {- Important special case of the general form of fmap-equiv:
       the underlying type of a truncation is unique
       up to constructor-preserving equivalence. -}
    module unique (Tr₁ : trunc-ty n A (i ⊔ j))
                  (Tr₂ : trunc-ty n A (i ⊔ j)) where
      type-equiv : ⟦ type Tr₁ ≃-≤ type Tr₂ ⟧
      type-equiv = fmap-equiv {j = j} Tr₁ Tr₂ (ide _)
  
      cons-path : –> type-equiv ∘ cons Tr₁ == cons Tr₂
      cons-path = λ= (fmap.β {j = j} Tr₁ Tr₂ (idf _))

      type-cons-path : Path {A = Σ (n -Type i) (λ ty → A → ⟦ ty ⟧)}
                            (fst (–> e Tr₁)) (fst (–> e Tr₂))
      type-cons-path = <– (path _ _) (type-equiv , cons-path)

    -- Lemma 7.6.7
    -- We are now ready to prove propositionality of trunc-ty.
    trunc-ty-prop : is-prop (trunc-ty n A _)
    trunc-ty-prop = all-paths-is-prop $ λ Tr₀ Tr₁ → <– (equiv-ap e _ _) (pair=
      (unique.type-cons-path Tr₀ Tr₁)
      (prop-has-all-paths-↓ (Π-level (λ _ → is-equiv-is-prop _))))

    trunc-inhab-contr : trunc-ty n A _ → is-contr (trunc-ty n A _)
    trunc-inhab-contr Tr = (Tr , prop-has-all-paths trunc-ty-prop _)

-- Corollary 7.6.8 (for completeness; 
-- not used later in this formalisation)
trunc-ty-gen-prop : (i j : ULevel) → is-prop ((nA : ℕ₋₂ × Type i) → trunc-ty (fst nA) (snd nA) (i ⊔ j))
trunc-ty-gen-prop i j = Π-level {A = ℕ₋₂ × Type i}
                                 {B = λ nA → trunc-ty (fst nA) (snd nA) (i ⊔ j)}
                                 {n = ⟨-1⟩}
                                 (λ nA → trunc-ty-prop {n = fst nA} {A = snd nA} {j = j})
