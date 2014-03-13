{-# OPTIONS --without-K #-}

{-
  Favonia:  I was trying to generalize OneSkeleton but failed
  to achieve what I wanted.  Nicolai then told me this HIT
  which is suitable for the constancy lemma I was looking for.
  This construction should be attributed to Paolo Capriotti
  and Nicolai Kraus. [1]

  [1] Eliminating Higher Truncations via Constancy
      by Paolo Capriotti and Nicolai Kraus
      (in preparation/work in progress)
-}

open import HoTT

module experimental.TwoConstancyHIT {i} {A : Type i} where

module _ where
  private
    data #TwoConstancy-aux : Type i where
      #point : A → #TwoConstancy-aux

    data #TwoConstancy : Type i where
      #two-constancy : #TwoConstancy-aux → (Unit → Unit) → #TwoConstancy

  TwoConstancy : Type i
  TwoConstancy = #TwoConstancy

  point : A → TwoConstancy
  point a = #two-constancy (#point a) _

  postulate  -- HIT
    link₀ : ∀ a₁ a₂ → point a₁ == point a₂

    link₁ : ∀ a₁ a₂ a₃ → link₀ a₁ a₂ ∙' link₀ a₂ a₃ == link₀ a₁ a₃

    TwoConstancy-level : has-level ⟨1⟩ TwoConstancy

  module TwoConstancyElim
    {l} {P : TwoConstancy → Type l}
    (p : ∀ x → has-level ⟨1⟩ (P x))
    (point* : ∀ a → P (point a))
    (link₀* : ∀ a₁ a₂ → point* a₁ == point* a₂ [ P ↓ link₀ a₁ a₂ ])
    (link₁* : ∀ a₁ a₂ a₃
      →  link₀* a₁ a₂ ∙'ᵈ link₀* a₂ a₃
      == link₀* a₁ a₃
      [ (λ p → point* a₁ == point* a₃ [ P ↓ p ]) ↓ link₁ a₁ a₂ a₃ ]) where

    f : Π TwoConstancy P
    f = f-aux phantom phantom phantom where

      f-aux : Phantom p → Phantom link₀* → Phantom link₁* → Π TwoConstancy P
      f-aux phantom phantom phantom (#two-constancy (#point a) _) = point* a

    postulate  -- HIT
      link₀-β : ∀ a₁ a₂ → apd f (link₀ a₁ a₂) == link₀* a₁ a₂

    private
      lemma : ∀ a₁ a₂ a₃
            → apd f (link₀ a₁ a₂ ∙' link₀ a₂ a₃)
           == link₀* a₁ a₂ ∙'ᵈ link₀* a₂ a₃
      lemma a₁ a₂ a₃ =
        apd f (link₀ a₁ a₂ ∙' link₀ a₂ a₃)
          =⟨ apd-∙' f (link₀ a₁ a₂) (link₀ a₂ a₃) ⟩
        apd f (link₀ a₁ a₂) ∙'ᵈ apd f (link₀ a₂ a₃)
          =⟨ link₀-β a₁ a₂ |in-ctx (λ u → u ∙'ᵈ apd f (link₀ a₂ a₃)) ⟩
        link₀* a₁ a₂ ∙'ᵈ apd f (link₀ a₂ a₃)
          =⟨ link₀-β a₂ a₃ |in-ctx (λ u → link₀* a₁ a₂ ∙'ᵈ u) ⟩
        link₀* a₁ a₂ ∙'ᵈ link₀* a₂ a₃
          ∎

    postulate  -- HIT
      link₁-β : ∀ a₁ a₂ a₃
              → apd (apd f) (link₁ a₁ a₂ a₃)
             == lemma a₁ a₂ a₃ ◃ (link₁* a₁ a₂ a₃ ▹! link₀-β a₁ a₃)

open TwoConstancyElim public using () renaming (f to TwoConstancy-elim)

module TwoConstancyRec {l} {P : Type l}
  (p : has-level ⟨1⟩ P)
  (point* : ∀ a → P)
  (link₀* : ∀ a₁ a₂ → point* a₁ == point* a₂)
  (link₁* : ∀ a₁ a₂ a₃
            → link₀* a₁ a₂ ∙' link₀* a₂ a₃
           == link₀* a₁ a₃) where

  private
    module M = TwoConstancyElim {l = l} {P = λ _ → P}
      (λ _ → p)
      point*
      (λ a₁ a₂ → ↓-cst-in (link₀* a₁ a₂))
      (λ a₁ a₂ a₃
        → ↓-cst-in-∙' (link₀ a₁ a₂) (link₀ a₂ a₃) (link₀* a₁ a₂) (link₀* a₂ a₃)
       !◃ ↓-cst-in2 (link₁* a₁ a₂ a₃))

  f : TwoConstancy → P
  f = M.f

  link₀-β : ∀ a₁ a₂ → ap f (link₀ a₁ a₂) == link₀* a₁ a₂
  link₀-β a₁ a₂ = apd=cst-in {f = f} $ M.link₀-β a₁ a₂

  private
    lemma : ∀ a₁ a₂ a₃
          → ap f (link₀ a₁ a₂ ∙' link₀ a₂ a₃)
         == link₀* a₁ a₂ ∙' link₀* a₂ a₃
    lemma a₁ a₂ a₃ =
      ap f (link₀ a₁ a₂ ∙' link₀ a₂ a₃)
        =⟨ ap-∙' f (link₀ a₁ a₂) (link₀ a₂ a₃) ⟩
      ap f (link₀ a₁ a₂) ∙' ap f (link₀ a₂ a₃)
        =⟨ link₀-β a₁ a₂ |in-ctx (λ u → u ∙' ap f (link₀ a₂ a₃)) ⟩
      link₀* a₁ a₂ ∙' ap f (link₀ a₂ a₃)
        =⟨ link₀-β a₂ a₃ |in-ctx (λ u → link₀* a₁ a₂ ∙' u) ⟩
      link₀* a₁ a₂ ∙' link₀* a₂ a₃
        ∎

  -- I am a lazy person.
  postulate  -- HIT
    link₁-β : ∀ a₁ a₂ a₃
            → ap (ap f) (link₁ a₁ a₂ a₃)
           == (lemma a₁ a₂ a₃ ∙ link₁* a₁ a₂ a₃) ∙ (! $ link₀-β a₁ a₃)