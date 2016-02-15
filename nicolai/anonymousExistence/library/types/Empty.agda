{-# OPTIONS --without-K #-}

open import library.Basics

module library.types.Empty where

⊥ = Empty

⊥-elim : ∀ {i} {A : ⊥ → Type i} → ((x : ⊥) → A x)
⊥-elim = Empty-elim

Empty-rec : ∀ {i} {A : Type i} → (Empty → A)
Empty-rec = Empty-elim

⊥-rec : ∀ {i} {A : Type i} → (⊥ → A)
⊥-rec = Empty-rec

Empty-is-prop : is-prop Empty
Empty-is-prop = Empty-elim

⊥-is-prop : is-prop ⊥
⊥-is-prop = Empty-is-prop
