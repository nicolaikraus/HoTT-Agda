{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Nat
open import lib.types.Sigma

module nicolai.pseudotruncations.PathSeqAlt where

{-
This is a modified version of the library file on reified equational reasoning;
see here:

  lib/types/PathSeq

Reified equational reasoning was implemented by Guillaume.
The idea is that we construct sequences of paths, rather than just concatenating
everythings immediately (which is what happens when we use equational reasoning).

The reason why I define an alternative version is that the original one
is too clever for me in one aspect: it tries to delete 'idp' instead of 
including it when using [↯]. The [↯] function turns a sequence into a path. 
This behavious is very nice (see the examples in the original file).
However, this seems to make certain things difficult that I want to do; 
for example, I want that [↯] is "natural" (i.e. concatenation sequences, then
↯ gives the same as ↯ for each sequence, then concatenating the paths).

It's possible that this can be done in a very elegant way and I just don't 
see it (I will be grateful for hints!).
-}

infix  15 _∎∎
infixr 10 _=⟪_⟫_
infixr 10 _=⟪idp⟫_


data PathSeq {i} {A : Type i} : A → A → Type i where
  _∎∎ : (a : A) → PathSeq a a
  _=⟪_⟫_ : (a : A) {a' a'' : A} (p : a == a') (s : PathSeq a' a'') → PathSeq a a''

infix 30 _=-=_
_=-=_ = PathSeq

_=⟪idp⟫_ : ∀ {i} {A : Type i} (a : A) {a' : A} (s : PathSeq a a') → PathSeq a a'
a =⟪idp⟫ s = s


-- "Embedding": get a sequence out of a path
toSeq : ∀ {i} {A : Type i} {a₁ a₂ : A} → a₁ == a₂ → a₁ =-= a₂
toSeq p = _ =⟪ p ⟫ _ ∎∎ 

module _ {i} {A : Type i} where

  infix 0 ↯_
  infixr 5 _⋯_ 


  ↯_ : {a a' : A} (s : PathSeq a a') → a == a'
  ↯ a ∎∎ = idp
  ↯ a =⟪ p ⟫ s = p ∙ (↯ s)

  -- Concatenation of sequences
  _⋯_ : {a a' a'' : A} (s : a =-= a') (s' : a' =-= a'') → a =-= a''
  (a ∎∎) ⋯ s' = s'
  (a =⟪ p ⟫ s) ⋯ s' = a =⟪ p ⟫ (s ⋯ s')


-- Concatenation of sequences commutes with concatenation of paths
  ∙-⋯-↯ : {a a' a'' : A} (s : a =-= a') (s' : a' =-= a'')
             → (↯ (s ⋯ s')) == (↯ s) ∙ (↯ s')
  ∙-⋯-↯ (a ∎∎) s' = idp
  ∙-⋯-↯ (a =⟪ p ⟫ s) s' =
    (↯ a =⟪ p ⟫ s ⋯ s')
      =⟨ ap (λ q → p ∙ q) (∙-⋯-↯ s s') ⟩
    p ∙ (↯ s) ∙ (↯ s')
      =⟨ ! (∙-assoc p _ _) ⟩ 
    (p ∙ (↯ s)) ∙ (↯ s')
      =⟨ idp ⟩ 
    (↯ a =⟪ p ⟫ s) ∙ (↯ s')
      ∎ 

  ‼ : {a a' : A} → a =-= a' → a' =-= a
  ‼ (a ∎∎) = a ∎∎
  ‼ (a =⟪ p ⟫ s) = (‼ s) ⋯ (_ =⟪ ! p ⟫ _ ∎∎ )

{-
  ‼-⋯-↯ : {a a' a'' : A} (s : a =-= a') (s' : a' =-= a'')
        → ↯ (‼ (s ⋯ s')) == 
-}

  !-‼-↯ : {a a' : A} (s : a =-= a') → (↯ (‼ s)) == ! (↯ s)
  !-‼-↯ (a ∎∎) = idp
  !-‼-↯ (a =⟪ p ⟫ s) = 
    (↯ (‼ (a =⟪ p ⟫ s)))
      =⟨ idp ⟩ 
    (↯ ‼ s ⋯ (_ =⟪ ! p ⟫ _ ∎∎))
      =⟨ ∙-⋯-↯ (‼ s) _ ⟩
    (↯ ‼ s) ∙ (↯ (toSeq (! p)))
      =⟨ ap (λ q → (↯ ‼ s) ∙ q) (∙-unit-r _) ⟩
    (↯ ‼ s) ∙ (! p)
      =⟨ ap (λ q → q ∙ (! p)) (!-‼-↯ s) ⟩
    ! (↯ s) ∙ (! p)
      =⟨ ! (!-∙ p (↯ s)) ⟩ 
    ! (p ∙ (↯ s))
      ∎ 











  private
    point-from-start : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
    point-from-start O {a} s = a
    point-from-start (S n) (a ∎∎) = a
    point-from-start (S n) (a =⟪ p ⟫ s) = point-from-start n s

  _-! : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq (point-from-start n s) a'
  (O -!) s = s
  (S n -!) (a ∎∎) = a ∎∎
  (S n -!) (a =⟪ p ⟫ s) = (n -!) s

  private
    last1 : {a a' : A} (s : PathSeq a a') → A
    last1 (a ∎∎) = a
    last1 (a =⟪ p ⟫ a' ∎∎) = a
    last1 (a =⟪ p ⟫ s) = last1 s

    strip : {a a' : A} (s : PathSeq a a') → PathSeq a (last1 s)
    strip (a ∎∎) = a ∎∎
    strip (a =⟪ p ⟫ a' ∎∎) = a ∎∎
    strip (a =⟪ p ⟫ a' =⟪ p' ⟫ s) = a =⟪ p ⟫ strip (a' =⟪ p' ⟫ s)

    point-from-end : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
    point-from-end O {a} {a'} s = a'
    point-from-end (S n) s = point-from-end n (strip s)

  !- : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq a (point-from-end n s)
  !- O s = s
  !- (S n) s = !- n (strip s)

  _-# : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq a (point-from-start n s)
  (O -#) s = _ ∎∎
  (S n -#) (a ∎∎) = a ∎∎
  (S n -#) (a =⟪ p ⟫ s) = a =⟪ p ⟫ (n -#) s

  private
    split : {a a' : A} (s : PathSeq a a')
      → Σ A (λ a'' → (PathSeq a a'') × (a'' == a'))
    split (a ∎∎) = (a , ((a ∎∎) , idp))
    split (a =⟪ p ⟫ a' ∎∎) = (a , ((a ∎∎) , p))
    split (a =⟪ p ⟫ s) = let (a'' , (t , q)) = split s in (a'' , ((a =⟪ p ⟫ t) , q))

    infix 80 _∙∙_
    _∙∙_ : {a a' a'' : A} (s : PathSeq a a') (p : a' == a'') → PathSeq a a''
    (a ∎∎) ∙∙ p = a =⟪ p ⟫ _ ∎∎
    (a =⟪ p ⟫ s) ∙∙ p' = a =⟪ p ⟫ s ∙∙ p'

    point-from-end' : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
    point-from-end' n (a ∎∎) = a
    point-from-end' O (a =⟪ p ⟫ s) = point-from-end' O s
    point-from-end' (S n) (a =⟪ p ⟫ s) = point-from-end' n (fst (snd (split (a =⟪ p ⟫ s))))

  #- : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq (point-from-end' n s) a'
  #- n (a ∎∎) = a ∎∎
  #- O (a =⟪ p ⟫ s) = #- O s
  #- (S n) (a =⟪ p ⟫ s) = let (a' , (t , q)) = split (a =⟪ p ⟫ s) in #- n t ∙∙ q

  infix 120 _!0 _!1 _!2 _!3 _!4 _!5
  _!0 = !- 0
  _!1 = !- 1
  _!2 = !- 2
  _!3 = !- 3
  _!4 = !- 4
  _!5 = !- 5

  0! = 0 -!
  1! = 1 -!
  2! = 2 -!
  3! = 3 -!
  4! = 4 -!
  5! = 5 -!

  infix 120 _#0 _#1 _#2 _#3 _#4 _#5
  _#0 = #- 0
  _#1 = #- 1
  _#2 = #- 2
  _#3 = #- 3
  _#4 = #- 4
  _#5 = #- 5

  0# = 0 -#
  1# = 1 -#
  2# = 2 -#
  3# = 3 -#
  4# = 4 -#
  5# = 5 -#

  private
    postulate   -- Demo
      a b c d e : A
      p : a == b
      q : b == c
      r : c == d
      s : d == e

    t : PathSeq a e
    t =
      a =⟪ p ⟫
      b =⟪idp⟫
      b =⟪ q ⟫
      c =⟪ idp ⟫
      c =⟪ r ⟫
      d =⟪ s ⟫
      e =⟪idp⟫
      e ∎∎

    t' : a == e
    t' = ↯
      a =⟪ p ⟫
      b =⟪ q ⟫
      c =⟪ idp ⟫
      c =⟪ r ⟫
      d =⟪ s ⟫
      e ∎∎

    ex0 : t' == (↯ t)
    ex0 = idp






apd= : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
       (p : (x : A) → f x == g x) {a b : A} (q : a == b)
       → apd f q ▹ p b == p a ◃ apd g q
apd= {B = B} p {b} idp = idp▹ {B = B} (p b) ∙ ! (◃idp {B = B} (p b))

apd=-red : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
           (p : (x : A) → f x == g x) {a b : A} (q : a == b)
           {u : B b} (s : g b =-= u)
           → apd f q ▹ (↯ _ =⟪ p b ⟫ s) == p a ◃ (apd g q ▹ (↯ s))
apd=-red {B = B} p {b} idp s = coh (p b) s  where

  coh : ∀ {i} {A : Type i} {u v w : A} (p : u == v) (s : v =-= w)
    → (idp ∙' (↯ _ =⟪ p ⟫ s)) == p ∙ idp ∙' (↯ s)
  coh idp (a ∎∎) = idp
  coh idp (a =⟪ p₁ ⟫ s₁) = idp
