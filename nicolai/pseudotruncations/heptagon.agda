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


open import nicolai.pseudotruncations.wconst-preparation

module nicolai.pseudotruncations.heptagon
  {i} {C : Sequence {i}} (wc : wconst-chain C) (a₀ : fst C O) where

  {- î-def is defined in this module: -}
  open wconst-init {i} {C} wc a₀
  
  module _ (n : ℕ) (a : A n) where

    {- Let us formulate different simplification steps of the 
       heptagon. -}

    full-hepta : seq-loop (ins (S n) (f n a)) 
    full-hepta = (î-def (S n) (f n a)) ⋯ (‼ (î-def n a) ⋯ toSeq (glue n a))

    remove-g : seq-loop (ins (S n) (f n a)) 
    remove-g = (î-def (S n) (f n a))
               ⋯ ‼ (ins (S n) (f n a)
                      =⟪ ap (ins (S n)) (wc n _ _) ⟫
                    ins (S n) (lift-point C a₀ (S n)) 
                      =⟪ ! (lift-point-= C a₀ (S n)) ⟫
                    ins O a₀
                      ∎∎)

    simplify-‼ : seq-loop (ins (S n) (f n a)) 
    simplify-‼ = (î-def (S n) (f n a))
               ⋯ (ins O a₀
                    =⟪ lift-point-= C a₀ (S n) ⟫
                  ins (S n) (lift-point C a₀ (S n)) 
                    =⟪ ! (ap (ins (S n)) (wc n _ _)) ⟫
                  ins (S n) (f n a)
                    ∎∎)

    simplify-one-g : seq-loop (ins {C = C} (S n) (f n a))
    simplify-one-g =
                  ins (S n) (f n a)
                    =⟪ glue (S n) (f n a) ⟫
                  ins (S (S n)) (f (S n) (f n a))
                    =⟪ ap (ins (S (S n))) (wc (S n) (f n a) (lift-point C a₀ (S n))) ⟫
                  ins (S (S n)) (lift-point C a₀ (S (S n)))
                    =⟪ ! (glue (S n) (lift-point C a₀ (S n))) ⟫
                  ins (S n) (lift-point C a₀ (S n))
                    =⟪ ! (lift-point-= C a₀ (S n)) ⟫
                  ins O a₀
                    =⟪ lift-point-= C a₀ (S n) ⟫
                  ins (S n) (lift-point C a₀ (S n))
                    =⟪ ! (ap (ins (S n)) (wc n a (lift-point C a₀ n))) ⟫
                  ins (S n) (f n a)
                    ∎∎

    simplify-many-g : seq-loop (ins {C = C} (S n) (f n a))
    simplify-many-g =
                  ins (S n) (f n a)
                    =⟪ glue (S n) (f n a) ⟫
                  ins (S (S n)) (f (S n) (f n a))
                    =⟪ ap (ins (S (S n))) (wc (S n) (f n a) (lift-point C a₀ (S n))) ⟫
                  ins (S (S n)) (lift-point C a₀ (S (S n)))
                    =⟪ ! (glue (S n) (lift-point C a₀ (S n))) ⟫
                  ins (S n) (lift-point C a₀ (S n))
                    =⟪ ! (ap (ins (S n)) (wc n a (lift-point C a₀ n))) ⟫
                  ins (S n) (f n a)
                    ∎∎

    replace-ap-SSn : seq-loop (ins {C = C} (S n) (f n a))
    replace-ap-SSn =
                  ins (S n) (f n a)
                    =⟪ glue (S n) (f n a) ⟫
                  ins (S (S n)) (f (S n) (f n a))
                    =⟪ ap (ins (S (S n))) (ap (f (S n)) (wc n a (lift-point C a₀ n))) ⟫
                  ins (S (S n)) (lift-point C a₀ (S (S n)))
                    =⟪ ! (glue (S n) (lift-point C a₀ (S n))) ⟫
                  ins (S n) (lift-point C a₀ (S n))
                    =⟪ ! (ap (ins (S n)) (wc n a (lift-point C a₀ n))) ⟫
                  ins (S n) (f n a)
                    ∎∎

    {-
      Now, let us generalize:
        x   for   f n a 
        y   for   lift-point C a₀ (S n) 
        q   for   wc n a (lift C a₀ n)
      Then, we can show that the square commutes by induction on q.
    -}
    generalize-square : (x y : A (S n)) (q : x == y)
              → (↯ 
                  ins {C = C} (S n) x
                    =⟪ glue (S n) x ⟫
                  ins (S (S n)) (f (S n) x)
                    =⟪ ap (ins (S (S n))) (ap (f (S n)) q) ⟫
                  ins (S (S n)) (f (S n) y)
                    =⟪ ! (glue (S n) y) ⟫
                  ins (S n) y
                    =⟪ ! (ap (ins (S n)) q) ⟫
                  ins (S n) x
                    ∎∎
               ) == idp
    generalize-square x .x idp = 
                  glue (S n) x ∙ ! (glue (S n) x) ∙ idp
                    =⟨ ap (λ q → (glue (S n) x) ∙ q) (∙-unit-r _) ⟩
                  glue (S n) x ∙ ! (glue (S n) x)
                    =⟨ !-inv-r (glue (S n) x) ⟩
                  idp
                    ∎ 

    {- Let us use some ad-hoc lemmas; these could all be done via
       very tedious concatenations of library lemmas.
       Of course, our ad-hoc way is somewhat ugly, but it saves a
       lot of work compared to using concatenations and nestings of
       library lemmas. The strategy is to formulate the equality 
       that we need and solve it by trivial path induction.

       This ad-hoc approach is surely not the best way one can 
       think of. 
       The best way to do it would probably be a more principled 
       approach with more powerful high-level lemmas that allow the
       manipulation of paths; however, such a technology is not
       implemented so far. -}
    adhoc-!-∙ : ∀ {i} {X : Type i} {x y z u v w o : X}
                         (p : x == y) (q : y == z) (r : u == z)
                         (s : v == u) (t : v == w) (l : w == o)
                         → (↯ x =⟪ p ⟫ y =⟪ q ⟫ z =⟪ ! (s ∙ r) ⟫ v =⟪ t ⟫ w =⟪ l ⟫ o ∎∎ )
                           ==
                           (↯ x =⟪ p ⟫ y =⟪ q ⟫ z =⟪ ! r ⟫ u =⟪ ! s ⟫ v =⟪ t ⟫ w =⟪ l ⟫ o ∎∎)
    adhoc-!-∙ idp idp idp idp idp idp = idp


    adhoc-cancel-inv : ∀ {i} {X : Type i} {x y z u v w : X}
                         (p : x == y) (q : y == z) (r : z == u)
                         (s : v == u) (t : u == w)
                         → (↯ x =⟪ p ⟫ y =⟪ q ⟫ z =⟪ r ⟫ u =⟪ ! s ⟫ v =⟪ s ⟫ u =⟪ t ⟫ w ∎∎ )
                           ==
                           (↯ x =⟪ p ⟫ y =⟪ q ⟫ z =⟪ r ⟫ u =⟪ t ⟫ w ∎∎)
    adhoc-cancel-inv idp idp idp idp idp = idp


    {- Now, we are ready to show that the heptagon is trivial! -}
    ĝ-def :  (↯ full-hepta) == idp
    ĝ-def = 

      (↯ full-hepta)

        =⟨ ap (λ q → (glue (S n) (f n a))
                   ∙ ap (ins (S (S n))) (wc (S n) (f n a) (snd C n (lift-point C a₀ n)))
                   ∙ ! ((lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n))
                        ∙ glue (S n) (snd C n (lift-point C a₀ n)))
                   ∙ ! (! (lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n)))
                   ∙ ! (ap (ins (S n)) (wc n a (lift-point C a₀ n)))
                   ∙ q )
              (!-inv-l (glue n a)) ⟩

      (↯ (remove-g ⋯ (toSeq idp)))

        =⟨ ap (λ q → (glue (S n) (f n a))
                    ∙ ap (ins (S (S n))) (wc (S n) (f n a) (snd C n (lift-point C a₀ n)))
                    ∙ ! ((lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n))
                    ∙ glue (S n) (snd C n (lift-point C a₀ n)))
                    ∙ ! (! (lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n)))
                    ∙ q )
              (∙-unit-r (! (ap (ins (S n)) (wc n a (lift-point C a₀ n))))) ⟩
      (↯ remove-g)

        =⟨ ap (λ q → (glue (S n) (f n a))
                    ∙ ap (ins (S (S n))) (wc (S n) (f n a) (snd C n (lift-point C a₀ n)))
                    ∙ ! ((lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n))
                    ∙ glue (S n) (snd C n (lift-point C a₀ n)))
                    ∙ q
                    ∙ ! (ap (ins (S n)) (wc n a (lift-point C a₀ n)))
               )
               (!-! (lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n))) ⟩

      (↯ simplify-‼) 

        =⟨ adhoc-!-∙
              (glue (S n) (f n a))
              (ap (ins (S (S n))) (wc (S n) (f n a) (snd C n (lift-point C a₀ n))))
              (glue (S n) (snd C n (lift-point C a₀ n)))
              (lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n))
              (lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n))
              (! (ap (ins (S n)) (wc n a (lift-point C a₀ n)))) ⟩
      (↯ simplify-one-g) 
        =⟨ adhoc-cancel-inv
             (glue (S n) (f n a))
             (ap (ins (S (S n))) (wc (S n) (f n a) (snd C n (lift-point C a₀ n))))
             (! (glue (S n) (snd C n (lift-point C a₀ n))))
             (lift-point-= C a₀ n ∙ glue n (lift-point C a₀ n))
             (! (ap (ins (S n)) (wc n a (lift-point C a₀ n)))) ⟩

      (↯ simplify-many-g) 

        =⟨ ap (λ q → (glue (S n) (f n a))
                    ∙ q
                    ∙ ! (glue (S n) (snd C n (lift-point C a₀ n)))
                    ∙ ! (ap (ins (S n)) (wc n a (lift-point C a₀ n)))
               )
               (ap-wconst (ins (S (S n)))
                          (ins-wconst (S (S n)))
                          (wc (S n) (f n a) (snd C n (lift-point C a₀ n)))
                          (ap (f (S n)) (wc n a (lift-point C a₀ n)))
               ) ⟩

      (↯ replace-ap-SSn) 

        =⟨ generalize-square (f n a) (lift-point C a₀ (S n)) (wc n a (lift-point C a₀ n)) ⟩

      idp
        ∎ 

