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
-- open import lib.PathGroupoid

-- open import nicolai.pseudotruncations.PathSeqAlt
open import lib.types.PathSeq

open import nicolai.pseudotruncations.Liblemmas
open import nicolai.pseudotruncations.SeqColim

open import nicolai.pseudotruncations.wconstSequence

module nicolai.pseudotruncations.heptagon {i} {C : Sequence {i}} (wc : wconst-chain C) (a₀ : fst C O) where

  open wconst-init {i} {C} wc a₀
  
{- Recall that î is defined like this:

  î : (n : ℕ) → (a : A n) → (ins {C = C} n a) =-= (ins O a₀)
  î n a = 
    ins n a
      =⟪ glue n a ⟫
    ins (S n) (f n a)
      =⟪ ap (ins (S n)) (wc n _ _) ⟫
    ins (S n) (lift-point C a₀ (S n))
      =⟪ ! (lift-point-= C a₀ (S n)) ⟫
    ins O a₀
      ∎∎ 
-}

  module _ (n : ℕ) (a : A n) where

    full-hepta : loop (ins (S n) (f n a)) 
    full-hepta = (î (S n) (f n a)) ⋯ (‼ (î n a) ⋯ toSeq (glue n a))

    remove-g : loop (ins (S n) (f n a)) 
    remove-g = (î (S n) (f n a))
               ⋯ ‼ (ins (S n) (f n a)
                      =⟪ ap (ins (S n)) (wc n _ _) ⟫
                    ins (S n) (lift-point C a₀ (S n)) 
                      =⟪ ! (lift-point-= C a₀ (S n)) ⟫
                    ins O a₀
                      ∎∎)

    simplify-‼ : loop (ins (S n) (f n a)) 
    simplify-‼ = (î (S n) (f n a))
               ⋯ (ins O a₀
                    =⟪ lift-point-= C a₀ (S n) ⟫
                  ins (S n) (lift-point C a₀ (S n)) 
                    =⟪ ! (ap (ins (S n)) (wc n _ _)) ⟫
                  ins (S n) (f n a)
                    ∎∎)

   

    simplify-many-g : loop (ins {C = C} (S n) (f n a))
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


    replace-ap-SSn : loop (ins {C = C} (S n) (f n a))
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


    ĝ-aux :  (↯ full-hepta) == idp
    ĝ-aux = 
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
        =⟨ {!↯ (remove-g ⋯ (toSeq idp))!} ⟩
      (↯ simplify-many-g) 
        =⟨ {!↯ (remove-g ⋯ (toSeq idp))!} ⟩
      (↯ replace-ap-SSn) 
        =⟨ generalize-square (f n a) (lift-point C a₀ (S n)) (wc n a (lift-point C a₀ n)) ⟩
      idp
        ∎ 

