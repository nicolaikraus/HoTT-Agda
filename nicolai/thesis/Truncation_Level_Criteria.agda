{-# OPTIONS --without-K #-}
module Truncation_Level_Criteria where

open import lib.Basics hiding (_⊔_)
open import lib.NType2

open import lib.types.Nat hiding (_+_)
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Unit
open import lib.types.Empty
open import lib.types.TLevel

open import Preliminaries
open import Pointed

-- Chapter 3: Truncation Level Criteria

-- Chapter 3.1: Hedberg's Theorem Revisited


-- Proposition 3.1.1 is below.

-- Definition 3.1.2
const : ∀{i j} {X : Type i} {Y : Type j} → (f : X → Y) → Type (i ⊔ j)
const {X = X} f = (x₁ x₂ : X) → (f x₁) == (f x₂)

coll : ∀{i} → Type i → Type i
coll X = Σ (X → X) const

pathColl : ∀ {i} → Type i → Type i
pathColl X = (x₁ x₂ : X) → coll (x₁ == x₂)

-- Lemma 3.1.3
discr→pathColl : ∀ {i} {X : Type i} → has-dec-eq X → pathColl X
discr→pathColl dec x₁ x₂ with (dec x₁ x₂) 
discr→pathColl dec x₁ x₂ | inl p  = (λ _ → p) , (λ _ _ → idp)
discr→pathColl dec x₁ x₂ | inr np = idf _ , λ p → Empty-elim (np p)

-- Lemma 3.1.4
pathColl→isSet : ∀ {i} {X : Type i} → pathColl X → is-set X
pathColl→isSet {X = X} pc x₁ x₂ = all-paths-is-prop paths-equal where
  claim : (y₁ y₂ : X) → (p : y₁ == y₂) → p == ! (fst (pc _ _) idp) ∙ fst (pc _ _) p 
  claim x₁ .x₁ idp = ! (!-inv-l (fst (pc x₁ x₁) idp))
  paths-equal : (p₁ p₂ : x₁ == x₂) → p₁ == p₂
  paths-equal p₁ p₂ = 
    p₁                                      =⟨ claim _ _ p₁ ⟩
    ! (fst (pc _ _) idp) ∙ fst (pc _ _) p₁  =⟨ ap (λ q → (! (fst (pc x₁ x₁) idp)) ∙ q) (snd (pc _ _) p₁ p₂) ⟩ -- whiskering
    ! (fst (pc _ _) idp) ∙ fst (pc _ _) p₂  =⟨ ! (claim _ _ p₂) ⟩
    p₂                                      ∎  

-- Proposition 3.1.1
hedberg : ∀ {i} {X : Type i} → has-dec-eq X → is-set X
hedberg = pathColl→isSet ∘ discr→pathColl 

-- Definition 3.1.5
stable : ∀ {i} → Type i → Type i
stable X = ¬ (¬ X) → X

separated : ∀ {i} → Type i → Type i
separated X = (x₁ x₂ : X) → stable (x₁ == x₂)

-- Proposition 3.1.6
sep→set : ∀ {i} {X : Type i} → (separated X) → is-set X
sep→set {X = X} sep = pathColl→isSet isPc where
  isPc : pathColl X  
  isPc x₁ x₂ = f , c where 
    f : x₁ == x₂ → x₁ == x₂
    f = (sep x₁ x₂) ∘ (λ p np → np p)
    c : const f 
    c p₁ p₂ = 
      f p₁                        =⟨ idp ⟩
      (sep x₁ x₂) (λ np → np p₁)  =⟨ ap (sep x₁ x₂) 
                                     (λ= λ np → Empty-elim {P = λ _ → np p₁ == np p₂} (np p₁)) ⟩
      (sep x₁ x₂) (λ np → np p₂)  =⟨ idp ⟩
      f p₂                        ∎ 

-- Lemma 3.1.7
-- first: definition of 'reflexive propositional relation that implies identity'
rel-ref-id : ∀ {i} → Type i → Type (lsucc i)
rel-ref-id {i} X = Σ (X → X → Type i)
                     λ R → 
                           ((x : X) → R x x)
                         × ((x₁ x₂ : X) → (R x₁ x₂) → x₁ == x₂)
                         × ((x₁ x₂ : X) → is-prop (R x₁ x₂))

-- the actual Lemma 3.1.7
module lem317 {i : _} (X : Type i) (Rrip : rel-ref-id X) where

  R : X → X → Type i
  R = fst Rrip
  ref : (x : X) → R x x
  ref = fst (snd (Rrip)) -- fst (fst (snd Rrip))
  ii : (x₁ x₂ : X) → (R x₁ x₂) → x₁ == x₂
  ii = fst (snd (snd (Rrip))) -- snd (fst (snd Rrip))
  pr : (x₁ x₂ : X) → is-prop (R x₁ x₂)
  pr = snd (snd (snd Rrip))

  f : (x₁ x₂ : X) → x₁ == x₂ → R x₁ x₂
  f x₁ .x₁ idp = ref x₁

  id↔R : (x₁ x₂ : X) → (x₁ == x₂) ↔ R x₁ x₂
  id↔R x₁ x₂ = f _ _ , ii _ _

  pc : pathColl X
  pc x₁ x₂ = ii _ _ ∘ f _ _ , λ p₁ p₂ → ap (ii x₁ x₂) (prop-has-all-paths (pr x₁ x₂) _ _)

  isSet : is-set X
  isSet = pathColl→isSet pc


open wtrunc

-- Definition 3.1.9
splitSup : ∀ {i} → (X : Type i) → Type i
splitSup X = ∣∣ X ∣∣ → X

hSeparated : ∀ {i} → (X : Type i) → Type i
hSeparated X = (x₁ x₂ : X) → splitSup (x₁ == x₂)

-- Proposition 3.1.10
-- we show "2->1", "1->3", "3->2" as in the thesis.
-- for the last part, we show "1->4" and "4->3
set-characterisations : ∀ {i} → (X : Type i) → 
      (pathColl X → is-set X)
    × (is-set X → rel-ref-id X)
    × (rel-ref-id X → pathColl X)
    × (is-set X → hSeparated X)
    × (hSeparated X → rel-ref-id X)
set-characterisations X = 
  pathColl→isSet , 
  (λ ss → _==_ , (λ _ → idp) , (λ _ _ p → p) , ss) ,
  (lem317.pc X) ,
  (λ ss x₁ x₂ → tr-rec (ss x₁ x₂) (λ p → p)) ,
  (λ hsep → ((λ x₁ x₂ → ∣∣ x₁ == x₂ ∣∣) , (λ _ → ∣ idp ∣) , hsep , λ _ _ → tr-is-prop))

-- The rest of this section is only a replication of the arguments that we have given so far (for that reason, the proofs are not given in the article).
-- They do not directly follow from the propositions that we have proved before, but they directly imply them.
-- Of course, replication of arguments is not a good style for a formalization -
-- we chose this "disadvantageous" order purely as we believe it led to a better presentation in the article.

-- Lemma 3.1.11
pathColl→isSet-local : ∀ {i} {X : Type i} → {x₀ : X} → ((y : X) → coll (x₀ == y)) → (y : X) → is-prop (x₀ == y)
pathColl→isSet-local {X = X} {x₀} pc y = all-paths-is-prop paths-equal  where
  claim : (y : X) → (p : x₀ == y) → p == ! (fst (pc _) idp) ∙ fst (pc _) p 
  claim .x₀ idp = ! (!-inv-l (fst (pc _) idp))
  paths-equal : (p₁ p₂ : x₀ == y) → p₁ == p₂
  paths-equal p₁ p₂ = 
    p₁                                  =⟨ claim _ p₁ ⟩
    ! (fst (pc _) idp) ∙ fst (pc _) p₁  =⟨ ap (λ q → (! (fst (pc x₀) idp)) ∙ q) (snd (pc y) p₁ p₂) ⟩ -- whiskering
    ! (fst (pc _) idp) ∙ fst (pc _) p₂  =⟨ ! (claim _ p₂) ⟩
    p₂                                  ∎  

-- Proposition 3.11.12
hedberg-local : ∀ {i} {X : Type i} → {x₀ : X} → ((y : X) → Coprod (x₀ == y) (¬(x₀ == y))) → (y : X) → is-prop (x₀ == y)
hedberg-local {X = X} {x₀ = x₀} dec = pathColl→isSet-local local-pathColl where
  local-pathColl : (y : X) → coll (x₀ == y)
  local-pathColl y with (dec y)
  local-pathColl y₁ | inl p  = (λ _ → p) , (λ _ _ → idp)
  local-pathColl y₁ | inr np = idf _ , (λ p → Empty-elim (np p))

-- Lemma 3.1.13. This needs function extensionality.
sep→set-local : ∀ {i} {X : Type i} {x₀ : X} → ((y : X) → stable (x₀ == y)) → (y : X) → is-prop (x₀ == y)
sep→set-local {X = X} {x₀ = x₀} sep = pathColl→isSet-local is-pathColl where
  is-pathColl : (y : X) → coll (x₀ == y)
  is-pathColl y = f , c where
    f : x₀ == y → x₀ == y
    f = (sep y) ∘ (λ p np → np p)
    c : const f 
    c p₁ p₂ = 
      f p₁                    =⟨ idp ⟩
      (sep _) (λ np → np p₁) =⟨ ap (sep y) 
                                    (λ= (λ np → prop-has-all-paths Empty-is-prop _ _)) ⟩
      (sep _) (λ np → np p₂) =⟨ idp ⟩
      f p₂ ∎ 



-- Chapter 3.2: Generalisations to Higher Levels

-- first: some lemmata.

-- If A -> B -> A is the identity, then
-- a₁ == a₂ → s a₁ == s a₂ → r(s a₁) == r(s a₂) 
-- is also the identity in an appropriate sense
retract-path-retract : ∀ {i j} {A : Type i} {B : Type j}
  → (s : A → B) → (r : B → A) → (s-r : (a : A) → r (s a) == a)
  → (a₁ a₂ : A)
  → (p : a₁ == a₂) → ! (s-r a₁) ∙ (ap r (ap s p)) ∙ (s-r a₂) == p
retract-path-retract s r s-r a₁ .a₁ idp = !-inv-l (s-r a₁)

-- retracts of n-types are n-truncated
retract-is-truncated : ∀ {n : ℕ₋₂} {i j} {A : Type i} {B : Type j} 
  → (has-level n B) → (s : A → B) → (r : B → A) → ((a : A) → r (s a) == a) → has-level n A
retract-is-truncated {⟨-2⟩} h s r s-r = inhab-prop-is-contr (r (fst h)) (all-paths-is-prop (λ a₁ a₂ →
                       a₁       =⟨ ! (s-r a₁) ⟩
                       r(s(a₁)) =⟨ ap r (contr-has-all-paths h _ _) ⟩ 
                       r(s(a₂)) =⟨ s-r a₂ ⟩ 
                       a₂ ∎  
                       ))
retract-is-truncated {S n} h s r s-r a₁ a₂ = 
  retract-is-truncated {n} {A = a₁ == a₂} {B = s a₁ == s a₂} 
                       (h (s a₁) (s a₂)) 
                       (ap s) 
                       (λ p → ! (s-r a₁) ∙ (ap r p) ∙ (s-r a₂)) 
                       (retract-path-retract s r s-r a₁ a₂)

-- this is essentially one direction of a local version of the lemma which says that
-- a type is n-truncated iff its loop spaces are (n-1)-truncated 
trunclevel-aux₁ : ∀ {i} {X : Type i} {x₀ : X} → (n : ℕ) → ((x : X) → has-level (n -2) (x₀ == x)) 
                   → is-contr (fst ((Ω ^ n) (X , x₀)))
trunclevel-aux₁ {x₀ = x₀} O h = x₀ , λ x → fst (h x)
trunclevel-aux₁ {X = X} {x₀ = x₀} (S n) h = trunclevel-aux₁ n (h x₀ idp)

-- the other direction...
trunclevel-aux₂ : ∀ {i} {X : Type i} {x₀ : X} → (n : ℕ) → is-contr (fst ((Ω ^ n) (X , x₀)))
                   → ((x : X) → has-level (n -2) (x₀ == x)) 
trunclevel-aux₂ {X = X} {x₀ = x₀} O h = λ x → inhab-prop-is-contr (contr-has-all-paths h x₀ x) (contr-is-prop (contr-is-prop h x₀ x))
trunclevel-aux₂ {X = X} {x₀ = x₀} (S n) h .x₀ idp = trunclevel-aux₂ n h


-- Theorem 3.2.1

-- in the thesis, we write "let n ≥ -1 be a number". 
-- As we do not want to introduce a type of number that are at least -1,
-- we use ℕ.
-- To make up for this, we reduce n everywhere by 1.
module GLHA {i : ULevel} {X : Type i} {x₀ : X} {n : ℕ} where

  Ω-contr : Type i
--  loop-contr = is-contr (fst ((Ω ^ (n + 1)) (X , x₀)))
  Ω-contr = is-contr (fst ((Ω ^ n) (X , x₀)))

  locally-truncated : Type i
--  locally-truncated = (x : X) → has-level (n -1) (x₀ == x)
  locally-truncated = (x : X) → has-level (n -2) (x₀ == x)

  tr-rel-id : Type (lsucc i)
  tr-rel-id = Σ (X → Type i) λ Q → 
--                ((x : X) → has-level (n -1) (Q x))
                ((x : X) → has-level (n -2) (Q x))
                × (Q x₀)
                × ((x : X) → Q x → x₀ == x)


  tr-rel-id→locally-truncated : tr-rel-id → locally-truncated
  tr-rel-id→locally-truncated (Q , h , q₀ , ii) = λ x → retract-is-truncated {n = n -2} {A = x₀ == x} {B = Q x} (h x) s r r-s where 

    r : {x : X} → (Q x) → (x₀ == x)
    r {x} q = ! (ii x₀ q₀) ∙ (ii x q)

    s : {x : X} → (x₀ == x) → Q x
    s idp = q₀

    r-s : {x : X} → (p : x₀ == x) → r (s p) == p
    r-s idp = !-inv-l (ii x₀ q₀)


  locally-truncated→Ω-contr : locally-truncated → Ω-contr
  locally-truncated→Ω-contr loctr = trunclevel-aux₁ n loctr -- trunclevel-aux n loctr

  Ω-contr→tr-rel-id : Ω-contr → tr-rel-id
  Ω-contr→tr-rel-id h = (λ x → x₀ == x) , (trunclevel-aux₂ n h) , idp , (λ x p → p)

  module with-higher-truncs where
    -- for convenience, we import truncations from the library.
    open import lib.types.Truncation

    -- fourth item in Theorem 3.2.1
    id-stable : Type i
    id-stable = (x : X) → Trunc (n -2) (x₀ == x) → x₀ == x

    -- it is very easy to see that (4) and (2) are logically equivalent.
    -- 2 ⇒ 4
    tr-rel-id→id-stable : tr-rel-id → id-stable
    tr-rel-id→id-stable (Q , h , q₀ , ii) = λ x → (ii x) ∘ (Trunc-rec (h x) (λ p → transport _ p q₀)) 

    -- 4 ⇒ 2
    id-stable→tr-rel-id : id-stable → tr-rel-id
    id-stable→tr-rel-id idst = (λ x → Trunc (n -2) (x₀ == x)) , (λ _ → Trunc-level) , [ idp ] , idst


