{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.PathGroupoid

open import lib.types.Bool
open import lib.types.IteratedSuspension
open import lib.types.Lift
open import lib.types.LoopSpace
open import lib.types.Nat
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.Suspension
open import lib.types.TLevel
open import lib.types.Unit

open SuspensionRec public using () renaming (f to Susp-rec)
open import nicolai.pseudotruncations.Liblemmas

module nicolai.pseudotruncations.LoopsAndSpheres where

{- We greatly benefit from Evan Cavallo's code - thank you! -}
open import homotopy.PtdAdjoint
open import homotopy.SuspAdjointLoop


{- Pointed maps (without the 'point') -}
_→̇_ : ∀ {i j} (Â : Ptd i) (B̂ : Ptd j) → Type _
Â →̇ B̂ = fst (Â ⊙→ B̂)


{- It is useful to have a lemma which allows to construct equalities
   between pointed types. Of course, we know that such an equality
   is a pair of equalities; however, transporting a function can 
   make things more tedious than necessary! -}
make-=-∙ : ∀ {i j} {Â : Ptd i} {B̂ : Ptd j} (f̂ ĝ : Â →̇ B̂)
           (p : fst f̂ == fst ĝ)
           → ! (app= p (snd Â)) ∙ snd f̂ == snd ĝ
           → f̂ == ĝ
make-=-∙ (f , p) (.f , q) idp t = pair= idp t


isNull : ∀ {i j} {A : Type i} {B : Type j} (b : B) (f : A → B) → Type _
isNull {A = A} b f = (a : A) → f a == b


module null {i} {j} {Â : Ptd i} {B̂ : Ptd j} (ĝ : Â →̇ B̂) where

  A = fst Â
  a₀ = snd Â 
  B = fst B̂
  b₀ = snd B̂
  g = fst ĝ
  p = snd ĝ 

  -- derived isNull
  isNulld = (a : fst Â) → g a == b₀ 

  -- pointed isNull; we state it in the equivalence form (slightly easier to handle)
  isNull∙' = Σ ((a : A) → g a == b₀) λ pr → pr a₀ == p

  -- the 'real' pointed isNull
  isNull∙ = ĝ == ((λ _ → b₀) , idp)

{- THIS NEEDS TO BE DONE LATER
  isNull-eq : isNull∙ ≃ isNull∙'
  isNull-eq = ĝ == ((λ _ → b₀) , idp)
                 ≃⟨ {!=Σ-eqv!}⁻¹ ⟩
               =Σ ĝ ((λ _ → b₀) , idp)
                 ≃⟨ coe-equiv (Σ= {!λ=!} {!!}) ⟩
               (Σ ((a : A) → g a == b₀) λ pr → pr a₀ == p)
                 ≃∎ 
-}

-- Lemma 4.4: pointed and non-pointed 'nullness' are logically equivalent;
-- we only do one direction (the other one is trivial)
  null-lequiv : isNulld → isNull∙'
  null-lequiv isnull = (λ a → isnull a ∙ ! (isnull a₀) ∙ p) , (
                 isnull a₀ ∙ ! (isnull a₀) ∙ p
                   =⟨ ! (∙-assoc (isnull a₀) _ _) ⟩
                 (isnull a₀ ∙ ! (isnull a₀)) ∙ p
                   =⟨ ap (λ t → t ∙ p) (!-inv-r (isnull a₀)) ⟩
                 p
                   ∎)





-- uncomment this if you want to wait forever for typechecking...
-- Σ⊣Ω-unitCounit : CounitUnitAdjoint Σ⊣Ω.SuspFunctor Σ⊣Ω.LoopFunctor
Σ⊣Ω-unitCounit = Σ⊣Ω.adj

Σ⊣Ω-homset : ∀ {i} → HomAdjoint {i} {i} Σ⊣Ω.SuspFunctor Σ⊣Ω.LoopFunctor
Σ⊣Ω-homset = counit-unit-to-hom Σ⊣Ω-unitCounit




module hom-adjoint {i} (Â : Ptd i) (B̂ : Ptd i) where

  A = fst Â
  B = fst B̂
  a₀ = snd Â
  b₀ = snd B̂

  Φeq : (⊙Susp Â →̇ B̂) ≃ (Â →̇ ⊙Ω B̂)
  Φeq = HomAdjoint.eq Σ⊣Ω-homset Â B̂  

  Φ : (⊙Susp Â →̇ B̂) → (Â →̇ ⊙Ω B̂)
  Φ = –> Φeq  



  -- Lemma 4.2; this is actually too general, we only need the case that p is refl!
  Φ-pres-isNull : (p : b₀ == b₀) (a : A)
                  → (fst (Φ ((λ _ → b₀) , p)) a) == idp
  Φ-pres-isNull p a = 
    (fst (Φ ((λ _ → b₀) , p)) a)
      =⟨ idp ⟩
    ! p ∙ (ap (λ _ → b₀) _) ∙' p
      =⟨ ap (λ x → ! p ∙ x ∙' p) (ap-cst b₀ _) ⟩
    ! p ∙ idp ∙' p
      =⟨ ap (λ x → ! p ∙ x) (∙'-unit-l p) ⟩ 
    ! p ∙ p
      =⟨ !-inv-l p ⟩ 
    idp {a = b₀}
      ∎


  -- real Lemma 4.2
  Φ-is-pointed-map : Φ ((λ _ → b₀) , idp) == ((λ _ → idp) , idp)
  Φ-is-pointed-map = -- {!make-=-∙ !}
    pair= X Y where
      
        X = (λ= (λ a → fst (Φ ((λ _ → b₀) , idp)) a
                     =⟨ ap-cst b₀ _ ⟩
                   idp {a = b₀}
                     ∎))
        Y : {!Π-equiv-l!}
        Y = {!app= X a₀!} 





{-
  -- real Lemma 4.2
  Φ-is-pointed-map : Φ ((λ _ → b₀) , idp) == ((λ _ → idp) , idp)
  Φ-is-pointed-map = pair= (λ= (Φ-pres-isNull idp)) {!!} --  {!(λ= (Φ-pres-isNull idp)) , ? !}
-}

-- TODO is this true more generally? I.e. for any adjoint pair?
--  Φ-pres-isNull-equiv : (f : ⊙Susp Â →̇ B̂)



-- fix i
module _ {i} where

  open hom-adjoint

  open HomAdjoint
  open null

  -- Lemma 4.3
  Φ-snd-nat : {Â B̂ Ĉ : Ptd i} (f : ⊙Susp Â →̇ B̂) (g : B̂ →̇ Ĉ)
              → Φ Â Ĉ (g ⊙∘ f) == ⊙ap g ⊙∘ Φ Â B̂ f
  Φ-snd-nat {Â} {B̂} {Ĉ} f g = ! (nat-cod Σ⊣Ω-homset Â {B̂} {Ĉ} g f)

  -- Lemma 4.5
  isnull-Φ : {Â B̂ : Ptd i} (g : ⊙Susp Â →̇ B̂) → (isNull∙ g) ≃ isNull∙ (Φ Â B̂ g)
  isnull-Φ {Â} {B̂} g =
    isNull∙ g
      ≃⟨ equiv-ap (Φeq Â B̂) _ _ ⟩
    (Φ Â B̂ g) == Φ Â B̂ ((λ _ → snd B̂) , idp)
      ≃⟨ coe-equiv
           {A = (Φ Â B̂ g) == Φ Â B̂ ((λ _ → snd B̂) , idp)}
           {B = (Φ Â B̂ g) == (λ _ → idp) , idp}
           (ap (λ q → (Φ Â B̂ g == q)) (Φ-is-pointed-map _ _)) ⟩
    (Φ Â B̂ g) == (λ _ → idp) , idp
      ≃∎ 


  -- combination of 4.3 and 4.5
  combine-isnull-nat : {Â B̂ Ĉ : Ptd i} (f : ⊙Susp Â →̇ B̂) (g : B̂ →̇ Ĉ)
               → (isNull∙ (g ⊙∘ f)) ≃ (isNull∙ (⊙ap g ⊙∘ Φ Â B̂ f)) --   
  combine-isnull-nat {Â} {B̂} {Ĉ} f g = 
    isNull∙ (g ⊙∘ f)
      ≃⟨ isnull-Φ _ ⟩
    isNull∙ (Φ Â Ĉ (g ⊙∘ f))
      ≃⟨ coe-equiv (ap (λ q → isNull∙ q) (Φ-snd-nat f g)) ⟩
    isNull∙ (⊙ap g ⊙∘ Φ Â B̂ f)
      ≃∎ 


-- this is in the library, but very inconvenient unfortunately (todo: explain why)
module _ {i} where

  open hom-adjoint
  
  ⊙Susp-iter : (n : Nat) (Â : Ptd i) → Ptd i
  ⊙Susp-iter O Â = Â
  ⊙Susp-iter (S n) Â = ⊙Susp-iter n (⊙Susp Â)

{-
  ⊙Ω-iter : (n : Nat) (Â : Ptd i) → Ptd i
  ⊙Ω-iter O Â = Â
  ⊙Ω-iter (S n) Â = ⊙Ω (⊙Ω-iter n Â)
-}

  ⊙Sphere* : (n : Nat) → Ptd i
  ⊙Sphere* n = ⊙Susp-iter n (⊙Lift ⊙Bool) 

  -- This was tricky (todo: could explain why)
  Φ-iter : (Â B̂ : Ptd i) (n : Nat)
           → ((⊙Susp-iter n Â) →̇ B̂)
           → (Â →̇ (⊙Ω^ n B̂))
  Φ-iter Â B̂ O f = f
  Φ-iter Â B̂ (S n) f = Φ Â (⊙Ω^ n B̂) (Φ-iter (⊙Susp Â) B̂ n f)

  Φ-iter-equiv : (Â B̂ : Ptd i) (n : Nat) → is-equiv (Φ-iter Â B̂ n)
  Φ-iter-equiv Â B̂ O = snd (ide _)
  Φ-iter-equiv Â B̂ (S n) =
    snd ((Φeq Â (⊙Ω^ n B̂)) ∘e ((Φ-iter (⊙Susp Â) B̂ n) , Φ-iter-equiv (⊙Susp Â) B̂ n) )



module _ {i} where

  open null
  open hom-adjoint
  
  -- Lemma 4.7 -- generalized, because we need to do it for Susp first before it works for Sphere!
  isNull-Φ-many : (m : Nat)
                  → (Â B̂ Ĉ : Ptd i)
                  → (f : ⊙Susp-iter m Â →̇ B̂) (g : B̂ →̇ Ĉ)
                  → isNull∙ (g ⊙∘ f)
                    ≃
                    isNull∙ ((ap^ m g) ⊙∘ Φ-iter Â B̂ m f)
  isNull-Φ-many O Â B̂ Ĉ f g = ide _
  isNull-Φ-many (S m) Â B̂ Ĉ f g = 
                    isNull∙ (g ⊙∘ f)
                      ≃⟨ isNull-Φ-many m (⊙Susp Â) B̂ Ĉ f g   ⟩
                    isNull∙ ((ap^ m g) ⊙∘ Φ-iter (⊙Susp Â) B̂ m f)
                      ≃⟨ combine-isnull-nat (Φ-iter (⊙Susp Â) B̂ m f) (ap^ m g) ⟩
                    (isNull∙
                      (⊙ap (ap^ m g) ⊙∘
                        Φ Â (⊙Ω^ m B̂)
                          (Φ-iter (⊙Susp Â) B̂ m f)))
                      ≃∎

  -- Lemma 4.7 (special with k = 0)
  module _ {B̂ Ĉ : Ptd i} (m : Nat)
           (f : ⊙Sphere* {i} m →̇ B̂) (g : B̂ →̇ Ĉ) where

    isNull-Φ-Sphere : isNull∙ (g ⊙∘ f)
                      ≃
                      isNull∙ ((ap^ m g) ⊙∘ Φ-iter (⊙Sphere* {i} O) B̂ m f)
    isNull-Φ-Sphere = isNull-Φ-many m _ _ _ f g

  module triv-O-sphere {j} {D̂ : Ptd j} where

    D = fst D̂
    d₀ = snd D̂ 

    bool = fst (⊙Sphere {i} O)
    tt₀ : bool
    tt₀ = snd (⊙Sphere {i} O)
    ff₀ : bool
    ff₀ = lift false

    -- standard lemma
    from-bool : ∀ {j} (X : Type j) → X × X ≃ (bool → X) 
    from-bool X =
      equiv (λ x2 → λ { (lift true) → fst x2 ; (lift false) → snd x2 })
            (λ f → f tt₀ , f ff₀)
            (λ f → λ= (λ { (lift true) → idp ; (lift false) → idp }))
            (λ x2 → idp)

    -- a bit more interesting: pointed maps from bool
    from-bool∙ : (Σ (D × D) λ d2 → fst d2 == d₀) ≃ (⊙Sphere {i} O →̇ D̂)
    from-bool∙ = equiv-Σ-fst
                   {A = D × D}
                   {B = bool → D}
                   (λ f → f tt₀ == d₀)
                   {h = fst (from-bool D)}
                   (snd (from-bool D))


    -- but we also have (would maybe be much easier to prove with a library lemma?):
    Σ-sngltn : (Σ (D × D) λ d2 → fst d2 == d₀) ≃ D
    Σ-sngltn = equiv (λ dx → snd (fst dx))
                     (λ d → (d₀ , d) , idp)
                     (λ d → idp)
                     (λ {((d₁ , d) , p)
                         → pair= (pair×= (! p) idp)
                                 (from-transp (λ d2 → fst d2 == d₀)
                                 (pair×= (! p) idp)
                                 ((transport (λ d2 → fst d2 == d₀) (pair×= (! p) idp) idp)
                                    =⟨ trans-ap₁ fst d₀ (pair×= (! p) idp) idp ⟩
                                  ! (ap (λ r → fst r) (pair×= (! p) idp)) ∙ idp
                                    =⟨ ap (λ q → ! q ∙ idp) (ap-fst (! p) idp) ⟩
                                  ! (! p) ∙ idp
                                    =⟨ ∙-unit-r _ ⟩
                                  ! (! p)
                                    =⟨ !-! p ⟩
                                  p
                                    ∎))})

    -- finally: pointed maps from bool are actually just one element in the codomain.
    from-bool∙-single : (⊙Sphere {i} O →̇ D̂) ≃ D
    from-bool∙-single = (⊙Sphere {i} O →̇ D̂)
                           ≃⟨ from-bool∙ ⁻¹ ⟩
                         (Σ (D × D) λ d2 → fst d2 == d₀)
                           ≃⟨ Σ-sngltn ⟩
                         D
                           ≃∎ 
                   
    -- very good - it computes as it should!
    reduce : ((⊙Sphere {i} O) →̇ D̂) → D
    reduce (f , _) = f ff₀

    test : reduce == fst from-bool∙-single
    test = idp


{-    -- Given a b : B̂, we can form a function Sphere O →̇ B̂ which is an equivalence
    expand : {B̂ : Ptd i} → (b : fst B̂) → ((⊙Sphere {i} O) →̇ B̂)
    expand {B̂} b = (λ { (lift true) → snd B̂ ; (lift false) → b }) , idp

    reduce : {B̂ : Ptd i} → ((⊙Sphere {i} O) →̇ B̂) → (fst B̂)
    reduce {B , b₀} (f , _) = f ff₀

    test : 

    bool∙-trivial₁ : {X̂ : Ptd i} → (⊙Sphere {i} O →̇ X̂) ≃ fst X̂ × (Σ (fst X̂) λ x → x == snd X̂)
    bool∙-trivial₁ {X , x₀} = {!!}
  

    reduce-equiv : {B̂ : Ptd i} → is-equiv (reduce {B̂})
    reduce-equiv {B̂} = is-eq reduce
                           expand
                           (λ _ → idp)
                           (λ {(f , p) → {! p!}})
    --                         → pair= (λ= (λ { (lift true) → ! p ; (lift false) → idp }))
    --                                 {!!} })



  {- Two useful small helper lemma:
     If the first map has the O-sphere (i.e. Bool) as its domain,
     we can simplify. -}
    reduce-O-Sphere : {B̂ Ĉ : Ptd i}
                      (f̂ : ⊙Sphere {i} O →̇ B̂)
                      (ĝ : B̂ →̇ Ĉ)
                      → (isNull∙ (ĝ ⊙∘ f̂)) ≃ ((fst (ĝ ⊙∘ f̂) ff₀) == snd Ĉ) -- WRONG!!!
    reduce-O-Sphere {B , b₀} {C , c₀} f̂ ĝ =
                    let
                      f = fst f̂
                      p = snd f̂
                      g = fst ĝ
                      q = snd ĝ 
                    in
                      isNull∙ (ĝ ⊙∘ f̂)
                        ≃⟨ {!equivalence between isNull∙ and isNull∙'!} ⟩
                      (Σ ((x : bool) → g (f x) == c₀)
                        λ k → (k tt₀) == (ap g p ∙ q))
                        ≃⟨ {!!} ⟩
                      g (f ff₀) == c₀ 
                        ≃⟨ ide _ ⟩
                      (fst (ĝ ⊙∘ f̂) ff₀) == c₀
                        ≃∎

    {- This means that, if we quantify over f on both sides: -}
    red-O-Sph-quant : {B̂ Ĉ : Ptd i}
                      (ĝ : B̂ →̇ Ĉ)
                      → ((f̂ : ⊙Sphere {i} O →̇ B̂) → isNull∙ (ĝ ⊙∘ f̂))
                         ≃
                        (isNulld ĝ)
    red-O-Sph-quant {B̂} {Ĉ} ĝ =
                    let
                      g = fst ĝ
                      q = snd ĝ 
                    in
                      ((f̂ : ⊙Sphere {i} O →̇ B̂) → isNull∙ (ĝ ⊙∘ f̂))
                        ≃⟨ {!!} ⟩
                     {!(x : bool) → ((fst (ĝ ⊙∘ f̂) x) == snd Ĉ)!}
                        ≃⟨ {!!} ⟩
                      {!(x : ⊙Sphere {i})!}
                        ≃⟨ {!!} ⟩
                      {!(x : ⊙Sphere {i})!}
                        ≃∎ 

-}

  -- reminder: equiv-Π-l is very useful

  module _ {B̂ Ĉ : Ptd i} (m : Nat)
           (g : B̂ →̇ Ĉ) where

    c₀ = snd (⊙Ω^ m Ĉ)

    null-on-pspaces :
      ((f : (⊙Sphere* {i} m) →̇ B̂) → isNull∙ (g ⊙∘ f))
      ≃
      isNulld (ap^ m g)
      
    null-on-pspaces = -- {!equiv-Π-l!}

      ((f : (⊙Sphere* {i} m) →̇ B̂) → isNull∙ (g ⊙∘ f))

        ≃⟨ equiv-Π-r (λ f → isNull-Φ-Sphere m f g) ⟩

      ((f : (⊙Sphere* {i} m) →̇ B̂) → isNull∙ ((ap^ m g) ⊙∘ Φ-iter (⊙Sphere* {i} O) B̂ m f))

        ≃⟨ equiv-Π-l
             {A = (⊙Sphere* {i} m) →̇ B̂}
             {B = (⊙Sphere* {i} O) →̇ (⊙Ω^ m B̂)}
             (λ f' → isNull∙ ((ap^ m g) ⊙∘ f'))
             {h = Φ-iter (⊙Sphere* {i} O) B̂ m}
             (Φ-iter-equiv _ _ m)
              ⟩

      ((f' : (⊙Sphere* {i} O) →̇ (⊙Ω^ m B̂)) → isNull∙ ((ap^ m g) ⊙∘ f'))

        ≃⟨ {!!} ⟩

      {!!}

        ≃⟨ {!!} ⟩

      {!!}

        ≃⟨ {!!} ⟩

      {!!}

        ≃⟨ {!!} ⟩

      {!!}
        ≃∎













{-
((f : (⊙Sphere* {i} m) →̇ B̂) → isNull∙' ((ap^ m g) ⊙∘ Φ-iter (⊙Sphere* {i} O) B̂ m f))
        ≃⟨ ide _ ⟩ 
      ((f : (⊙Sphere* {i} m) →̇ B̂) →
          Σ ((x : fst (⊙Sphere* {i} O))
              → fst ((ap^ m g) ⊙∘ Φ-iter (⊙Sphere* {i} O) B̂ m f) x == c₀)
            (λ h → h tt₀ == {!!}))

        -- now, we get rid of the complicated type of f.
        ≃⟨ equiv-Π-l
             {A = (⊙Sphere* {i} m) →̇ B̂}
             {B = (⊙Sphere* {i} O) →̇ (⊙Ω^ m B̂)}
             (λ f' → Σ ((x : fst (⊙Sphere* {i} O))
                         → fst ((ap^ m g) ⊙∘ f') x == c₀)
                       (λ h → h _ == _))
             {h = Φ-iter (⊙Sphere* O) B̂ m}
             {!!}
              ⟩
             
      ((f' : (⊙Sphere* {i} O) →̇ (⊙Ω^ m B̂)) →
          Σ (((x : fst (⊙Sphere* {i} O))
              → fst ((ap^ m g) ⊙∘ f') x == c₀)) (λ h → h _ == _))

        ≃⟨ {!!} ⟩ 
--      {!!}
--        ≃⟨ {!!} ⟩ 
      isNulld (ap^ m g)
        ≃∎ 
-}
