module MonoidPaC where

open import Categories
open import Library

record Monoid : Set₁  where
  constructor mon
  infixr 7 _∙_
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier  {- ∙ = \. -}
         ε       : Carrier
         lid     : {x : Carrier} → ε ∙ x ≅ x
         rid     : {x : Carrier} → x ∙ ε ≅ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≅ x ∙ (y ∙ z)
open Monoid

record mon-hom (M N : Monoid) : Set₀ where
    constructor monhom
    open Monoid M renaming (Carrier to CM ; ε to ε₁ ;  _∙_ to _∙₁_)
    open Monoid N renaming (Carrier to CN ; ε to ε₂ ;  _∙_ to _∙₂_)
    field
        morph : CM → CN
        preserves-unit : morph ε₁ ≅ ε₂
        preserves-mult : ∀{x y} → morph (x ∙₁ y) ≅ morph x ∙₂ morph y
open mon-hom        

mon-hom-op : {X Y Z : Monoid} → (G : mon-hom Y Z) → (F : mon-hom X Y) → mon-hom X Z
mon-hom-op {X} {Y} {Z} (monhom morphG unitG multG) (monhom morphF unitF multF) = monhom (morphG ∘ morphF) demunit demmult
        where open Monoid X renaming (Carrier to CX; ε to εX ;  _∙_ to _∙X_)
              open Monoid Y renaming (ε to εY ;  _∙_ to _∙Y_)
              open Monoid Z renaming (ε to εZ ;  _∙_ to _∙Z_)
              demunit : morphG (morphF εX) ≅ εZ
              demunit = proof
                        morphG (morphF εX)
                        ≅⟨ cong morphG unitF ⟩
                        morphG εY
                        ≅⟨ unitG ⟩
                        εZ
                        ∎
              demmult : {x y : CX} → morphG (morphF (x ∙X y)) ≅ morphG (morphF x) ∙Z morphG (morphF y)
              demmult {x} {y} = proof
                                morphG (morphF (x ∙X y))
                                ≅⟨ cong morphG multF ⟩
                                morphG (morphF x ∙Y morphF y)
                                ≅⟨ multG ⟩
                                morphG (morphF x) ∙Z morphG (morphF y)
                                ∎

mon-hom-eq : {X Y : Monoid} {h h' : mon-hom X Y} → morph h ≅ morph h' → h ≅ h'
mon-hom-eq {X} {Y} {monhom morphG unitG multG} {monhom .morphG unitF multF} refl =
           cong₂ (monhom morphG) (ir unitG unitF) (i2ir multG multF)

CatMon : Cat
CatMon = record
            { Obj = Monoid 
            ; Hom = mon-hom
            ; iden = monhom id refl refl
            ; _∙_ = mon-hom-op
            ; idl = mon-hom-eq refl
            ; idr = mon-hom-eq refl
            ; ass = mon-hom-eq refl
            }
open Cat CatMon

open import Categories.Products CatMon

MonProd : (M N : Monoid) → Monoid
MonProd (mon Carrier₁ _∙₁_ ε₁ lid₁ rid₁ assoc₁) (mon Carrier₂ _∙₂_ ε₂ lid₂ rid₂ assoc₂) =
        mon (Carrier₁ × Carrier₂)
            (λ g f → (fst g ∙₁ fst f) , (snd g ∙₂ snd f))
            (ε₁ , ε₂) 
            (cong₂ _,_ lid₁ lid₂)
            (cong₂ _,_ rid₁ rid₂)
            (cong₂ _,_ assoc₁ assoc₂)

HomProd : {A B C : Monoid} → mon-hom C A → mon-hom C B → mon-hom C (MonProd A B)
HomProd {A} {B} {C} (monhom morph₁ preserves-unit₁ preserves-mult₁) (monhom morph₂ preserves-unit₂ preserves-mult₂) =
        monhom (λ x → morph₁ x , morph₂ x)
               (cong₂ _,_ preserves-unit₁ preserves-unit₂)
               (cong₂ _,_ preserves-mult₁ preserves-mult₂)

CatMonProd : Products
CatMonProd = prod MonProd
                  (monhom fst refl refl)
                  (monhom snd refl refl)
                  HomProd
                  (mon-hom-eq refl)
                  (mon-hom-eq refl)
                  λ {f = f} {g = g} eq1 eq2 → mon-hom-eq (cong₂ (λ f g x → morph f x , morph g x) eq1 eq2)


open import Categories.Coproducts CatMon

open import Data.Sum using (_⊎_) renaming (inj₁ to Inl ; inj₂ to Inr)
{- 
MonCoprod : (M N : Monoid) → Monoid
MonCoprod (mon Carrier₁ _∙_ ε₁ lid₁ rid₁ assoc₁) (mon Carrier₂ _∙_₁ ε₂ lid₂ rid₂ assoc₂) =
          mon (Carrier₁ ⊎ Carrier₂)
              comp
              {!   !}
              {!   !}
              {!   !}
              {!   !}
                where comp : Carrier₁ ⊎ Carrier₂ → Carrier₁ ⊎ Carrier₂ → Carrier₁ ⊎ Carrier₂
                      comp (Inl x) (Inl y) = Inl (x ∙ y)
                      comp (Inl x) (Inr y) = {!   !}
                      comp (Inr x) (Inl y) = {!   !}
                      comp (Inr x) (Inr y) = Inr (x ∙ y ₁)
-}
open import Data.List

++eq : ∀{X : Set} → {xs : List X} → xs ++ [] ≅ xs
++eq {X} {[]} = refl
++eq {X} {x ∷ xs} = cong (x ∷_) ++eq

++assoc : ∀{X : Set} → {xs ys zs : List X} → (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
++assoc {X} {[]} {ys} {zs} = refl
++assoc {X} {x ∷ xs} {ys} {zs} = cong (x ∷_) (++assoc {xs = xs})

reduce : {M N : Monoid} → List (Carrier M ⊎ Carrier N) → List (Carrier M ⊎ Carrier N)
reduce {M} {N} = foldr func []
        where open Monoid M renaming (Carrier to CM; ε to εM ;  _∙_ to _∙M_)
              open Monoid N renaming (Carrier to CN; ε to εN ;  _∙_ to _∙N_)
              func : Carrier M ⊎ Carrier N → List (Carrier M ⊎ Carrier N) → List (Carrier M ⊎ Carrier N)
              func (Inl x) (Inl y ∷ xs) = Inl (x ∙M y) ∷ xs
              func (Inl εM) xs = xs
              func (Inr x) (Inr y ∷ xs) = Inr (x ∙N y) ∷ xs
              func (Inr εN) xs = xs
              func x xs = x ∷ xs

record Eithers (M N : Monoid) : Set where
    constructor eith
    field toList : List (Carrier M ⊎ Carrier N)
          cond : reduce {M} {N} toList ≅ toList
open Eithers

eith-prod : {M N : Monoid} → (x y : Eithers M N) → Eithers M N
eith-prod {M} {N} (eith toList cond) (eith toList₁ cond₁) =
           eith (reduce {M} {N} (toList ++ toList₁)) (demapp cond cond₁)
            where demapp : ∀{xs} → ∀{ys} → reduce {M} {N} xs ≅ xs → reduce {M} {N} ys ≅ ys → reduce {M} {N} (reduce {M} {N} (xs ++ ys)) ≅ reduce (xs ++ ys)
                  demapp eqx eqy = {!   !}

eith-eq : {M N : Monoid} {x y : Eithers M N} → toList x ≅ toList y → x ≅ y
eith-eq {M} {N} {eith toList₁ cond₁} {eith .toList₁ cond₂} refl = cong (eith toList₁) (ir cond₁ cond₂)

-- ∣_∣ : Set → Monoid
-- ∣ M ∣ = mon (List M) _++_ [] refl ++eq (λ {x} → ++assoc {xs = x})

EithersMon : (M N : Monoid) → Monoid
EithersMon M N = mon (Eithers M N)
                     eith-prod
                     (eith [] refl)
                     (λ {x} → eith-eq (cond x))
                     (λ {x} → eith-eq (trans (cong (reduce {M} {N})  ++eq) (cond x)))
                     λ {x} {y} {z} → eith-eq (proof
                                              reduce ((reduce (toList x ++ toList y)) ++ toList z)
                                              ≅⟨ cong (λ x₁ → reduce ({! x₁  !} ++ {!   !})) (cond (eith-prod x y)) ⟩
                                              reduce ((toList x ++ toList y) ++ toList z)
                                              ≅⟨ {!   !} ⟩
                                              {!   !}
                                              ≅⟨ {!   !} ⟩
                                              {!   !}
                                              ≅⟨ {!   !} ⟩
                                              {!   !}
                                              ≅⟨ {!   !} ⟩
                                              reduce ( toList x ++ (reduce (toList y ++ toList z)) )
                                              ∎)


MonCoprod : Coproducts
MonCoprod = coproduct
            {!   !}
            {!   !}
            {!   !}
            {!   !}
            {!   !}
            {!   !}
            {!   !}

-- ============== INICIALES Y TERMINALES =======================

open import Categories.Initial

unitMon : Monoid
unitMon = mon ⊤
              (λ _ _ → tt)
              tt
              refl
              refl
              refl

CatMonInit : Initial CatMon unitMon
CatMonInit = init ifunc
                  demfunc
            where ifunc : {X : Monoid} → mon-hom unitMon X
                  ifunc {X} = monhom (λ {tt → ε X}) refl (sym (lid X))
                  demfunc : {X : Monoid} → {f : mon-hom unitMon X} → ifunc {X} ≅ f
                  demfunc {X} {f} = mon-hom-eq (ext (λ {tt → sym (preserves-unit f)}))

open import Categories.Terminal

CatMonTerm : Terminal CatMon unitMon
CatMonTerm = term (monhom (λ- tt) refl refl)
                  (mon-hom-eq (ext (λ- refl)))