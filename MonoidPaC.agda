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

unitMon : Monoid
unitMon = mon ⊤
              (λ _ _ → tt)
              tt
              refl
              refl
              refl

-- open import Categories.Coproducts CatMon

open import Data.Sum using (_⊎_) renaming (inj₁ to Inl ; inj₂ to Inr)

-- MonCoprod : (M N : Monoid) → Monoid
-- MonCoprod (mon Carrier₁ _∙_ ε₁ lid₁ rid₁ assoc₁) (mon Carrier₂ _∙_₁ ε₂ lid₂ rid₂ assoc₂) =
--           mon (Carrier₁ ⊎ Carrier₂)
--               comp
--               {!   !}
--               {!   !}
--               {!   !}
--               {!   !}
--                 where comp : Carrier₁ ⊎ Carrier₂ → Carrier₁ ⊎ Carrier₂ → Carrier₁ ⊎ Carrier₂
--                       comp (Inl x) (Inl y) = Inl (x ∙ y)
--                       comp (Inl x) (Inr y) = {!   !}
--                       comp (Inr x) (Inl y) = {!   !}
--                       comp (Inr x) (Inr y) = Inr (x ∙ y ₁)


-- open import Data.List

-- ++eq : ∀{X : Set} → {xs : List X} → xs ++ [] ≅ xs
-- ++eq {X} {[]} = refl
-- ++eq {X} {x ∷ xs} = cong (x ∷_) ++eq

-- ++assoc : ∀{X : Set} → {xs ys zs : List X} → (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
-- ++assoc {X} {[]} {ys} {zs} = refl
-- ++assoc {X} {x ∷ xs} {ys} {zs} = cong (x ∷_) (++assoc {xs = xs})
 
-- open import Relation.Nullary using (Dec ; yes ; no) renaming (¬_ to neg)

-- esNeutro : {M : Monoid} → (x : Carrier M) → Dec (x ≅ ε M)
-- esNeutro = {!   !}

-- reduce : {M N : Monoid} → List (Σ (Carrier M) (λ x → Dec (x ≅ ε M)) ⊎ Σ (Carrier N) (λ x → Dec (x ≅ ε N))) → List (Σ (Carrier M) (λ x → Dec (x ≅ ε M)) ⊎ Σ (Carrier N) (λ x → Dec (x ≅ ε N)))
-- reduce {M} {N} [] = []
-- reduce {M} {N} (Inl (x , eq) ∷ xs) with eq
-- ... | yes p = reduce {M} {N} xs
-- ... | no np with reduce {M} {N} xs
-- ...         | [] = Inl (x , eq) ∷ []
-- ...         | Inr y ∷ ys = Inl (x , eq) ∷ Inr y ∷ ys
-- ...         | Inl (y , eqy) ∷ ys with esNeutro {M} (_∙_ M x y)
-- ...                               | yes pn = ys
-- ...                               | no npn = Inl ((_∙_ M x y) , no npn) ∷ ys
-- reduce {M} {N} (Inr (x , eq) ∷ xs) with eq
-- ... | yes p = reduce {M} {N} xs
-- ... | no np with reduce {M} {N} xs
-- ...         | [] = Inr (x , eq) ∷ []
-- ...         | Inl y ∷ ys = Inr (x , eq) ∷ Inl y ∷ ys
-- ...         | Inr (y , eqy) ∷ ys with esNeutro {N} (_∙_ N x y)
-- ...                               | yes pn = ys
-- ...                               | no npn = Inr ((_∙_ N x y) , no npn) ∷ ys


-- record Eithers (M N : Monoid) : Set where
--     constructor eith
--     field toList : List (Σ (Carrier M) (λ x → Dec (x ≅ ε M)) ⊎ Σ (Carrier N) (λ x → Dec (x ≅ ε N)))
--           -- cond : reduce {M} {N} toList ≅ toList
-- open Eithers

-- eith-prod : {M N : Monoid} → (x y : Eithers M N) → Eithers M N
-- eith-prod {M} {N} (eith toList₁ cond₁) (eith toList₂ cond₂) =
--            eith (reduce {M} {N} (toList₁ ++ toList₂)) (demapp cond₁ cond₂)
--             where demapp : ∀{xs} → ∀{ys} → reduce {M} {N} xs ≅ xs → reduce {M} {N} ys ≅ ys → reduce {M} {N} (reduce {M} {N} (xs ++ ys)) ≅ reduce (xs ++ ys)
--                   demapp eqx eqy = {!   !}

-- eith-eq : {M N : Monoid} {x y : Eithers M N} → toList x ≅ toList y → x ≅ y
-- eith-eq {M} {N} {eith toList₁ cond₁} {eith .toList₁ cond₂} refl = cong (eith toList₁) (ir cond₁ cond₂)

-- EithersMon : (M N : Monoid) → Monoid
-- EithersMon M N = mon (Eithers M N)
--                      eith-prod
--                      (eith [] refl)
--                      ?
--                      ?
--                      ?

-- EitherCoprod : Coproducts



-- MonCoprod : Coproducts
-- MonCoprod = coproduct
--             MonProd
--             inj1
--             inj2
--             [_,_]
--             (λ {A} {B} {C} {f} {g} → law1 {A} {B} {C} {f} {g})
--             (λ {A} {B} {C} {f} {g} → law2 {A} {B} {C} {f} {g})
--             law3
--                where inj1 : {A B : Monoid} → mon-hom A (MonProd A B)
--                      inj1 {A} {B} = let open Monoid A renaming (Carrier to CA; ε to εA ;  _∙_ to _∙A_)
--                                         open Monoid B renaming (Carrier to CB; ε to εB ;  _∙_ to _∙B_ ; lid to lidB)
--                                     in monhom (_, εB) refl (cong ((_ ∙A _) ,_) (sym lidB))
--                      inj2 : {A B : Monoid} → mon-hom B (MonProd A B)
--                      inj2 {A} {B} = let open Monoid A renaming (Carrier to CA; ε to εA ;  _∙_ to _∙A_ ; lid to lidA)
--                                         open Monoid B renaming (Carrier to CB; ε to εB ;  _∙_ to _∙B_)
--                                     in monhom (εA ,_) refl (cong (_, (_ ∙B _)) (sym lidA))
--                      [_,_] : {A B C : Monoid} → mon-hom A C → mon-hom B C → mon-hom (MonProd A B) C
--                      [_,_] {A} {B} {C} f g = let open Monoid A renaming (Carrier to CA; ε to εA ;  _∙_ to _∙A_ ; lid to lidA)
--                                                  open Monoid B renaming (Carrier to CB; ε to εB ;  _∙_ to _∙B_ ; lid to lidB)
--                                                  open Monoid C renaming (Carrier to CC; ε to εC ;  _∙_ to _∙C_ ; lid to lidC)
--                                              in monhom (λ {(a , b) → morph f a ∙C morph g b}) (proof
--                                                                                                morph f εA ∙C morph g εB
--                                                                                                ≅⟨ cong₂ _∙C_ (preserves-unit f) (preserves-unit g) ⟩
--                                                                                                εC ∙C εC
--                                                                                                ≅⟨ lidC ⟩
--                                                                                                εC
--                                                                                                ∎)
--                                                                                               (λ {x} {y} → proof
--                                                                                                morph f (fst x ∙A fst y) ∙C morph g (snd x ∙B snd y)
--                                                                                                ≅⟨ cong₂ _∙C_ (preserves-mult f) (preserves-mult g) ⟩
--                                                                                                (morph f (fst x) ∙C morph f (fst y)) ∙C (morph g (snd x) ∙C morph g (snd y))
--                                                                                                ≅⟨ {!   !} ⟩
--                                                                                                {!   !}
--                                                                                                ≅⟨ {!   !} ⟩
--                                                                                                {!   !}
--                                                                                                ≅⟨ {!   !} ⟩
--                                                                                                {!   !}
--                                                                                                ≅⟨ {!   !} ⟩
--                                                                                                (morph f (fst x) ∙C morph g (snd x)) ∙C (morph f (fst y) ∙C morph g (snd y))
--                                                                                                ∎)
--                      law1 : {A B C : Monoid} → {f : mon-hom  A C} {g : mon-hom B C} → mon-hom-op [ f , g ] inj1 ≅ f
--                      law1 {A} {B} {C} {f} {g} = let open Monoid C using () renaming (_∙_ to _∙C_) 
--                                                     open Monoid B using () renaming (ε to nB) in
--                                                 mon-hom-eq (ext (λ x → proof
--                                                                        morph (mon-hom-op [ f , g ] inj1) x
--                                                                        ≅⟨ refl ⟩
--                                                                        morph f x ∙C morph g nB
--                                                                        ≅⟨ cong (morph f x ∙C_) (preserves-unit g) ⟩
--                                                                        morph f x ∙C ε C
--                                                                        ≅⟨ rid C ⟩
--                                                                        morph f x
--                                                                        ∎))
--                      law2 : {A B C : Monoid} → {f : mon-hom  A C} {g : mon-hom B C} → mon-hom-op [ f , g ] inj2 ≅ g
--                      law2 {A} {B} {C} {f} {g} = let open Monoid C using () renaming (_∙_ to _∙C_) 
--                                                     open Monoid A using () renaming (ε to nA) in
--                                                 mon-hom-eq (ext (λ x → proof
--                                                                        morph (mon-hom-op [ f , g ] inj2) x
--                                                                        ≅⟨ refl ⟩
--                                                                        morph f nA ∙C morph g x
--                                                                        ≅⟨ cong (_∙C morph g x) (preserves-unit f) ⟩
--                                                                        ε C ∙C morph g x
--                                                                        ≅⟨ lid C ⟩
--                                                                        morph g x
--                                                                        ∎))
--                      law3 : {A B C : Monoid} → {f : mon-hom  A C} {g : mon-hom B C} {h : mon-hom (MonProd A B) C} → mon-hom-op h inj1 ≅ f → mon-hom-op h inj2 ≅ g → h ≅ [ f , g ]
--                      law3 {A} {B} {C} {f} {g} {h} eq1 eq2 = let open Monoid C using () renaming (_∙_ to _∙C_) in
--                                                             mon-hom-eq (ext (λ x → {!   !}))

record Commutative : Set₁ where
  constructor comm
  field
    monoid : Monoid
    cond : {x y : Carrier monoid} → _∙_ monoid x y ≅ _∙_ monoid y x
open Commutative

comm-hom : (M N : Commutative) → Set₀
comm-hom M N = mon-hom (monoid M) (monoid N)

CommCatMon : Cat
CommCatMon = record
             { Obj = Commutative
             ; Hom = comm-hom
             ; iden = monhom id refl refl
             ; _∙_ = mon-hom-op
             ; idl = mon-hom-eq refl
             ; idr = mon-hom-eq refl
             ; ass = mon-hom-eq refl
             }
module CommutativeCoprod where
    open import Categories.Coproducts CommCatMon

    CommMonProd : (M N : Commutative) → Commutative
    CommMonProd M N = comm (MonProd (monoid M) (monoid N)) (cong₂ _,_ (cond M) (cond N))

    CommCoprod : Coproducts
    CommCoprod = coproduct
                 CommMonProd
                 (λ {A} {B} → inj1 {A} {B})
                 (λ {A} {B} → inj2 {A} {B})
                 (λ {A} {B} {C} → [_,_] {A} {B} {C})
                 (λ {A} {B} {C} {f} {g} → law1 {A} {B} {C} {f} {g})
                 (λ {A} {B} {C} {f} {g} → law2 {A} {B} {C} {f} {g})
                 (λ {A} {B} {C} {f} {g} {h} → law3 {A} {B} {C} {f} {g} {h})
                  where inj1 : {A B : Commutative} → comm-hom A (CommMonProd A B)
                        inj1 {A} {B} = let open Monoid (monoid A) using () renaming (_∙_ to _∙A_)
                                           open Monoid (monoid B) using () renaming (ε to εB ; lid to lidB)
                                       in monhom (_, εB) refl (cong ((_ ∙A _) ,_) (sym lidB))
                        inj2 : {A B : Commutative} → comm-hom B (CommMonProd A B)
                        inj2 {A} {B} = let open Monoid (monoid A) using () renaming (ε to εA ; lid to lidA)
                                           open Monoid (monoid B) using () renaming (_∙_ to _∙B_)
                                       in monhom (εA ,_) refl (cong (_, (_ ∙B _)) (sym lidA))
                        [_,_] : {A B C : Commutative} → comm-hom A C → comm-hom B C → comm-hom (CommMonProd A B) C
                        [_,_] {A} {B} {C} f g = let open Monoid (monoid A) renaming (Carrier to CA; ε to εA ;  _∙_ to _∙A_ ; lid to lidA)
                                                    open Monoid (monoid B) renaming (Carrier to CB; ε to εB ;  _∙_ to _∙B_ ; lid to lidB)
                                                    open Monoid (monoid C) renaming (Carrier to CC; ε to εC ;  _∙_ to _∙C_ ; lid to lidC)
                                                in monhom (λ {(x , y) → morph f x ∙C morph g y}) (proof morph f εA ∙C morph g εB
                                                                                                        ≅⟨ cong₂ _∙C_ (preserves-unit f) (preserves-unit g) ⟩
                                                                                                        εC ∙C εC
                                                                                                        ≅⟨ lidC ⟩
                                                                                                        εC
                                                                                                        ∎)
                                                                                                 (λ {x} {y} → proof
                                                                                                               morph f (fst x ∙A fst y) ∙C morph g (snd x ∙B snd y)
                                                                                                              ≅⟨ cong₂ _∙C_ (preserves-mult f) (preserves-mult g) ⟩
                                                                                                              (morph f (fst x) ∙C morph f (fst y)) ∙C (morph g (snd x) ∙C morph g (snd y))
                                                                                                              ≅⟨ assoc (monoid C) ⟩
                                                                                                              morph f (fst x) ∙C (morph f (fst y) ∙C (morph g (snd x) ∙C morph g (snd y)))
                                                                                                              ≅⟨ cong (morph f (fst x) ∙C_) (sym (assoc (monoid C))) ⟩
                                                                                                              morph f (fst x) ∙C ((morph f (fst y) ∙C morph g (snd x)) ∙C morph g (snd y))
                                                                                                              ≅⟨ cong (morph f (fst x) ∙C_) (cong (_∙C morph g (snd y)) (cond C)) ⟩
                                                                                                              morph f (fst x) ∙C ((morph g (snd x) ∙C morph f (fst y)) ∙C morph g (snd y))
                                                                                                              ≅⟨ cong (morph f (fst x) ∙C_) (assoc (monoid C)) ⟩
                                                                                                              morph f (fst x) ∙C (morph g (snd x) ∙C (morph f (fst y) ∙C morph g (snd y)))
                                                                                                              ≅⟨ sym (assoc (monoid C)) ⟩
                                                                                                              (morph f (fst x) ∙C morph g (snd x)) ∙C (morph f (fst y) ∙C morph g (snd y))
                                                                                                              ∎)
                        law1 : {A B C : Commutative} → {f : comm-hom A C} {g : comm-hom B C} → mon-hom-op ([_,_] {A} {B} {C} f g) (inj1 {A} {B}) ≅ f
                        law1 {A} {B} {C} {f} {g} = let open Monoid (monoid C) using () renaming (_∙_ to _∙C_ ; ε to εC ; rid to ridC) 
                                                       open Monoid (monoid B) using () renaming (ε to εB) in
                                                   mon-hom-eq (ext (λ x → proof
                                                                          morph (mon-hom-op ([_,_] {A} {B} {C} f g) (inj1 {A} {B})) x
                                                                          ≅⟨ refl ⟩
                                                                          morph f x ∙C morph g εB
                                                                          ≅⟨ cong (morph f x ∙C_) (preserves-unit g) ⟩
                                                                          morph f x ∙C εC
                                                                          ≅⟨ ridC ⟩
                                                                          morph f x
                                                                          ∎))
                        law2 : {A B C : Commutative} → {f : comm-hom A C} {g : comm-hom B C} → mon-hom-op ([_,_] {A} {B} {C} f g) (inj2 {A} {B}) ≅ g
                        law2 {A} {B} {C} {f} {g} = let open Monoid (monoid C) using () renaming (_∙_ to _∙C_ ; ε to εC ; lid to lidC) 
                                                       open Monoid (monoid A) using () renaming (ε to εA) in
                                                   mon-hom-eq (ext (λ x → proof
                                                                          morph (mon-hom-op ([_,_] {A} {B} {C} f g) (inj2 {A} {B})) x
                                                                          ≅⟨ refl ⟩
                                                                          morph f εA ∙C morph g x
                                                                          ≅⟨ cong (_∙C morph g x) (preserves-unit f) ⟩
                                                                          εC ∙C morph g x
                                                                          ≅⟨ lidC ⟩
                                                                          morph g x
                                                                          ∎))
                        law3 : {A B C : Commutative} → {f : comm-hom  A C} {g : comm-hom B C} {h : comm-hom (CommMonProd A B) C} → mon-hom-op h (inj1 {A} {B}) ≅ f → mon-hom-op h (inj2 {A} {B}) ≅ g → h ≅ ([_,_] {A} {B} {C} f g)
                        law3 {A} {B} {C} {f} {g} {h} eq1 eq2 = let open Monoid (monoid C) using () renaming (_∙_ to _∙C_)
                                                                   open Monoid (monoid A) using () renaming (ε to εA ; _∙_ to _∙A_ ; rid to ridA)
                                                                   open Monoid (monoid B) using () renaming (ε to εB ; _∙_ to _∙B_ ; lid to lidB)
                                                                   open Monoid (monoid (CommMonProd A B)) using () renaming (_∙_ to _∙AB_) in
                                                               mon-hom-eq (ext (λ {(x , y) → proof morph h (x , y)
                                                                                                   ≅⟨ cong (morph h) (cong₂ _,_ (sym ridA) (sym lidB)) ⟩ -- aparecen identidades
                                                                                                   morph h (x ∙A εA , εB ∙B y)
                                                                                                   ≅⟨ refl ⟩ -- Definicion de producto en el monoide producto
                                                                                                   morph h ((x , εB) ∙AB (εA , y))
                                                                                                   ≅⟨ refl ⟩ -- definicion de injs
                                                                                                   morph h (morph (inj1 {A} {B}) x ∙AB morph (inj2 {A} {B}) y)
                                                                                                   ≅⟨ preserves-mult h ⟩
                                                                                                   morph h (morph (inj1 {A} {B}) x) ∙C morph h (morph (inj2 {A} {B}) y)
                                                                                                   ≅⟨ refl ⟩
                                                                                                   (morph h ∘ morph (inj1 {A} {B})) x ∙C (morph h ∘ morph (inj2 {A} {B})) y
                                                                                                   ≅⟨ cong₂ (λ a b → a x ∙C b y) (cong morph eq1) (cong morph eq2) ⟩
                                                                                                   morph f x ∙C morph g y
                                                                                                   ≅⟨ refl ⟩
                                                                                                   morph ([_,_] {A} {B} {C} f g) (x , y)
                                                                                                   ∎}))

module InitCoprod where
    open import Categories.Coproducts CatMon
    CatMonCoprod : Coproducts
    CatMonCoprod = coproduct (λ _ _ → unitMon)
                             (monhom (λ- tt) refl refl)
                             (monhom (λ- tt) refl refl)
                             comp
                             (mon-hom-eq {!   !})
                             (mon-hom-eq {!   !})
                             λ eq eq2 → mon-hom-eq {!   !}
                    where comp : {A B C : Monoid} → mon-hom A C → mon-hom B C → mon-hom unitMon C
                          comp {A} {B} {C} _ _  = monhom (λ {tt → ε C}) refl (sym (lid C))

module EQMon where
    open import Relation.Nullary using (Dec ; yes ; no) renaming (¬_ to neg)
    record eqMon : Set₁ where
        constructor eqmon
        field monoid : Monoid
              eq : (x : Carrier monoid) → Dec (x ≅ ε monoid)
    open eqMon
    
    open import Data.List
    reduce : {A B : eqMon} → List (Carrier (monoid A) ⊎ Carrier (monoid B)) → List (Carrier (monoid A) ⊎ Carrier (monoid B))
    reduce {A} {B} = foldr func []
                        where open Monoid (monoid A) using () renaming (_∙_ to _∙A_)
                              open Monoid (monoid B) using () renaming (_∙_ to _∙B_)
                              func : Carrier (monoid A) ⊎ Carrier (monoid B) → List (Carrier (monoid A) ⊎ Carrier (monoid B)) → List (Carrier (monoid A) ⊎ Carrier (monoid B))
                              func (Inl x) (Inl y ∷ xs) = func (Inl (x ∙A y)) xs
                              func (Inl x) xs with eq A x
                              ... | yes p = xs
                              ... | no np = Inl x ∷ xs
                              func (Inr x) (Inr y ∷ xs) = func (Inr (x ∙B y)) xs
                              func (Inr x) xs with eq B x
                              ... | yes p = xs
                              ... | no np = Inr x ∷ xs

    record Eithers (A B : eqMon) : Set where
        constructor eithers
        field toList : List (Carrier (monoid A) ⊎ Carrier (monoid B))
              cond : reduce {A} {B} toList ≅ toList
    


module IdealCoprod where
    record IdealMon : Set₁ where
        constructor ideal
        field monoid : Monoid
              _↓_ : ⊤ ⊎ (Carrier monoid) → (Carrier monoid) → ⊤ ⊎ (Carrier monoid)

            
              
-- ============== INICIALES Y TERMINALES =======================

open import Categories.Initial

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