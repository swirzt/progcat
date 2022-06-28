module MonoidPaC where

open import Categories
open import Library

record Monoid : Set₁  where
  constructor mon
  infixr 7 _∙_
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier
         ε       : Carrier
         lid     : {x : Carrier} → ε ∙ x ≅ x
         rid     : {x : Carrier} → x ∙ ε ≅ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≅ x ∙ (y ∙ z)
open Monoid

record mon-hom (M N : Monoid) : Set₀ where
    constructor monhom
    open Monoid M renaming (Carrier to CM ; ε to ε₁ ;  _∙_ to _∙M_)
    open Monoid N renaming (Carrier to CN ; ε to ε₂ ;  _∙_ to _∙N_)
    field
        morph : CM → CN
        preserves-unit : morph ε₁ ≅ ε₂
        preserves-mult : ∀{x y} → morph (x ∙M y) ≅ morph x ∙N morph y
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

module MonProducts where
    open import Categories.Products CatMon

    --           C
    --         / | \
    --        /  |  \
    --       /   |   \
    --    f /    |    \ g
    --     /     |     \
    --    /      |      \
    --   /       |⟨f,g⟩   \
    --  /   π₁   v   π₂   \
    -- A <----- AxB -----> B
        

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
                      π₁
                      π₂
                      HomProd
                      (mon-hom-eq refl)
                      (mon-hom-eq refl)
                      proofUnico
                                where π₁ : {A B : Monoid} → mon-hom (MonProd A B) A
                                      π₁ = monhom fst refl refl
                                      π₂ : {A B : Monoid} → mon-hom (MonProd A B) B
                                      π₂ = monhom snd refl refl
                                      proofUnico : {A B C : Monoid} {f : mon-hom C A} {g : mon-hom C B} {h : mon-hom C (MonProd A B)} → mon-hom-op π₁ h ≅ f → mon-hom-op π₂ h ≅ g → h ≅ HomProd f g
                                      proofUnico {_} {_} {_} {f} {g} {h} eq1 eq2 = mon-hom-eq (ext (λ x → proof 
                                                                                                          morph h x
                                                                                                          ≅⟨ refl ⟩ -- Expando ambos lados
                                                                                                          fst (morph h x) , snd (morph h x)
                                                                                                          ≅⟨ refl ⟩ -- composición de funciones
                                                                                                          (fst ∘ morph h) x , (snd ∘ morph h) x
                                                                                                          ≅⟨ refl ⟩ -- es el morph del producto en la categoria
                                                                                                          morph (mon-hom-op π₁ h) x , morph (mon-hom-op π₂ h) x
                                                                                                          ≅⟨ cong₂ (λ hf hg → (morph hf) x , (morph hg) x) eq1 eq2 ⟩ -- mon-hom-op πₙ h ≅ πₙ ∙ h 
                                                                                                          morph f x , morph g x
                                                                                                          ≅⟨ refl ⟩ -- definición de morph en HomProd
                                                                                                          morph (HomProd f g) x
                                                                                                          ∎))
                                    --   proofUnico eq1 eq2 = mon-hom-eq (ext (λ x → cong₂ (λ f g → morph f x , morph g x) eq1 eq2))
-- ========================================


















module MonCoproducts where
    open import Data.Sum using (_⊎_) renaming (inj₁ to Inl ; inj₂ to Inr)
    open import Categories.Coproducts CatMon

    --           C
    --         / ∧ \
    --        /  |  \
    --       /   |   \
    --    f /    |    \ g
    --     /     |     \
    --    /      |      \
    --   /       |[f,g]  \
    --  / inj₁   |   inj₂ \
    -- A -----> A+B <----- B

    MonCoprod : (M N : Monoid) → Monoid
    MonCoprod (mon Carrier₁ _∙₁_ ε₁ lid₁ rid₁ assoc₁) (mon Carrier₂ _∙₂_ ε₂ lid₂ rid₂ assoc₂) =
              mon (Carrier₁ ⊎ Carrier₂)
                  comp
                  {!   !}
                  {!   !}
                  {!   !}
                  {!   !}
                    where comp : Carrier₁ ⊎ Carrier₂ → Carrier₁ ⊎ Carrier₂ → Carrier₁ ⊎ Carrier₂
                          comp (Inl x) (Inl y) = Inl (x ∙₁ y)
                          comp (Inr x) (Inr y) = Inr (x ∙₂ y)
                          comp (Inl x) (Inr y) = {!   !}
                          comp (Inr x) (Inl y) = {!   !}
-- ========================================


















module MonCoproducts2 where
    open import Categories.Coproducts CatMon
    open MonProducts

    --           C
    --         / ∧ \
    --        /  |  \
    --       /   |   \
    --    f /    |    \ g
    --     /     |     \
    --    /      |      \
    --   /       |[f,g]  \
    --  / inj₁   |   inj₂ \
    -- A -----> A+B <----- B

    MonCoprod : Coproducts
    MonCoprod = coproduct
                MonProd
                inj1
                inj2
                [_,_]
                (λ {A} {B} {C} {f} {g} → law1 {A} {B} {C} {f} {g})
                (λ {A} {B} {C} {f} {g} → law2 {A} {B} {C} {f} {g})
                law3
                where   inj1 : {A B : Monoid} → mon-hom A (MonProd A B)
                        inj1 {A} {B} = let  open Monoid A renaming (Carrier to CA; ε to εA ;  _∙_ to _∙A_)
                                            open Monoid B renaming (Carrier to CB; ε to εB ;  _∙_ to _∙B_ ; lid to lidB)
                                       in monhom (_, εB) refl (cong ((_ ∙A _) ,_) (sym lidB))
                        inj2 : {A B : Monoid} → mon-hom B (MonProd A B)
                        inj2 {A} {B} = let  open Monoid A renaming (Carrier to CA; ε to εA ;  _∙_ to _∙A_ ; lid to lidA)
                                            open Monoid B renaming (Carrier to CB; ε to εB ;  _∙_ to _∙B_)
                                        in monhom (εA ,_) refl (cong (_, (_ ∙B _)) (sym lidA))
                        [_,_] : {A B C : Monoid} → mon-hom A C → mon-hom B C → mon-hom (MonProd A B) C
                        [_,_] {A} {B} {C} f g = let open Monoid A renaming (Carrier to CA; ε to εA ;  _∙_ to _∙A_ ; lid to lidA)
                                                    open Monoid B renaming (Carrier to CB; ε to εB ;  _∙_ to _∙B_ ; lid to lidB)
                                                    open Monoid C renaming (Carrier to CC; ε to εC ;  _∙_ to _∙C_ ; lid to lidC)
                                                in monhom (λ {(a , b) → morph f a ∙C morph g b}) (proof
                                                                                                morph f εA ∙C morph g εB
                                                                                                ≅⟨ cong₂ _∙C_ (preserves-unit f) (preserves-unit g) ⟩
                                                                                                εC ∙C εC
                                                                                                ≅⟨ lidC ⟩
                                                                                                εC
                                                                                                ∎)
                                                                                                (λ {x} {y} → proof
                                                                                                morph f (fst x ∙A fst y) ∙C morph g (snd x ∙B snd y)
                                                                                                ≅⟨ cong₂ _∙C_ (preserves-mult f) (preserves-mult g) ⟩
                                                                                                (morph f (fst x) ∙C morph f (fst y)) ∙C (morph g (snd x) ∙C morph g (snd y))
                                                                                                ≅⟨ {!   !} ⟩
                                                                                                {!   !}
                                                                                                ≅⟨ {!   !} ⟩
                                                                                                {!   !}
                                                                                                ≅⟨ {!   !} ⟩
                                                                                                {!   !}
                                                                                                ≅⟨ {!   !} ⟩
                                                                                                (morph f (fst x) ∙C morph g (snd x)) ∙C (morph f (fst y) ∙C morph g (snd y))
                                                                                                ∎)
                        law1 : {A B C : Monoid} → {f : mon-hom  A C} {g : mon-hom B C} → mon-hom-op [ f , g ] inj1 ≅ f
                        law1 {A} {B} {C} {f} {g} = let  open Monoid C using () renaming (_∙_ to _∙C_) 
                                                        open Monoid B using () renaming (ε to nB) in
                                                    mon-hom-eq (ext (λ x → proof
                                                                        morph (mon-hom-op [ f , g ] inj1) x
                                                                        ≅⟨ refl ⟩
                                                                        morph f x ∙C morph g nB
                                                                        ≅⟨ cong (morph f x ∙C_) (preserves-unit g) ⟩
                                                                        morph f x ∙C ε C
                                                                        ≅⟨ rid C ⟩
                                                                        morph f x
                                                                        ∎))
                        law2 : {A B C : Monoid} → {f : mon-hom  A C} {g : mon-hom B C} → mon-hom-op [ f , g ] inj2 ≅ g
                        law2 {A} {B} {C} {f} {g} = let  open Monoid C using () renaming (_∙_ to _∙C_) 
                                                        open Monoid A using () renaming (ε to nA) in
                                                    mon-hom-eq (ext (λ x → proof
                                                                        morph (mon-hom-op [ f , g ] inj2) x
                                                                        ≅⟨ refl ⟩
                                                                        morph f nA ∙C morph g x
                                                                        ≅⟨ cong (_∙C morph g x) (preserves-unit f) ⟩
                                                                        ε C ∙C morph g x
                                                                        ≅⟨ lid C ⟩
                                                                        morph g x
                                                                        ∎))
                        law3 : {A B C : Monoid} → {f : mon-hom  A C} {g : mon-hom B C} {h : mon-hom (MonProd A B) C} → mon-hom-op h inj1 ≅ f → mon-hom-op h inj2 ≅ g → h ≅ [ f , g ]
                        law3 {A} {B} {C} {f} {g} {h} eq1 eq2 = let open Monoid C using () renaming (_∙_ to _∙C_) in
                                                                mon-hom-eq (ext (λ x → {!   !}))
-- ========================================


















module MonCoproducts3 where
    open MonProducts

    --           C
    --         / ∧ \
    --        /  |  \
    --       /   |   \
    --    f /    |    \ g
    --     /     |     \
    --    /      |      \
    --   /       |[f,g]  \
    --  / inj₁   |   inj₂ \
    -- A -----> A+B <----- B

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



-- ========================================


















-- ============== INICIALES Y TERMINALES =======================

unitMon : Monoid
unitMon = mon ⊤
              (λ _ _ → tt)
              tt
              refl
              refl
              refl
-- ==========

open import Categories.Initial

-- i : ∀{X} → Hom C I X
-- law : ∀{X}{f : Hom C I X} → i {X} ≅ f 

CatMonInit : Initial CatMon unitMon
CatMonInit = init
                ifunc
                demfunc
            where ifunc : {X : Monoid} → mon-hom unitMon X
                  ifunc {X} = monhom (λ {tt → ε X}) refl (sym (lid X))
                  demfunc : {X : Monoid} → {f : mon-hom unitMon X} → ifunc {X} ≅ f
                  demfunc {X} {f} = mon-hom-eq (ext (λ {tt → sym (preserves-unit f)}))
--
open import Categories.Terminal

-- t : ∀{X} → Hom C X T
-- law : ∀{X}{f : Hom C X T} → t {X} ≅ f

CatMonTerm : Terminal CatMon unitMon
CatMonTerm = term
                (monhom (λ- tt) refl refl)
                (mon-hom-eq (ext (λ- refl)))