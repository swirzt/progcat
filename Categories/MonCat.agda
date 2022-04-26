module Categories.MonCat where

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

MonCat : Monoid → Cat {lsuc lzero} {lzero}
MonCat (mon Carrier _∙_ ε lid rid assoc) = record
            { Obj = Lift (lsuc lzero) ⊤
            ; Hom = λ _ _ → Carrier
            ; iden = ε
            ; _∙_ = _∙_
            ; idl = lid
            ; idr = rid
            ; ass = assoc
            }

record Is-Monoid-Homo (M N : Monoid)(morph : Carrier M → Carrier N) : Set₁ where
   constructor monhom
   open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_)
   open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_)
   field
    preserves-unit : morph ε₁ ≅ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≅ morph x ∙₂ morph y 