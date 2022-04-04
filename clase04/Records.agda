
module Records where

open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional as Ext

-- postulamos extensionalidad
postulate ext : ∀{a b} → Ext.Extensionality a b

{- Veremos, el uso de records para definir estructuras algebraicas -}


-- MONOIDES

{- Notar el uso de de Set₁ en lugar de Set ya que tenemos que
 situarnos en el nivel siguiente a Set₀ = Set, para hablar de cosas en
 Set (como carrier).

Los subindices son ₀ = \_0 y ₁ = \_1
 -}

record Monoid : Set₁  where
  infixr 7 _∙_
  -- constructor monoid
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier  {- ∙ = \. -}
         ε       : Carrier   {- ε = \epsilon -}
         lid     : {x : Carrier} → ε ∙ x ≡ x
         rid     : {x : Carrier} → x ∙ ε ≡ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z) 

{- ¿Qué sucede si queremos usar un Carrier en Set₁? ¿o en Set₂? -}

{- Al escribir las ecuaciones estamos tomando una decisión sobre la noción de igualdad 
 En esta definición elegimos la igualdad proposicional
-}

open import Data.Nat
open import Data.Nat.Properties using (+-identityʳ ; +-assoc ; *-distribʳ-+)

-- Monoide de Naturales y suma

module NatMonoid where


  NatMonoid : Monoid
  NatMonoid = record
    { Carrier = ℕ 
    ; _∙_ = _+_ 
    ; ε = 0 
    ; lid = refl 
    ; rid = λ {x} → +-identityʳ x ; 
    assoc = λ {x} {y} {z} → +-assoc x y z }

open NatMonoid


--------------------------------------------------
{- Ejercicio: Probar que las listas son un monoide -}

open ≡-Reasoning


infixr 5 _∷_
infixr 4 _++_

{- \:: -}

data List (A : Set) : Set where
      [] : List A
      _∷_ : (x : A) → (xs : List A) → List A

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
x ∷ xs ++ ys = x ∷ (xs ++ ys)

ListMonoid : Set → Monoid
ListMonoid X = record
    { Carrier = List X 
    ; _∙_ = _++_ 
    ; ε = [] 
    ; lid = refl 
    ; rid = demrid 
    ; assoc = λ {x} {y} {z} → demassoc {X} {x} {y} {z} }
    where demrid : {X : Set} → {l : List X} → (l ++ []) ≡ l
          demrid {l = []} = refl
          demrid {l = x ∷ xs} = cong (λ y → x ∷ y) demrid
          demassoc : {X : Set} → {x y z : List X} → ((x ++ y) ++ z) ≡ (x ++ y ++ z)
          demassoc {x = []} {y} {z} = refl
          demassoc {x = x ∷ xs} {y} {z} = cong (λ w → x ∷ w) (demassoc {x = xs})


--------------------------------------------------

{- Ejercicio: Probar que para todo monoide M, N, el producto
   cartesiano de los respectivos soportes (Carrier M × Carrier N)
   es  el soporte de un monoide

 Ayuda : puede ser útil cong₂
-}
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)

f = cong₂
ProductMonoid : Monoid → Monoid → Monoid
ProductMonoid M N = record
  { Carrier = Carrier₁ × Carrier₂ ;
    _∙_ = λ x y → ((fst x) ∙₁ (fst y)) , ((snd x) ∙₂ (snd y)) ;
    ε = ε₁ , ε₂ ;
    lid = cong₂ (_,_) lid₁ lid₂ ;
    rid = cong₂ _,_ rid₁ rid₂ ;
    assoc = cong₂ _,_ assoc₁ assoc₂ }
    where open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_; lid to lid₁; rid to rid₁; assoc to assoc₁; Carrier to Carrier₁)
          open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_; lid to lid₂; rid to rid₂; assoc to assoc₂; Carrier to Carrier₂)

--------------------------------------------------
open import Function

-- Monoide de endofunciones
EndoMonoid : Set → Monoid
EndoMonoid X = record
                 { Carrier = X → X
                 ; _∙_ = _∘′_
                 ; ε = id
                 ; lid = refl
                 ; rid = refl
                 ; assoc = refl }


module Cayley where

  open Monoid using (Carrier)

  Cayley : Monoid → Monoid
  Cayley M = EndoMonoid (Carrier M) 

  rep : (M : Monoid) → Carrier M → Carrier (Cayley M)
  rep M x = λ y → x ∙ y
           where open Monoid M

  abs : (M : Monoid) → Carrier (Cayley M) → Carrier M
  abs M f = f ε
           where open Monoid M

  lemma : (M : Monoid) → {x : Carrier M} →
          abs M (rep M x) ≡ x
  lemma M = rid
           where open Monoid M

module Monoid-Homomorphism where
 open Monoid

-- Homomorfismos de monoides
 record Is-Monoid-Homo (M N : Monoid)(morph : Carrier M → Carrier N) : Set₁ where
   open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_)
   open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_)
   field
    preserves-unit : morph ε₁ ≡ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≡ morph x ∙₂ morph y 

open Monoid-Homomorphism
open Cayley

rep-is-monoid-homo : {M : Monoid} → Is-Monoid-Homo M (Cayley M) (rep M)
rep-is-monoid-homo {M} = record {
                         preserves-unit = ext (λ x → lid)
                       ; preserves-mult = ext (λ x → assoc) }
                  where open Monoid M

--------------------------------------------------
{- Ejercicio: Probar que length es un homorfismo de monoides -}


length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

length-is-monoid-homo : {X : Set} → Is-Monoid-Homo (ListMonoid X) NatMonoid length
length-is-monoid-homo {X} = record {
                              preserves-unit = refl ;
                              preserves-mult = λ {x} {y} → dem {x} {y} }
                               where dem : {x y : List X} → length (x ++ y) ≡ length x + length y
                                     dem {[]} = refl
                                     dem {x ∷ xs} {y} = cong suc (dem {x = xs})
                          
--------------------------------------------------
{- Ejercicio: Probar que multiplicar por una constante es un es un homorfismo de NatMonoid -}

multcont-is-monoid-homo : {n : ℕ} → Is-Monoid-Homo NatMonoid NatMonoid (λ x → x * n)
multcont-is-monoid-homo {n} = record {
                                preserves-unit = refl ;
                                preserves-mult = λ {x} {y} → *-distribʳ-+ x {! y  !} {! n  !} }
                                  where dem : {x y : ℕ} → (x + y) * n ≡ x * n + y * n
                                        dem {zero} = refl
                                        dem {suc x} = begin 
                                                      {! c  !}
                                                      ≡⟨ {!   !} ⟩
                                                      {!   !}
                                                      ∎



--------------------------------------------------
module Foldr (M : Monoid) where

 open Monoid M

 {- Ejercicio : Definir foldr y probar que (foldr _∙_ ε) es un homorfismo de monoides -}

{-
 foldr : {A B : Set} → (A → B → B) → B → List A → B
 foldr _⊗_ e xs = {!   !}
-}
--------------------------------------------------

{- Isomorfismos entre conjuntos -}

record Iso (A : Set)(B : Set) : Set where
  field fun : A → B
        inv : B → A
        law1 : ∀ b → fun (inv b) ≡ b
        law2 : ∀ a → inv (fun a) ≡ a

open Iso

-----------------------------

{- Ejercicio : introducir un tipo de datos (record) ⊤ con un único habitante y
probar que  ℕ es isomorfo a List ⊤ -}


{- Ejercicio: introducir un constructor de tipos Maybe (o usar Data.Maybe) y probar que
Maybe ℕ es isomorfo a ℕ -}

{- Ejercicio: introducir un constructor de tipos _×_ para productos
cartesianos (o usar el de Data.Product) y probar que (A → B × C) es
isomorfo a (A → B) × (A → C) para todos A, B, y C, habitantes de Set -}


{- Ejercicio: construir isomorfismos entre Vec A n × Vec B n y
Vec (A × B) n para todos A, B habitantes de Set y n natural -}

open import Data.Vec


--------------------------------------------------
{- Ejercicio Extra
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

Biyectiva : {X Y : Set}(f : X → Y) → Set
Biyectiva {X} {Y} f = (y : Y) → Σ X (λ x → (f x ≡ y) × (∀ x' → f x' ≡ y → x ≡ x')) 
 