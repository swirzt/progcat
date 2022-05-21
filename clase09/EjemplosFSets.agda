
module clase09.EjemplosFSets where

open import Categories.Iso
open import Categories.Sets
open import Categories.Products
open import Categories.Coproducts
open import Categories.Terminal
open import Categories.Initial
open import Functors
open import Functors.Constant
open import Library hiding (_×_)

open Products (SetsHasProducts {lzero})
open Coproducts (SetsHasCoproducts {lzero}) 
open Terminal OneSet
open Initial ZeroSet

open import Functors.Product (SetsHasProducts {lzero})
open import Functors.Coproduct (SetsHasCoproducts {lzero})

open import Data.Sum renaming (_⊎_ to _+_) hiding ([_,_])

--------------------------------------------------
{- Definir el siguiente funtor sobre Sets
 *usando suma y producto de functores*
 La idea es reusar lo que ya está definido.
 *No* definir functores usando el constructor de funtores.
  -}

-- Nat X = 1 + X
Nat : Fun Sets Sets
Nat = K ⊤ +F IdF

module Nat where

  open Fun Nat
  open import clase09.FAlgebraCat Nat
  open F-algebra
  open F-homomorphism
  open import Data.Nat using (ℕ ; suc ; zero)

  -- definir constructores
  0N : μF
  0N = α (inj₁ tt)

  sucN : μF → μF
  sucN x = α (inj₂ x)

--------------------------------------------------
{- Probar que los naturales, junto con foldℕ son el álgebra inicial de Nat -}

  foldℕ : ∀{A : Set} → (A → A) → A → ℕ → A
  foldℕ s z zero = z
  foldℕ s z (suc n) = s (foldℕ s z n)

  μNat : F-algebra
  μNat = falgebra ℕ [ λ- zero , suc ]

  init-homo-base : (k : F-algebra) → ℕ → carrier k 
  init-homo-base (falgebra carr alg) = foldℕ (λ x → alg (inj₂ x)) (alg (inj₁ tt))

  lema-init-homo-prop : {X : F-algebra} → (n : OMap ℕ) → (init-homo-base X ∘ algebra μNat) n ≅
                                       (algebra X ∘ HMap (init-homo-base X)) n
  lema-init-homo-prop (inj₁ x) = refl
  lema-init-homo-prop (inj₂ y) = refl

  init-homo-prop : (X : F-algebra) →
       init-homo-base X ∘ algebra μNat ≅  algebra X ∘ HMap (init-homo-base X)
  init-homo-prop X = ext (λ n → lema-init-homo-prop {X} n)
  
  init-homoℕ : {X : F-algebra} → F-homomorphism μNat X
  init-homoℕ {X} = homo (init-homo-base X) (init-homo-prop X) 

  univℕ : ∀{X : F-algebra} → {f : F-homomorphism μNat X}
       → (n : ℕ) →  init-homo-base X n ≅ homo-base f n
  univℕ {f = homo mor prop} zero = sym (cong (λ x → x (inj₁ tt)) prop)
  univℕ {X} {f = homo mor prop} (suc n) = proof -- Obviamente fui por las dos puntas, no fui de arriba para abajo :)
                                          init-homo-base X (suc n)
                                          ≅⟨ refl ⟩ -- Aplicando definición de foldN
                                          algebra X (inj₂ (init-homo-base X n))
                                          ≅⟨ cong (λ x → algebra X (inj₂ x)) (univℕ {X} {f = homo mor prop} n) ⟩ -- Paso recursivo
                                          algebra X (inj₂ (mor n))
                                          ≅⟨ refl ⟩ -- inj₂ (mor n) == HMap mor (inj₂ n)
                                          algebra X (HMap mor (inj₂ n))
                                          ≅⟨ sym (cong (λ x → x (inj₂ n)) prop) ⟩ -- Usando propiedad
                                          mor (algebra μNat (inj₂ n))
                                          ≅⟨ refl ⟩ -- Definición del algebra de μNat
                                          mor (suc n)
                                          ∎

  initial-ℕ : Initial F-AlgebraCat μNat
  initial-ℕ = init init-homoℕ (λ {X} {f} → homomorphismEq (ext (univℕ {X} {f})))

--------------------------------------------------
{- Definir un functor cuya algebra inicial sea las listas.
-}
-- List a = Nil | Cons a (List a)
L : (A : Set) → Fun (Sets {lzero}) (Sets {lzero})
L A = K ⊤ +F (K A ×F IdF)

module Listas (A : Set) where

  open Fun (L A)
  open import clase09.FAlgebraCat (L A)
  open F-homomorphism
  open F-algebra
  open import Data.Nat

  data List (A : Set) : Set where
     Nil : List A
     Cons : A → List A → List A

{-
   Definir constructores, y probar que
   efectivamente son listas (como hicimos con los naturales)
-}
  nil : μF
  nil = α (inj₁ tt)

  cons : A → μF → μF
  cons x xs = α (inj₂ (x , xs))

{-
  Definir la función length para listas
-}

  length : μF → ℕ
  length = fold (λ {(inj₁ x) → zero
                  ; (inj₂ (_ , y)) → suc y})

--------------------------------------------------
{- Probar que los las Listas junto con foldr son el
   álgebra inicial de L -}

  foldr : ∀{A X : Set} → (n : X) → (c : A → X → X) → List A → X
  foldr n c Nil = n
  foldr n c (Cons x xs) = c x (foldr n c xs)

  μList : F-algebra
  μList = falgebra (List A) [ λ- Nil , uncurry Cons ]

  init-homo-base : (k : F-algebra) → List A → carrier k 
  init-homo-base k = foldr (algebra k (inj₁ tt)) (λ x xs → algebra k (inj₂ (x , xs)))

  init-homo-prop : (X : F-algebra) →
       init-homo-base X ∘ algebra μList ≅  algebra X ∘ HMap (init-homo-base X)
  init-homo-prop X = ext (λ {(inj₁ x) → refl
                           ; (inj₂ y) → refl})

  init-homoList : {X : F-algebra} → F-homomorphism μList X
  init-homoList {X} = homo (init-homo-base X) (init-homo-prop X)

  univList : ∀{X : F-algebra} → {f : F-homomorphism μList X}
           → (xs : List A) → init-homo-base X xs ≅ homo-base f xs
  univList {X} {f = homo mor prop} Nil = proof
                                         init-homo-base X Nil
                                         ≅⟨ refl ⟩ -- def fold
                                         algebra X (inj₁ tt)
                                         ≅⟨ refl ⟩ -- HMap mor (inj₁ tt) = inj₁ tt
                                         algebra X (HMap mor (inj₁ tt))
                                         ≅⟨ cong (λ x → x (inj₁ tt)) (sym prop) ⟩ -- prop
                                         mor (algebra μList (inj₁ tt))
                                         ≅⟨ refl ⟩ -- def algebra μList
                                         mor Nil                                     
                                         ∎
  univList {X} {f = homo mor prop} (Cons x xs) = proof
                                                 init-homo-base X (Cons x xs)
                                                 ≅⟨ refl ⟩ -- def fold
                                                 algebra X (inj₂ (x , init-homo-base X xs))
                                                 ≅⟨ cong (λ y → algebra X (inj₂ (x , y))) (univList {X} {f = homo mor prop} xs) ⟩ -- recursivo
                                                 algebra X (inj₂ (x , mor xs))
                                                 ≅⟨ refl ⟩ -- HMap mor (inj₂ (x , xs)) = inj₂ (x , mor xs)
                                                 algebra X (HMap mor (inj₂ (x , xs)))
                                                 ≅⟨ cong (λ y → y (inj₂ (x , xs))) (sym prop) ⟩ -- prop
                                                 mor (algebra μList (inj₂ (x , xs)))
                                                 ≅⟨ refl ⟩ -- def algebra μList
                                                 mor (Cons x xs)
                                                 ∎

  initial-List : Initial (F-AlgebraCat) μList
  initial-List = init init-homoList (λ {X} {f} → homomorphismEq (ext (univList {X} {f})))
  