module Categories where

{- importamos extensionalidad, proof irrelevance -}
open import Library

open import Relation.Binary.PropositionalEquality  


--------------------------------------------------
{- Definición de Categoría -}
{-
 - Una colección de objetos  (denotado con Obj (C))
 - Conjuntos de flechas entre objetos (Sean A, B ∈ Obj(C) , hom (A, B))
 - todo objeto tiene una flecha identidad (id : A → A)
 - todo par de flechas "compatibles" puede componerse ( ∘ )
 - la composición es asociativa, con la flecha identidad como unidad. 
     (f ∘ g) ∘ h = f ∘ (g ∘ h)
     f ∘ id = id ∘ f = f 
-}


record Cat : Set₂ where
  infix 7 _∙_ 
  field Obj : Set₁
        Hom : Obj → Obj → Set
        iden : ∀ {X} → Hom X X
        _∙_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl : ∀ {X Y} {f : Hom X Y} → iden ∙ f ≡ f  
        idr : ∀ {X Y} {f : Hom X Y} → f ∙ iden ≡ f
        ass : ∀ {X Y Z W} {f : Hom Y Z} {g : Hom X Y}{h : Hom W X} →
              (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
        

--------------------------------------------------
{- El típico ejemplo de categoría es la categoría Set de conjuntos y
   funciones entre los mismos.
-}


Sets : Cat
Sets = record
         { Obj = Set
         ; Hom = λ X Y → X → Y  
         ; iden = id
         ; _∙_ = λ f g → f ∘ g  
         ; idl = refl
         ; idr = refl
         ; ass = refl
         } 


--------------------------------------------------
{- Para cada categoría existe la categoría dual, que consiste de los
mismos objetos, pero con las flechas invertidas.
   Cₒₚ :  
   Objetos : Obj (C) 
   Hom (X, Y) : Hom (Y, X) ∈ C   

-}

_Op : Cat → Cat
C Op =  let open Cat C in
        record
         { Obj = Obj
         ; Hom = λ X Y → Hom Y X 
         ; iden = iden
         ; _∙_ = λ f g → g ∙ f 
         ; idl = idr
         ; idr = idl
         ; ass = sym ass
         }  



--------------------------------------------------
{- Categoría Discreta

   Una categoría discreta es una categoría en la que los únicos
morfismos son identidades. La composición y ecuaciones de coherencia
son triviales.
-}


Discrete : Set₁ → Cat
Discrete X = record
               { Obj = X
               ; Hom = λ _ _ → ⊤ 
               ; iden = tt  
               ; _∙_ = λ _ _ → tt
               ; idl = refl
               ; idr = refl
               ; ass = refl
               } 



{- A menudo nos queremos "olvidar" de los morfismos de una
categoría. Es decir, miramos a la categoría como una categoría
discreta. Esto se nota en lenguaje categórico como |C| -}

∣_∣ : Cat → Cat
∣ C ∣ = Discrete (Cat.Obj C)

--------------------------------------------------
{- Categoría Producto -}
{- Dadas dos categorías, podemos formar la categoría producto 
   Los objetos son el producto cartesiano de los objetos
   Los morfismos son pares de flechas.


  Obj (C × D) = Obj (C) × Obj(D)
  
         (X , Y) ∈ Obj (C × D) donde X ∈ Obj (C) ∧ y ∈ Obj (D) 

  Hom ((X, Y), (X', Y')) = Hom (X, X') × Hom (Y , Y')

         f : X → X' ∈ Hom (X, X') ∧ g : Y → Y' ∈ Hom (Y, Y') ⇒ (f, g) ∈ Hom ((X, Y), (X', Y'))   

  (f , g) ∘ (f' , g') = (f ∘ f' ,  g ∘ g')
 
  id = (id , id)

-}

_×C_ : Cat → Cat → Cat
C ×C D = record
           { Obj = Obj₁ × Obj₂
           ; Hom = λ {(X , Y) (X' , Y') → Hom₁ X X' × Hom₂ Y Y' }
           ; iden = (iden₁ , iden₂)
           ; _∙_ = λ {(f , g) (f' , g') → f ∙₁ f' , (g ∙₂ g')} 
           ; idl = cong₂ _,_ idl₁ idl₂
           ; idr = cong₂ _,_ idr₁ idr₂
           ; ass = cong₂ _,_ ass₁ ass₂
           } 
           where open Cat C renaming (Obj to Obj₁ ; Hom to Hom₁ ; iden to iden₁ ; _∙_ to _∙₁_ ; idl to idl₁ ; idr to idr₁ ; ass to ass₁)
                 open Cat D renaming (Obj to Obj₂ ; Hom to Hom₂ ; iden to iden₂ ; _∙_ to _∙₂_ ; idl to idl₂ ; idr to idr₂ ; ass to ass₂)  
          


--------------------------------------------------
{- Familia de Conjuntos -}
{- Los objetos son familias de conjuntos
   (conjuntos indexados por un conjunto de índices)

  Los morfismos son funciones que preservan el índice.
 
  Objetos:  {Aᵢ} i ∈ I
  Flechas : Aᵢ → Bᵢ    
-}

Fam : Set → Cat
Fam I = record
          { Obj = I → Set
          ; Hom = λ A B → ∀ {i} → A i → B i  
          ; iden = id
          ; _∙_ = λ f g → f ∘ g  
          ; idl = refl
          ; idr = refl
          ; ass = refl
          } 


--------------------------------------------------
{- Ejemplo extendido: Categorías Slice -}

{- Dada una categoría C, los objetos de un slice
   sobre un objeto I, son morfismos con codominio I
-}


module Slice (C : Cat) where 

  open Cat C

  record Slice₀ (I : Obj) : Set₁ where
    constructor _,_
    field
     base : Obj
     homBase : Hom base I
     
  open Slice₀

  {- record para representar los morfismos de la categoría -}
  record Slice₁ (I : Obj) (X Y : Slice₀ I) : Set where 
    constructor _,_
    field
       baseHom : Hom (base X) (base Y)  -- h  
       prop : (homBase Y) ∙ baseHom ≡ homBase X   -- g ∙ h = f

  {- la composición es simplemente pegar triángulos -}
  Slice-comp :  {I : Obj} {X Y Z : Slice₀ I} →
                Slice₁ I Y Z → Slice₁ I X Y → Slice₁ I X Z
  Slice-comp {I} {X , f} {Y , g} {Z , i} (h , p) (h' , q) =
    ( h ∙ h') , (proof  i ∙ (h ∙ h')
                         ≡⟨ sym ass ⟩
                         (i ∙ h) ∙ h'
                         ≡⟨ cong (λ j → j ∙ h') p ⟩
                         g ∙ h'
                         ≡⟨ q ⟩
                         f
                         ∎ )
  
  open Slice₁

  {- veamos como funciona proof irrelevance -}
  Slice₁-eq : {I : Obj} {X Y : Slice₀ I} {h h' : Slice₁ I X Y} →
              (baseHom h) ≡ (baseHom h')  →
              h ≡ h'
  Slice₁-eq {I} {X , f} {Y , g} {h , p} {.h , q} refl = cong (λ p → (h , p)) (ir p q)
 

  Slice : (I : Obj) → Cat
  Slice I = record
              { Obj = Slice₀ I
              ; Hom = Slice₁ I 
              ; iden = iden , idr
              ; _∙_ = Slice-comp  
              ; idl = Slice₁-eq idl
              ; idr = Slice₁-eq idr
              ; ass = Slice₁-eq ass
              }
 
 
--------------------------------------------------

{- Ejercicio: Definir la categoría con un sólo objeto ⊤, y que sus
morfismos son los elementos de un monoide M -}

module CatMon where

 open import Records-completo hiding (Iso ; ⊤)

 CatMon : Monoid → Cat
 CatMon M = record
   { Obj = Lift (lsuc lzero) ⊤
   ; Hom = λ _ _ → Carrier
   ; iden = ε
   ; _∙_ = _∙_
   ; idl = lid
   ; idr = rid
   ; ass = assoc
   }
   where open Monoid M


--------------------------------------------------
{- Ejercicio: Definir la categoría en que los objetos son monoides,
  y las flechas son homomorfismos de monoides
-}

module MonCat where

 open import Records-completo hiding (Iso)

 open Is-Monoid-Homo


 MonCat : Cat
 MonCat = record
   { Obj = Monoid
   ; Hom = λ M N → Carrier M → Carrier N
   ; iden = id
   ; _∙_ = λ g f x → g (f x)
   ; idl = refl
   ; idr = refl
   ; ass = refl
   }
   where open Monoid
--------------------------------------------------
{- Ejercicio: Dada un categoría C, definir la siguiente categoría:
  - Los objetos son morfismos de C
  - Un morfismo entre una flecha f: A → B y f': A'→ B' es un par de morfismos de C
      g1 : A → A', y g2 : B → B', tal que
                    f' ∙ g₁ ≡ g₂ ∙ f
-}

module ArrowCat (C : Cat) where

 open Cat C 


 record Arrow₀ : Set₁ where
   constructor _,_,_
   field
     from : Obj
     to : Obj
     homFT : Hom from to
 open Arrow₀

 record Arrow₁ (f g : Arrow₀) : Set where
   constructor _,_
   field
     hom : Hom (from f) (from g) × Hom (to f) (to g)
     prop : (homFT g) ∙ (fst hom) ≡ (snd hom) ∙ (homFT f)
 open Arrow₁

 ArrowOp : {X Y Z : Arrow₀} → Arrow₁ Y Z → Arrow₁ X Y → Arrow₁ X Z
 ArrowOp {X} {Y} {Z} (hom , prop) (hom₁ , prop₁) = (((fst hom) ∙ (fst hom₁)) , ((snd hom) ∙ (snd hom₁))) , (proof 
                                                                                                homFT Z ∙ (fst hom ∙ fst hom₁)
                                                                                                ≡⟨ sym ass ⟩
                                                                                                (homFT Z ∙ fst hom) ∙ fst hom₁
                                                                                                ≡⟨ cong (λ x → x ∙ fst hom₁) prop ⟩
                                                                                                (snd hom ∙ homFT Y) ∙ fst hom₁
                                                                                                ≡⟨ ass ⟩
                                                                                                snd hom ∙ (homFT Y ∙ fst hom₁)
                                                                                                ≡⟨ cong (λ x → snd hom ∙ x) prop₁ ⟩
                                                                                                snd hom ∙ (snd hom₁ ∙ homFT X)
                                                                                                ≡⟨ sym ass ⟩
                                                                                                (snd hom ∙ snd hom₁) ∙ homFT X
                                                                                                ∎)

 Arrow₁-eq : {X Y : Arrow₀} {h h' : Arrow₁ X Y} → (hom h) ≡ (hom h') → h ≡ h'
 Arrow₁-eq {X} {Y} {f , prop₁} {.f , prop₂} refl = cong (λ x → (f , x)) (ir prop₁ prop₂)

 ArrowCat : Cat
 ArrowCat = record
   { Obj = Arrow₀
   ; Hom = Arrow₁
   ; iden = (iden , iden) , trans idr (sym idl)
   ; _∙_ = ArrowOp
   ; idl = Arrow₁-eq (cong₂ _,_ idl idl)
   ; idr = Arrow₁-eq (cong₂ _,_ idr idr)
   ; ass = Arrow₁-eq (cong₂ _,_ ass ass)
   }
 
--------------------------------------------------
{- Generalizamos la noción de isomorfismo de la clase pasada a cualquier categoría -}

{- Isomorfismo en una categoría -}

open Cat

record Iso {C : Cat}(A B : Obj C)(fun : Hom C A B) : Set where
  constructor iso
  field inv : Hom C B A
        law1 : _∙_ C fun inv  ≡ iden C {B}
        law2 : _∙_ C inv fun  ≡ iden C {A}

--------------------------------------------------

{- Ejercicio
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}
open import Records-completo renaming (Iso to IsoSet ; ext to ext2) 

isoc-biyeccion : {A B : Obj Sets} → (f : Hom Sets A B) → Iso {Sets} A B f → Biyectiva f 
isoc-biyeccion f (iso inv law1 law2) = λ y → (inv y) , ((cong-app law1 y) , (λ x' eq → proof
                                                                                       inv y
                                                                                       ≡⟨ sym (cong inv eq) ⟩
                                                                                       inv (f x')
                                                                                       ≡⟨ cong-app law2 x' ⟩
                                                                                       x'
                                                                                       ∎))

byeccion-isoc : {A B : Obj Sets} → (f : Hom Sets A B) → Biyectiva f → Iso {Sets} A B f
byeccion-isoc f biy = iso (λ x → fst (biy x))
                          (ext (λ b → let (x , p , _) = biy b in
                                      proof
                                      f x
                                      ≡⟨ p ⟩
                                      b
                                      ∎))
                          (ext (λ a → let (x , _ , u) = biy (f a) in
                                      proof
                                      x
                                      ≡⟨ u a refl ⟩
                                      a
                                      ∎))
--------------------------------------------------
{- Ejercicio:
 Probar que un isormofismo en (C : Cat) es un isomorfismo en (C Op).
-}
isoOp : {C : Cat}{A B : Obj C}{f : Hom C A B} → Iso {C} A B f → Iso {C Op} B A f
isoOp (iso inv law1 law2) = iso inv law2 law1

--------------------------------------------------
{- Ejercicio EXTRA:
 Definir la categoría de pointed sets:
  - objetos son conjuntos junto con un elemento designado del conjunto.
     Por ejemplo (Bool , false), (ℕ , 0) , etc.
  - los morfismos son funciones entre los conjuntos que preservan el punto
     (A,a) → (B, b) es una función f : A → B, tal que f(a) = b 
-}

record Point : Set₁ where
  constructor point
  field S : Set
        x : S
open Point

record PointHom (A B : Point) : Set where
  constructor pointHom
  field fun : S A → S B
        prop : fun (x A) ≡ x B
open PointHom

point-prod : {X Y Z : Point} → PointHom Y Z → PointHom X Y → PointHom X Z
point-prod {X} {Y} {Z} (pointHom f2 prop2) (pointHom f1 prop1) = pointHom (λ x → f2 (f1 x))
                                                                          (proof
                                                                           f2 (f1 (x X))
                                                                           ≡⟨ cong (λ v → f2 v) prop1 ⟩
                                                                           f2 (x Y)
                                                                           ≡⟨ prop2 ⟩
                                                                           x Z
                                                                           ∎)

point-eq : {X Y : Point} {f g : PointHom X Y} → fun f ≡ fun g → f ≡ g
point-eq {X} {Y} {pointHom fun₁ prop₁} {pointHom .fun₁ prop₂} refl = cong (λ x → pointHom fun₁ x) (ir prop₁ prop₂)

demidl : {X Y : Point} {f : PointHom X Y} → point-prod (pointHom id refl) f ≡ f
demidl {X} {Y} {pointHom fun prop} = proof
                                      pointHom fun (trans (cong (λ z → z) prop) refl)
                                      ≡⟨ cong (λ x → pointHom fun x) (trans-reflʳ (cong id prop)) ⟩
                                      pointHom fun (cong (λ z → z) prop)
                                      ≡⟨ cong (λ x → pointHom fun x) (cong-id prop) ⟩
                                      pointHom fun prop
                                      ∎

demidr : {X Y : Point} {f : PointHom X Y} → point-prod f (pointHom id refl) ≡ f
demidr {X} {Y} {pointHom fun prop} = proof
                                      pointHom fun (trans prop refl)
                                      ≡⟨ cong (λ x → pointHom fun x) (trans-reflʳ prop) ⟩
                                      pointHom fun prop
                                      ∎

-- La hice con pattern matching porque si no era muy larga
demass : {X Y Z W : Point} {f : PointHom Y Z} {g : PointHom X Y} {h : PointHom W X} → point-prod (point-prod f g) h ≡ point-prod f (point-prod g h)
demass {point _ .(fun1 x)} {point _ .(fun2 (fun1 x))} {point _ .(fun3 (fun2 (fun1 x)))} {point _ x} {pointHom fun3 refl} {pointHom fun2 refl} {pointHom fun1 refl} = refl

PointedCat : Cat
PointedCat = record
              { Obj = Point
              ; Hom = PointHom
              ; iden = pointHom id refl
              ; _∙_ = point-prod
              ; idl = demidl
              ; idr = demidr
              ; ass = λ {X} {Y} {Z} {W} {f} {g} {h} → demass {X} {Y} {Z} {W} {f} {g} {h}
              }
                    

--------------------------------------------------

{- Ejercicio EXTRA:
 Definir la categoría cuyos
  - objetos son conjuntos finitos (y por lo tanto isomorfos a Fin n para algún n)
  - morfismos son isomorfismos.  
-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

record FiniteSet : Set₁ where
  constructor finiteSet
  field S : Set
        n : ℕ
        f : S → Fin n
        isoFin : IsoSet S (Fin n) f
open FiniteSet

record FiniteSetHom (A B : FiniteSet) : Set where
  constructor finiteSetHom
  field fun : S A → S B
        isoprop : IsoSet (S A) (S B) fun
open FiniteSetHom
open IsoSet

finite-prod : {A B C : FiniteSet} → FiniteSetHom B C → FiniteSetHom A B → FiniteSetHom A C
finite-prod {A} {B} {C} h2 h1 = finiteSetHom (λ x → fun h2 (fun h1 x)) (iso (λ x → inv (isoprop h1) (inv (isoprop h2) x)) funinv invfun)
                                where 
                                      funinv : (b : S C) → fun h2 (fun h1 (inv (isoprop h1) (inv (isoprop h2) b))) ≡ b
                                      funinv b = proof 
                                                 fun h2 (fun h1 (inv (isoprop h1) (inv (isoprop h2) b)))                 
                                                 ≡⟨ cong (λ x → fun h2 x) (law1 (isoprop h1) (inv (isoprop h2) b)) ⟩
                                                 fun h2 (inv (isoprop h2) b)
                                                 ≡⟨ law1 (isoprop h2) b ⟩
                                                 b
                                                 ∎
                                      invfun : (a : S A) → inv (isoprop h1) (inv (isoprop h2) (fun h2 (fun h1 a))) ≡ a
                                      invfun a = proof 
                                                 inv (isoprop h1) (inv (isoprop h2) (fun h2 (fun h1 a)))
                                                 ≡⟨ cong (λ x → inv (isoprop h1) x) (law2 (isoprop h2) (fun h1 a)) ⟩
                                                 inv (isoprop h1) (fun h1 a)
                                                 ≡⟨ law2 (isoprop h1) a ⟩
                                                 a
                                                 ∎

sameinv : {X Y : Set} {f : X → Y} → (A B : IsoSet X Y f) → inv A ≡ inv B → A ≡ B
sameinv (iso inv₁ law3 law4) (iso .inv₁ law5 law6) refl = cong₂ (λ x y → iso inv₁ x y) (ext (λ b → ir (law3 b) (law5 b))) (ext (λ a → ir (law4 a) (law6 a)))

kk = cong-app

sameiso : {X Y : Set} {f : X → Y} → (A B : IsoSet X Y f) → inv A ≡ inv B
sameiso {X} {Y} {f} A B = ext (λ a → proof 
                                     inv A a
                                     ≡⟨ sym (law2 A {!   !}) ⟩
                                     {!   !}
                                     ≡⟨ {!   !} ⟩
                                     {!   !}
                                     ≡⟨ {!   !} ⟩
                                     {!   !}
                                     ≡⟨ {!   !} ⟩
                                     inv B a
                                     ∎)

finite-eq : {A B : FiniteSet} {f g : FiniteSetHom A B} → fun f ≡ fun g → f ≡ g
finite-eq {A} {B} {finiteSetHom fun₁ isoprop₁} {finiteSetHom .fun₁ isoprop₂} refl = {!   !}

-- -- Se complicó mucho, algo hice mal

FiniteCat : Cat
FiniteCat = record
  { Obj = FiniteSet
  ; Hom = FiniteSetHom
  ; iden = finiteSetHom id (iso id (λ b → refl) (λ a → refl))
  ; _∙_ = finite-prod
  ; idl = finite-eq refl
  ; idr = finite-eq refl
  ; ass = finite-eq refl
  }

--------------------------------------------------


 