-- Tipos de datos regulares

module clase10.Regular where 

open import Data.Empty   -- tipo vacío
open import Data.Unit    -- tipo con un elemento
open import Data.Sum     -- unión disjunta de tipos
  hiding (map)
open import Data.Product -- Producto de dos tipos
  hiding (map)
open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)


-- Universo para los tipos de datos Regulares
{-
 Símbolos : \o+ ⊕ , \ox  ⊗ , \u+ ⊎ , \[[ \]]  ⟦ ⟧      
-} 

-- F := K A | Π₁ | F × F | F + F | Π₂

data Regular : Set₁ where
  U   : Regular                          -- Tipo con un sólo elemento
  K   : (A : Set) → Regular             -- Tipos constante (Ej, ℕ , Float)
  P   : Regular                          -- Parámentro del tipo
  _⊗_ : Regular → Regular → Regular    -- Producto de dos tipos
  _⊕_ : Regular → Regular → Regular    -- Union disjunta
  I   : Regular                          -- Para tipos recursivos (Posición recursiva)
 

-- Función de interpretación indexada por
-- * Functor regular
-- * Parámetro de tipo
-- * Posición recursiva

⟦_⟧ᵣ : Regular → Set → Set → Set
⟦ U ⟧ᵣ p r = ⊤
⟦ K A ⟧ᵣ p r = A
⟦ P ⟧ᵣ p r = p
⟦ F ⊗ G ⟧ᵣ p r = ⟦ F ⟧ᵣ p r × ⟦ G ⟧ᵣ p r
⟦ F ⊕ G ⟧ᵣ p r = ⟦ F ⟧ᵣ p r ⊎ ⟦ G ⟧ᵣ p r
⟦ I ⟧ᵣ p r = r


-- Usamos dos funciones para convertir Booleanos a su representación
-- como tipo regular y al revés.
-- Vimos que Bool = 1 + 1

BoolF : Regular
BoolF = U ⊕ U


toBool : ∀ {p r} →  ⟦ BoolF ⟧ᵣ p r → Bool
toBool (inj₁ tt) = true
toBool (inj₂ tt) = false

fromBool : ∀ {p r} → Bool → ⟦ BoolF ⟧ᵣ p r
fromBool false = inj₁ tt
fromBool true = inj₂ tt

-- ¿Podremos hacer los mismo con listas? 
open import Data.List hiding (map ; sum)

-- List A = 1 + A × List A
-- List A B = 1 + A × B
-- List = 1 + P × I

-- No podemos definirlo, falta modelar recursión
-- toList' : ∀ {r} {A} → ⟦ U ⊕ (P ⊗ I) ⟧ᵣ A r → List A 
-- toList' (inj₁ x) = []
-- toList' (inj₂ (x , xs)) = x ∷ {!   !} 



-- Necesitamos un operador de punto fijo que compute
-- el punto fijo de la signatura del tipo de datos. 
-- X ≡ F X

data μ (F : Regular) (p : Set) : Set where
  ⟨_⟩ : ⟦ F ⟧ᵣ p (μ F p) → μ F p

-- Functor que captura la signatura de listas
ListF : Regular
ListF = U ⊕ (P ⊗ I)

-- Listas representadas como el punto fijo de su signatura
LIST : Set → Set
LIST A = μ ListF A 

-- Constructores
NIL : ∀ {A} → LIST A
NIL = ⟨ inj₁ tt ⟩

CONS : ∀ {A} → A → LIST A → LIST A
CONS x xs = ⟨ inj₂ (x , xs) ⟩

-- isomorfismo entre List A y LIST A
toList : ∀ {A} → LIST A → List A
toList ⟨ inj₁ x ⟩ = []
toList ⟨ inj₂ (x , xs) ⟩ = x ∷ toList xs 

fromList :  ∀ {A} → List A → LIST A  
fromList [] = ⟨ inj₁ tt ⟩
fromList (x ∷ xs) = ⟨ inj₂ ( x , fromList xs) ⟩

-- Probamos que forman un isomorfismo (útil para tener distintas vistas del mismo tipo) 

record Iso (A B : Set)(f : A → B) : Set  
  where
  constructor iso
  field inv  : B → A
        rinv : ∀ {x : B} → f (inv x) ≡ x
        linv : ∀ {x : A} → inv (f x) ≡ x

open Iso

-- Completar
iso1 : ∀ {A}{x} → toList {A} (fromList {A} x) ≡ x
iso1 {_} {[]} = refl
iso1 {_} {x ∷ xs} = cong (x ∷_) iso1  

iso2 : ∀ {A}{x} → fromList {A} (toList {A} x) ≡ x
iso2 {_} {⟨ inj₁ x ⟩} = refl
iso2 {_} {⟨ inj₂ y ⟩} = cong (λ x → ⟨ inj₂ (proj₁ y , x) ⟩) iso2 

listIso : ∀ {A : Set} → Iso (LIST A) (List A) (toList {A})
listIso = iso fromList iso1 iso2 


-- Definición genérica de map para los tipos de datos regulares

map : ∀ {A B C D} → (F : Regular) → (A → B) → (C → D) → ⟦ F ⟧ᵣ A C → ⟦ F ⟧ᵣ B D
map U f g tt = tt
map (K A) f g d = d
map P f g d = f d 
map (F ⊗ G) f g d = map F f g (proj₁ d) , map G f g (proj₂ d) 
map (F ⊕ G) f g (inj₁ x) = inj₁ (map F f g x)
map (F ⊕ G) f g (inj₂ x) = inj₂ (map G f g x)
map I f g d = g d 

-- Definición de fold 
-- fold (h) . inF = h . F fold (h)

-- La siguiente definición no pasa 'termination checking' 
-- Agda espera un valor estructuralmente más pequeño

-- fold : ∀ {F A P} → (⟦ F ⟧ᵣ P A → A) → μ F P → A
-- fold {F} alg ⟨ x ⟩ = alg (map F id (fold {F} alg) x)

-- Solución: fusionar map y fold

-- mapFold F G alg x = map F (fold G alg) x 

mapFold : ∀ {A P} (F G : Regular) → (⟦ G ⟧ᵣ P A → A) → ⟦ F ⟧ᵣ P (μ G P) → ⟦ F ⟧ᵣ P A
mapFold U G alg tt = tt
mapFold (K A) G alg x = x
mapFold P G alg x = x 
mapFold (F ⊗ F₁) G alg (x , y) = mapFold F G alg x , mapFold F₁ G alg y
mapFold (F ⊕ F₁) G alg (inj₁ x) = inj₁ (mapFold F G alg x)
mapFold (F ⊕ F₁) G alg (inj₂ x) = inj₂ (mapFold F₁ G alg x)
mapFold I G alg ⟨ x ⟩ = alg (mapFold G G alg x) 


fold : ∀ {F A P} → (⟦ F ⟧ᵣ P A → A) → μ F P → A
fold {F} alg x  = mapFold I F alg x 


-- Veamos cómo usar fold


Algebra : Regular → Set → Set → Set
Algebra F p A =  ⟦ F ⟧ᵣ p A → A


-- Calcula la cantidad de elementos de una estructura
elements : ∀ {F : Regular} {A : Set} → μ F A  → ℕ
elements {F} {A} = fold {F} (alg {F}) 
     where alg : ∀ {F' : Regular} → Algebra F' A ℕ
           alg {U} x = 0
           alg {K A} x = 0
           alg {P} x = 1
           alg {F' ⊗ F''} (x , y) = alg {F'} x + alg {F''} y
           alg {F' ⊕ F''} (inj₁ x) = alg {F'} x
           alg {F' ⊕ F''} (inj₂ y) = alg {F''} y
           alg {I} x = x
       


sl : ℕ
sl = elements (fromList (2 ∷ 4 ∷ 5 ∷ [])) 


-- Derivamos la definición de foldL a partir de fold
foldL : ∀ {A B} → B → (A × B → B) → List A → B
foldL {A} n c xs = fold ([_,_] (λ _ → n) c) (fromList xs) 



-- Ejemplos
n : ℕ
n = foldL 0 (uncurry _+_) (1 ∷ 2 ∷ [])


-- Ejercicio 1) Completar las siguientes definiciones

open import Data.Tree.Binary hiding (map)

-- Functor que captura la estructura de los árboles binarios
TreeF : Regular
TreeF = U ⊕ (I ⊗ (P ⊗ I)) 

-- Árboles representados como el punto fijo de su signatura

TREE : Set → Set
TREE A = μ TreeF A

-- Isomorfismo entre Tree A y TREE A
toTree : ∀ {A} → TREE A → Tree A
toTree ⟨ inj₁ tt ⟩ = leaf
toTree ⟨ inj₂ (l , x , r) ⟩ = node (toTree l) x (toTree r)

fromTree : ∀ {A} → Tree A → TREE A 
fromTree leaf = ⟨ inj₁ tt ⟩
fromTree (node l x r) = ⟨ inj₂ (fromTree l , x , fromTree r) ⟩ 

-- Definir foldT en términos de foldT
foldT : ∀ {a} {A B : Set a} → B → (B × (A × B) → B) → Tree A → B
foldT l n leaf = l
foldT l n (node t x t₁) = n (foldT l n t , x , foldT l n t₁) 


-- Ejercicio 2) Definir una función genérica depth, que calcule la profundidad de un
-- dato dado, es decir la cantidad de llamadas recursivas.


id : ∀ {A : Set} → A → A
id x = x

depth : ∀ {F : Regular} {A : Set} → μ F A → ℕ
depth {F} {A} = fold {F} (alg {F}) 
   where alg : ∀ {F'} → Algebra F' A ℕ
         alg {U} x = 1
         alg {K A} x = 1
         alg {P} x = 1
         alg {F' ⊗ F''} (x , y) = alg {F'} x ⊔ alg {F''} y
         alg {F' ⊕ F''} (inj₁ x) = alg {F'} x
         alg {F' ⊕ F''} (inj₂ y) = alg {F''} y
         alg {I} x = suc x 


-- función que calcula la altura de un árbol
height : ∀ {A} → Tree A → ℕ
height t = pred (depth (fromTree t))  

test : ℕ
test = height (node leaf (1 ∷ 2 ∷ 3 ∷ []) leaf)

test2 : ℕ
test2 = elements (fromTree (node (node leaf (1 ∷ 2 ∷ 3 ∷ []) leaf) (1 ∷ 2 ∷ 3 ∷ []) leaf))

-- Ejercicio 3)
-- Definir una función sum genérica que sume los números naturales almacenados
-- en una estructura de naturales. 

sum : ∀ {F : Regular} → μ F ℕ  → ℕ
sum {F} = fold {F} (alg {F})
          where alg : ∀ {F' : Regular} → Algebra F' ℕ ℕ
                alg {U} x = 0
                alg {K A} x = 0
                alg {P} x = x
                alg {F' ⊗ F''} (x , y) = alg {F'} x + alg {F''} y
                alg {F' ⊕ F''} (inj₁ x) = alg {F'} x
                alg {F' ⊕ F''} (inj₂ y) = alg {F''} y
                alg {I} x = x


test3 : ℕ
test3 = sum (fromList (1 ∷ 2 ∷ 3 ∷ []))

test4 : ℕ
test4 = sum (fromTree (node (node (leaf) 1 (leaf)) 2 (node (leaf) 3 (leaf))))