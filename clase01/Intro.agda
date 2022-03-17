{- 

    Introducción a la Programación con Tipos Dependientes
      
           Mauro Jaskelioff

 basado en día1 del curso de Thorsten Altenkirch en Rosario, 2011.


-}

module Intro where


{- Empezamos con programación en Agda desde cero. -}

{- Agda tiene muy pocos caracteres especiales  y un lexer simple
 En principio, (){} separan cosas,pero el resto debe separado por espacios.
-}


{- Hete aquí los números naturales -}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{- C-c C-l ejecuta el type checker. -}
{- Agda acepta unicode:  ℕ = \bN, → = \to -}

{- El siguiente pragma nos permite escribir decimales 
  en lugar de suc (suc (.... ))
-}
{-# BUILTIN NATURAL ℕ    #-}

{- En versiones viejas agregar
 {-# BUILTIN ZERO    zero #-}
 {-# BUILTIN SUC     suc  #-}
-}









_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)


{- C-c C-c divide en casos -}
{- C-c C-r refina el problema -}
{- C-c C-SPC llena el agujero -}
{- C-c C-. Me muestra información del agujero. -}


{- evaluar usando C-c C-n -}


----------------------------------------------
{- Ejercicio : Definir la multiplicación -}
_*_ :  ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n) 
----------------------------------------------

infixl 6 _+_
infixl 7 _*_

data Bool : Set where
        tt  : Bool
        ff : Bool

{- Escribir una función que decida la 
  igualdad de los números naturales,
   eq m n = tt, si m=n
   eq m n = ff, en otro caso
-}
eq : ℕ → ℕ → Bool
eq zero zero = tt
eq zero (suc _) = ff
eq (suc _) zero = ff
eq (suc n) (suc m) = eq n m

{- definimos las listas -}
{- Declaramos asociatividad y
  precedencia del operador ∷ -}
infixr 5 _∷_

{- \:: -}

data List (A : Set) : Set where
      [] : List A
      _∷_ : (x : A) → (xs : List A) → List A

{- el guión bajo indica el lugar de los argumentos.
   Esta notación permite operadores mixfijos
-}

{- snoc agrega un elemento al final de la lista -}
snoc : {A : Set} → List A → A → List A
snoc [] a = a ∷ []
snoc (x ∷ xs) a = x ∷ snoc xs a

{- {A : Set} .. es un parámetro implícito, es insertado por el compilador. -}

{- dar vuelta una lista -}
rev : {A : Set} → List A → List A
rev [] = []
rev (x ∷ xs) = snoc (rev xs) x

--------------------------------------------------
{- Ej : longitud de una lista -}
length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + (length xs)
--------------------------------------------------


--------------------------------------------------
{- Ej : concatenar dos listas -}
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
x ∷ xs ++ ys = x ∷ (xs ++ ys)
--------------------------------------------------

infixr 4 _++_

{- aplicación punto a punto -}
appL : {A B : Set} → List (A → B) → List A -> List B
appL [] [] = []
appL [] (x ∷ xs) = [] --trucho
appL (f ∷ fs) [] = [] --trucho
appL (f ∷ fs) (x ∷ xs) = (f x) ∷ (appL fs xs)





{-
¿Qué longitud debería tener la respuesta?

Si alguna de las listas es más larga que la otra, 
significa que alguna de las entradas tenía basura.

Si la listas son de igual longitud, digamos n, entonces la respuesta debería ser n.
O sea esperamos que

  ∀fs, xs. length fs ≡ length xs ⇒ length (appL fs xs) ≡ length fs

En EDyAII lo probaríamos por inducción sobre fs (por ejemplo).
-}





{- Definimos el tipo Maybe -}
data Maybe (A : Set) : Set where
     nothing : Maybe A
     just    : A -> Maybe A

{- devolver el elemento enésimo de una lista. -}
_!!_ : {A : Set} → List A → ℕ → Maybe A
[] !! n = nothing
(x ∷ xs) !! zero = just  x
(x ∷ xs) !! suc n = xs !! n












{- 
Necesitamos chequear dinámicamente que la proyección está bien definida.
Esto se hace en runtime!
  
  
  Mejor usamos tipos más precisos!
-}
{- Definimos los vectores -}

data Vec (A : Set) : ℕ → Set where
    []   : Vec A 0 
    _∷_  : {n : ℕ} → (x : A) → (xs : Vec A n) → Vec A (1 + n)

{-
Ejemplos:
          [] : Vec ℕ 0
      2 ∷ [] : Vec ℕ 1
  4 ∷ 2 ∷ [] : Vec ℕ 2

Con esta definición internalizamos las invariantes sobre longitud de la listas.

¡*Chequeamos* la longitud al escribir el programa, en lugar de *medir* en runtime!
-}


mapVec : ∀{n A B} → (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

snoc' : {A : Set}{n : ℕ} → Vec A n → A → Vec A (suc n)
snoc' [] a = a ∷ []
snoc' (x ∷ xs) a = x ∷ (snoc' xs a)

rev' : {A : Set}{n : ℕ} → Vec A n → Vec A n
rev' [] = []
rev' (x ∷ xs) = snoc' (rev' xs) x


{- El tipo Fin n me representa el conjunto {0,1,...,n-1}  -}
data Fin : ℕ -> Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n -> Fin (suc n)

{-
Fin 0   no tiene elementos
Fin 1   zero
Fin 2   zero  (suc (zero))
Fin 3   zero  (suc zero) (suc (suc (zero)))

-}




{- Un vector con los elementos de Fin, en orden -}
enum : (n : ℕ) → Vec (Fin n) n
enum zero = []
enum (suc n) = zero ∷ mapVec suc (enum n)



{- elemento máximo de un conjunto de tipo Fin (suc n) -}
max : {n : ℕ} → Fin (suc n)
max {zero} = zero
max {suc n} = suc max 


{- nat : da el natural correspondiente a un elemento de Fin n -}
nat : {n : ℕ} → Fin n → ℕ
nat zero = 0
nat (suc n) = suc (nat n)


-----------------------------------------------------------
{- Ej : emb inserta un elemento de Fin n en Fin (suc n)
        de manera tal que nat x = nat (emb x)
-}
emb : {n : ℕ} → Fin n → Fin (suc n)
emb zero = zero
emb (suc x) = suc (emb x)

-- pred : {n : ℕ} → Fin n → Fin n
-- pred zero = zero
-- pred (suc x) = emb x

{- Ej: inv me lleva de {0,1,...,n-1} a {n-1,..,1,0} -}
inv : {n : ℕ} → Fin n → Fin n
inv zero = max
inv (suc i) = emb (inv i)
-----------------------------------------------------------




{- proyección para vectores -}
_!!'_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !!' zero = x
(x ∷ xs) !!' suc n = xs !!' n





{- aplicación punto a punto para vectores -}
appV : {A B : Set}{n : ℕ} → Vec (A → B) n → Vec A n → Vec B n
appV [] [] = []
appV (f ∷ fs) (x ∷ xs) = (f x) ∷ (appV fs xs)






{- Estáticamente aseguramos que la proyección está bien definida -}

Vector : ℕ → Set {- Vec n es un vector n-dimensional -}
Vector m = Vec ℕ m

Matrix : ℕ → ℕ → Set {- Matrix m n es una matriz de m x n -}
Matrix m n = Vec (Vector n) m

-------------------------------------------------------
{- Ej: multiplicación por un escalar -}
_*v_ : {n : ℕ} → ℕ → Vector n → Vector n
k *v ms = mapVec (λ x → k * x) ms

v1 : Vector 3
v1 = 1 ∷ 2 ∷ 3 ∷ []

test1 : Vector 3
test1 = 2 *v v1

empty : ∀{n A} → A → Vec A n
empty {0} _ = []
empty {suc n} x = x ∷ empty x

emptyvec : {n : ℕ} → Vector n
emptyvec = empty 0

{- Ej: suma de vectores -}
_+v_ : {n : ℕ} → Vector n → Vector n → Vector n
[] +v [] = []
(m ∷ ms) +v (n ∷ ns) = (m + n) ∷ (ms +v ns)

v2 : Vector 3
v2 = 2 ∷ 3 ∷ 0 ∷ []

test2 : Vector 3
test2 = v1 +v v2

{- Ej: multiplicación de un vector y una matriz -}
_*vm_ : {m n : ℕ} → Vector m → Matrix m n → Vector n
[] *vm [] = emptyvec
(m ∷ ms) *vm (ns ∷ nss) = (m *v ns) +v (ms *vm nss)

id3 : Matrix 3 3
id3 = (1 ∷ 0 ∷ 0 ∷ []) 
    ∷ (0 ∷ 1 ∷ 0 ∷ []) 
    ∷ (0 ∷ 0 ∷ 1 ∷ []) 
    ∷ []

test3 : Vector 3
test3 = v1 *vm id3

emptymat : {n m : ℕ} → Matrix n m
emptymat = empty emptyvec

{- Ej: multiplicación de matrices -}
_*mm_ : {l m n : ℕ} → Matrix l m → Matrix m n → Matrix l n
[] *mm [] = emptymat
[] *mm (x ∷ nss) = emptymat
(ms ∷ mss) *mm nss = (ms *vm nss) ∷ (mss *mm nss)

inv3 : Matrix 3 3
inv3 = (0 ∷ 0 ∷ 1 ∷ []) 
     ∷ (0 ∷ 1 ∷ 0 ∷ []) 
     ∷ (1 ∷ 0 ∷ 0 ∷ []) 
     ∷ []

test4 : Matrix 3 3
test4 = inv3 *mm inv3

appendCol : {n m : ℕ} → Vector m → Matrix m n → Matrix m (suc n)
appendCol [] [] = emptymat
appendCol (x ∷ xs) (ms ∷ mss) = (x ∷ ms) ∷ appendCol xs mss

{- Ej: transposición de matrices -}
transpose : {n m : ℕ} → Matrix m n → Matrix n m
transpose [] = emptymat
transpose (m ∷ ms) = appendCol m (transpose ms)

ej5 : Matrix 3 3
ej5 = ( 0 ∷ 1 ∷ 2 ∷ [])
    ∷ ( 3 ∷ 4 ∷ 5 ∷ [])
    ∷ ( 6 ∷ 7 ∷ 8 ∷ [])
    ∷ []

test5 : Matrix 3 3
test5 = transpose ej5

--------------------------------------------------
{-
Bajar el archivo del repositorio y hacer los ejercicios.
 git clone https://github.com/mjaskelioff/progcat.git

-}
    