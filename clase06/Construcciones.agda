open import Library hiding (_×_ ; _,_ ; swap)
open import Categories

module clase06.Construcciones {a}{b}(C : Cat {a} {b}) where

--Revisamos la definición de categorías
open Cat C






-- Revisamos Isomorfismos
open import Categories.Iso C











----------------------
-- Objeto Terminal
----------------------

module ObjTerminal where

  record Terminal (T : Obj) : Set (a ⊔ b) where
    constructor term
    field t : ∀{X} → Hom X T
          law : ∀{X}{f : Hom X T} → t {X} ≅ f
  open Terminal
  




  open Iso
  
{- Dos objetos terminales son isomorfos -}
  TerminalIso : (T T' : Obj)
            → (p : Terminal  T)
            → (q : Terminal T')
            → Iso (t p {T'})
  TerminalIso T T' (term t₁ law₁) (term t₂ law₂) = iso t₂ (trans (sym law₁) law₁) (trans (sym law₂) law₂)

open ObjTerminal public

------------------
-- Productos
------------------

module Productos where

  record Products : Set (a ⊔ b) where
    constructor prod
    infixr 3 _×_
    field _×_ : Obj → Obj → Obj
          π₁ : ∀{A B} → Hom (A × B) A
          π₂ : ∀{A B} → Hom (A × B) B
          ⟨_,_⟩ : ∀{A B C} →(f : Hom C A) → (g : Hom C B) → Hom C (A × B)
          law1 : ∀{A B C}{f : Hom C A}{g} → π₁ {A} {B} ∙ ⟨ f , g ⟩ ≅ f
          law2 : ∀{A B C}{f : Hom C A}{g} → π₂ {A} {B} ∙ ⟨ f , g ⟩ ≅ g
          law3 : ∀{A B C}{f : Hom C A}{g : Hom C B}{h : Hom C (A × B)} →
                 π₁ ∙ h ≅ f → π₂ ∙ h ≅ g → h ≅ ⟨ f , g ⟩
  
  open Products

  ProductIso : ∀{A B} → (p q : Products)
           → Iso (⟨_,_⟩ p {A} {B} (π₁ q) (π₂ q))
  ProductIso p q = iso (⟨_,_⟩ q (π₁ p) (π₂ p))
                      (proof
                      ⟨_,_⟩ p (π₁ q) (π₂ q) ∙ ⟨_,_⟩ q (π₁ p) (π₂ p)
                      ≅⟨ law3 p (trans (sym ass) (trans (cong₂ _∙_ (law1 p) refl) (law1 q)))
                                (trans (sym ass) (trans (cong₂ _∙_ (law2 p) refl) (law2 q))) ⟩
                      ⟨_,_⟩ p (π₁ p)  (π₂ p)
                      ≅⟨ sym (law3 p idr idr) ⟩
                      iden
                      ∎)
                      (proof
                      ⟨ q , π₁ p ⟩ (π₂ p) ∙ ⟨ p , π₁ q ⟩ (π₂ q)
                      ≅⟨ law3 q (trans (sym ass) (trans (cong₂ _∙_ (law1 q) refl) (law1 p)))
                                (trans (sym ass) (trans (cong₂ _∙_ (law2 q) refl) (law2 p))) ⟩
                       ⟨ q , π₁ q ⟩ (π₂ q)
                      ≅⟨ sym (law3 q idr idr) ⟩
                      iden
                      ∎)


open Productos public

module ProductMorphisms (p : Products)
                        (Uno : Obj)(t : Terminal Uno)
                        where
  open Products p
  open Terminal t

  {- Toda categoría con productos posee los siguientes morfismos -}
  unit : ∀{A} → Hom (A × Uno) A
  unit = π₁

  swap : ∀{A B} → Hom (A × B)  (B × A)
  swap = ⟨ π₂ , π₁ ⟩

  assoc : ∀{A B C} → Hom ((A × B) × C) (A × (B × C))
  assoc = ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩

  -- Ejercicio extra Probar que unit, swap, y assoc son isomorfismos.

  {- Definir el morfismo pair -}
  pair : ∀{A B C D}(f : Hom A B)(g : Hom C D)
       → Hom (A × C) (B × D)
  pair f g = ⟨ f ∙ π₁ , g ∙ π₂ ⟩

  -- Probar las siguientes propiedades de pair

  idpair : ∀{X Y} → pair (iden {X}) (iden {Y}) ≅ iden {X × Y}
  idpair {X} {Y} = sym (law3 (trans idr (sym idl)) (trans idr (sym idl)))

  compdistrib : ∀{A B C D E F}
              → (f : Hom B C)(g : Hom A B)
              → (h : Hom E F)(i : Hom D E)
              → pair (f ∙ g) (h ∙ i) ≅ pair f h ∙ pair g i
  compdistrib f g h i = sym (law3 (proof 
                                   π₁ ∙ pair f h ∙ pair g i
                                   ≅⟨ sym ass ⟩
                                   (π₁ ∙ pair f h) ∙ pair g i
                                   ≅⟨ cong (λ x → x ∙ pair g i) law1 ⟩
                                   (f ∙ π₁) ∙ pair g i
                                   ≅⟨ ass ⟩
                                   f ∙ (π₁ ∙ pair g i)
                                   ≅⟨ cong (λ x → f ∙ x) law1 ⟩
                                   f ∙ (g ∙ π₁)
                                   ≅⟨ sym  ass ⟩
                                   (f ∙ g) ∙ π₁
                                   ∎) 
                                   
                                  (proof 
                                   π₂ ∙ pair f h ∙ pair g i
                                   ≅⟨ sym ass ⟩
                                   (π₂ ∙ pair f h) ∙ pair g i
                                   ≅⟨ cong (λ x → x ∙ pair g i) law2 ⟩
                                   (h ∙ π₂) ∙ pair g i
                                   ≅⟨ ass ⟩
                                   h ∙ (π₂ ∙ pair g i)
                                   ≅⟨ cong (λ x → h ∙ x) law2 ⟩
                                   h ∙ (i ∙ π₂)
                                   ≅⟨ sym  ass ⟩
                                   (h ∙ i) ∙ π₂
                                   ∎))

----------------------
-- Inicial
----------------------

record Initial (I : Obj) : Set (a ⊔ b) where
  constructor init
  field i : ∀{X} → Hom I X
        law : ∀{X}{f : Hom I X} → i {X} ≅ f 

open Initial

{- el morfismo universal del objeto inicial a sí mismo es la identidad -}
init-iden : (I : Obj){init : Initial I}
          → i init {I} ≅ iden {I}
init-iden I {init i₁ law₁} = law₁

----------------------
-- Coproductos
----------------------

record Coproducts : Set (a ⊔ b) where
  constructor coproduct
  infixr 2 _+_
  field _+_   : Obj → Obj → Obj
        inl   : ∀{A B} → Hom A (A + B)
        inr   : ∀{A B} → Hom B (A + B)
        [_,_] : ∀{A B C} -> Hom A C -> Hom B C -> Hom (A + B) C
        law1  : ∀{A B C}{f : Hom A C}{g : Hom B C} →
                [ f , g ] ∙ inl ≅ f
        law2  : ∀{A B C}{f : Hom A C}{g : Hom B C} →
                [ f , g ] ∙ inr ≅ g
        law3  : ∀{A B C}{f : Hom A C}{g : Hom B C}{h : Hom (A + B) C} →
                h ∙ inl ≅ f → h ∙ inr ≅ g → h ≅ [ f , g ]

 {- Ejercicio: Definir copair        -}
  copair : ∀{X Y Z W}(f : Hom X Z)(g : Hom Y W) → Hom (X + Y) (Z + W)
  copair f g = [ inl ∙ f , inr ∙ g ]
 


module CoproductMorphisms {cp : Coproducts} where

  open Coproducts cp

  {- Definir el siguiente morfismo -}
  plus : ∀{A B C D}(f : Hom A B)(g : Hom C D) → Hom (A + C) (B + D)
  plus f g = [ inl ∙ f , inr ∙ g ]

  {- Probar las siguentes propiedades -}

  idplus : ∀{A B} → plus (iden {A}) (iden {B}) ≅ iden {A + B}
  idplus = sym (law3 (trans idl (sym idr)) (trans idl (sym idr)))

  idcomp :  ∀{A B C D E F}
         → (f : Hom B C)(g : Hom A B)
         → (h : Hom E F)(i : Hom D E)
         → plus (f ∙ g) (h ∙ i) ≅ plus f h ∙ plus g i
  idcomp  f g h i = sym (law3 (proof 
                               (plus f h ∙ plus g i) ∙ inl
                               ≅⟨ ass ⟩
                               plus f h ∙ plus g i ∙ inl
                               ≅⟨ cong (λ x → plus f h ∙ x) law1 ⟩
                               plus f h ∙ inl ∙ g
                               ≅⟨ sym ass ⟩
                               (plus f h ∙ inl) ∙ g
                               ≅⟨ cong (λ x → x ∙ g) law1 ⟩
                               (inl ∙ f) ∙ g
                               ≅⟨ ass ⟩
                               inl ∙ (f ∙ g)
                               ∎)
                              (proof 
                               (plus f h ∙ plus g i) ∙ inr
                               ≅⟨ ass ⟩
                               plus f h ∙ plus g i ∙ inr
                               ≅⟨ cong (λ x → plus f h ∙ x) law2 ⟩
                               plus f h ∙ inr ∙ i
                               ≅⟨ sym ass ⟩
                               (plus f h ∙ inr) ∙ i
                               ≅⟨ cong (λ x → x ∙ i) law2 ⟩
                               (inr ∙ h) ∙ i
                               ≅⟨ ass ⟩
                               inr ∙ (h ∙ i)
                               ∎))  

module Intercambio {cp : Coproducts}{p : Products} where

  open Coproducts cp
  open Products p renaming (law1 to lawp1 ; law2 to lawp2 ; law3 to lawp3)

   {- intercambio entre poducto y coproducto -}

  intercambio : ∀{A B C D}
         → (f : Hom A C)(g : Hom B C)
         → (h : Hom A D)(k : Hom B D)
         → ⟨ [ f , g ] , [ h , k ] ⟩ ≅ [ ⟨ f , h ⟩ , ⟨ g , k ⟩ ]
  intercambio f g h k = proof
                        ⟨ [ f , g ] , [ h , k ] ⟩
                        ≅⟨ {!   !} ⟩
                        {!   !}
                        ≅⟨ {!   !} ⟩
                        {!   !}
                        ≅⟨ {!   !} ⟩
                        {!   !}
                        ≅⟨ {!   !} ⟩
                        {!   !}
                        ≅⟨ {!   !} ⟩
                        {!   !}
                        ≅⟨ {!   !} ⟩
                        {!   !}
                        ≅⟨ {!   !} ⟩
                        [ ⟨ f , h ⟩ , ⟨ g , k ⟩ ]
                        ∎


  -- [ f , g ] : (A + B) → C
  -- [ h , k ] : (A + B) → D
  -- ...       : Hom (A + B) (C × D)

