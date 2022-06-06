open import Categories
open import Categories.Products
open import Categories.Terminal

module clase11.CCC {a}{b}{C : Cat {a}{b}}
                                        (hasProducts : Products C)
                                        (T : Cat.Obj C)
                                        (hasTerminal : Terminal C T)
                                        where

open import Library hiding (_×_ ; curry ; uncurry)

open Cat C
open Products hasProducts

record CCC : Set (a ⊔ b) where
  infix 4 _⇒_
  field
     _⇒_ : Obj → Obj → Obj
     curry : ∀{X Y Z} → Hom (X × Y) Z → Hom X (Y ⇒ Z)
     uncurry : ∀{X Y Z} → Hom X (Y ⇒ Z) → Hom (X × Y) Z
     lawcurry1 : ∀{X Y Z}{f : Hom (X × Y) Z} → uncurry (curry f) ≅ f
     lawcurry2 : ∀{X Y Z}{f : Hom X (Y ⇒ Z)} → curry (uncurry f) ≅ f
     nat-curry : ∀{X X' Y Z Z'} → {f : Hom X' X}{h : Hom Z Z'}{x : Hom (X × Y) Z}
               →  curry (h ∙ uncurry iden) ∙ curry x ∙ f ≅ curry (h ∙ x ∙ pair f iden)

  apply : ∀{Y Z} → Hom ((Y ⇒ Z) × Y) Z
  apply = uncurry iden    

  {- Ejercicio: completar la definición -}
  map⇒ : ∀{X Y Z} → Hom X Z → Hom (Y ⇒ X) (Y ⇒ Z)
  map⇒ f = curry (f ∙ apply)

module Properties (isCCC : CCC) where
  open CCC isCCC
  open import Categories.Products.Properties hasProducts 
         using (comp-pair ; iden-pair )
  
 
  {- Ejercicio: map⇒ preserva identidades. -}
  map⇒iden : ∀{X Y} → map⇒ {X} {Y} {X} (iden {X}) ≅ iden {Y ⇒ X}
  map⇒iden = proof
             map⇒ iden
             ≅⟨ refl ⟩
             curry (iden ∙ apply)
             ≅⟨ cong curry idl ⟩
             curry apply
             ≅⟨ cong curry refl ⟩
             curry (uncurry iden)
             ≅⟨ lawcurry2 ⟩
             iden
             ∎

  {- Ejercicio: Propiedad de curry con map⇒. Caso particular de nat-curry, con f = iden. -}
  curry-prop : ∀{X Y Z Z'}{f : Hom (X × Y) Z}{g : Hom Z Z'}
              →  map⇒ g ∙ curry f ≅ curry (g ∙ f)
  curry-prop {f = f} {g} = proof
                           map⇒ g ∙ curry f
                           ≅⟨ refl ⟩
                           curry (g ∙ apply) ∙ curry f
                           ≅⟨ refl ⟩
                           curry (g ∙ uncurry iden) ∙ curry f
                           ≅⟨ sym idr ⟩
                           (curry (g ∙ uncurry iden) ∙ curry f) ∙ iden
                           ≅⟨ ass ⟩
                           curry (g ∙ uncurry iden) ∙ curry f ∙ iden
                           ≅⟨ nat-curry ⟩
                           curry (g ∙ f ∙ pair iden iden)
                           ≅⟨ cong curry (congr (congr iden-pair)) ⟩
                           curry (g ∙ f ∙ iden)
                           ≅⟨ cong curry (congr idr) ⟩
                           curry (g ∙ f)
                           ∎

  {- Ejercicio: probar que para todo objeto B,  B⇒_ define un endofunctor -}
  open import Functors
  nat-endo : {B : Obj} → Fun C C
  nat-endo {B} = functor (B ⇒_) map⇒ map⇒iden lemma
          where lemma : {X Y Z : Obj} {f : Hom Y Z} {g : Hom X Y} →
                        map⇒ (f ∙ g) ≅ map⇒ f ∙ map⇒ g
                lemma {f = f} {g = g} = proof
                                        map⇒ (f ∙ g)
                                        ≅⟨ refl ⟩
                                        curry ((f ∙ g) ∙ apply)
                                        ≅⟨ cong curry ass ⟩
                                        curry (f ∙ g ∙ apply)
                                        ≅⟨ sym curry-prop ⟩
                                        map⇒ f ∙ curry (g ∙ apply)
                                        ≅⟨ refl ⟩
                                        map⇒ f ∙ map⇒ g
                                        ∎ 

  {- Una definición alternativa de exponencial se puede dar en base al morfismo apply:
    Un exponencial entre A y B es un objeto B ⇒ A, y un morfismo apply : (B ⇒ A) × B → A tal que
    para cada f : C × B → A existe un único morfismo curry f : C → (B ⇒ A) tal que 
        apply ∙ pair (curry f) iden ≅ f  

    Ejercicio: probar que nuestra definición implica la de más arriba. 
  -}
  curry-exp : ∀{X Y Z} {f : Hom (X × Y) Z} →  apply ∙ pair (curry f) iden ≅ f
  curry-exp {f = f} = {!   !}

  