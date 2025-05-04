From CRocq.Category Require Import Category Functor.

(* Unset Automatic Proposition Inductives. *)


Class CoAlgebra {C : Category} (F : Functor C C) : Type := {
    coalgebra_obj : C;
    coalgebra_morph : C coalgebra_obj (F coalgebra_obj)
}.

Arguments coalgebra_obj {C F} _.
Arguments coalgebra_morph {C F} _.

Class CoAlgebraMorphism {C : Category} (F : Functor C C)
    (A B : CoAlgebra F) : Type := 
    {
        coalgebramorphism_morph : 
            C (coalgebra_obj A) (coalgebra_obj B);
        H_f : (fmap F coalgebramorphism_morph) ∘ (coalgebra_morph A) = 
            (coalgebra_morph B) ∘ coalgebramorphism_morph
    }.

Coercion coalgebramorphism_morph : CoAlgebraMorphism >-> hom.



(* coalgebra appears as a morphism *)

(* Arguments coalgebra_obj {C F} _. *)
(* Arguments destr {C} _ _. *)

(* Generalizable Variables  C F.

Record CoAlgebraMorphism {C : Category} {F : Functor C C}
    (a b : C) (A : CoAlgebra F a) (B : CoAlgebra F b) : Type :=
    {
        coalgebra_morph : C a b;
        H_f : (fmap F coalgebra_morph) ∘ A   = B ∘ coalgebra_morph
}.

Coercion coalgebra_morph : CoAlgebraMorphism >-> hom. *)

(* Class CoAlgebra {C : Category} (F : Functor C C) : Type :=
{
    coalgebra_obj : C;
    destr : C coalgebra_obj (F coalgebra_obj)
}.

Arguments coalgebra_obj {C F} _.
Arguments destr {C F} _.

Generalizable Variables  C F.

Record CoAlgebraMorphism {C : Category} {F : Functor C C}
    (A B : CoAlgebra F) : Type := 
    {
        f : C (coalgebra_obj A) (coalgebra_obj B);
        H_f : (fmap F f) ∘ (destr A)   = (destr B) ∘ f  
}.

Coercion f : CoAlgebraMorphism >-> hom. *)
