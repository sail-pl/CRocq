From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Coalgebra CategoryCoAlgebra.

(* R is also a relation *)

Class bisimulation {C : Category} {H : Cartesian C} {F : Functor C C} (A B : CoAlgebra F): Type := 
{
    R : CoAlgebra F;
    f : monic (coalgebra_obj R) ((coalgebra_obj A) ⊗ (coalgebra_obj B));
    proj1_spec : 
        (coalgebra_morph A) ∘ (π₁ ∘ f) 
            = (fmap F (π₁ ∘ f)) ∘ (coalgebra_morph R);
    proj2_spec : (coalgebra_morph B) ∘ (π₂ ∘ f) 
        = (fmap F (π₂ ∘ f)) ∘ (coalgebra_morph R) 
}.


(* Class bisimulation {C : Category} {H : Cartesian C} {F : Functor C C} (A B : CoAlgebra F): Type := 
{
    R : CoAlgebra F;
    H : crelation (coalgebra_obj A) (coalgebra_obj B) (coalgebra_obj R);
    proj1 : CoAlgebraMorphism R A;
    proj2 : CoAlgebraMorphism R B;

    proj1_spec : 
        (coalgebra_morph A) ∘ proj1 
            = (fmap F proj1) ∘ (coalgebra_morph R);
    proj2_spec : (coalgebra_morph B) ∘ proj2 = (fmap F proj2) ∘ (coalgebra_morph R) 
}. *)
