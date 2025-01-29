From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Coalgebra CategoryCoAlgebra.

(* R is also a relation *)

Class bisimulation {C : Category} {F : Functor C C} (A B : CoAlgebra F): Type := 
{
    (* R has a domain, must be both a coalgebra and a relation *)
    R : CoAlgebra F;
    proj1 : CoAlgebraMorphism R A;
    proj2 : CoAlgebraMorphism R B;
    proj1_spec : (coalgebra_morph A) ∘ proj1 = (fmap F proj1) ∘ (coalgebra_morph R);
    proj2_spec : (coalgebra_morph B) ∘ proj2 = (fmap F proj2) ∘ (coalgebra_morph R) 
}.
