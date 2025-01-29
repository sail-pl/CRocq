From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Coalgebra CategoryCoAlgebra.

Class bisimulation {C : Category} {F : Functor C C} (A B : CoAlgebra F): Type := 
{

    R : CoAlgebra F;
    proj1 : CoAlgebraMorphism R A;
    proj2 : CoAlgebraMorphism R B;
    proj1_spec : (destr A) ∘ proj1 = (fmap F proj1) ∘ (destr R);
    proj2_spec : (destr B) ∘ proj2 = (fmap F proj2) ∘ (destr R) 
}.

