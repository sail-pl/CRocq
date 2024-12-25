From Categories.Category Require Import Category Functor.

Unset Automatic Proposition Inductives.

Class CoAlgebra {C : Category} (F : Functor C C) : Type :=
{
    ca_u : C;
    destr : C ca_u (F ca_u)
}.

Arguments ca_u {C F} _.
Arguments destr {C F} _.

Generalizable Variables  C F.

Record CoAlgebraMorphism {C : Category} {F : Functor C C}
    (A B : CoAlgebra F) : Type := 
    {
        f : C (ca_u A) (ca_u B);
        H_f : (fmap F f) ∘ (destr A)   = (destr B) ∘ f  
}.

Coercion f : CoAlgebraMorphism >-> hom.
