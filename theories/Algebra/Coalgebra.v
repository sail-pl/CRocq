From Categories.Category Require Import Category Functor.

Unset Automatic Proposition Inductives.

Class CoAlgebra {C : Category} (F : Functor C C) : Type :=
{
    ca_u : C;
    destr : C ca_u (F ca_u)
}.

Arguments ca_u {C F} _.
Arguments destr {C F} _.
