From reactive.utils Require Import Functor Category.

Unset Automatic Proposition Inductives.

Class Algebra {C : Category} (F : Functor C C) : Type :=
{
    a_u : C;
    constr : C (F a_u) a_u
}.

Class CoAlgebra {C : Category} (F : Functor C C) : Type :=
{
    ca_u : C;
    destr : C ca_u (F ca_u)
}.

(* Morphism *)