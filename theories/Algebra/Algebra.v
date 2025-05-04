From CRocq.Category Require Import Category Functor.

(* Unset Automatic Proposition Inductives. *)

Class Algebra {C : Category} (F : Functor C C) : Type :=
{
    a_u : C; (* carrier *)
    constr : C (F a_u) a_u
}.

Arguments a_u {C F} _.
Arguments constr {C F} _.

Generalizable Variables  C F.

Record AlgebraMorphism {C : Category} {F : Functor C C}
    (A B : Algebra F) : Type := 
    {
        f : C (a_u A) (a_u B);
        H_f : (constr B) ∘ (fmap F f) = f ∘ (constr A)
}.

Coercion f : AlgebraMorphism >-> hom.
