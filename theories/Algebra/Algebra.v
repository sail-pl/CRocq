From Categories.Category Require Import Category Functor.

Unset Automatic Proposition Inductives.

Class Algebra {C : Category} (F : Functor C C) : Type :=
{
    a_u : C; (* carrier *)
    constr : C (F a_u) a_u
}.

Arguments a_u {C F} _.
Arguments constr {C F} _.

Class CoAlgebra {C : Category} (F : Functor C C) : Type :=
{
    ca_u : C;
    destr : C ca_u (F ca_u)
}.

Arguments ca_u {C F} _.
Arguments destr {C F} _.

Generalizable Variables  C F.

Record AlgebraMorphism {C : Category} {F : Functor C C}
    (A B : Algebra F) : Type := 
    {
        f : C (a_u A) (a_u B);
        H_f : (constr B) ∘ (fmap f) = f ∘ (constr A)
}.

Coercion f : AlgebraMorphism >-> hom.

(* morphisms are simply morphism of the category *)

Definition aid {C : Category} (F : Functor C C) 
    (a : Algebra F): AlgebraMorphism a a.
    refine ({|f := idty _ |}).
Proof.
    rewrite fmap_identity.
    rewrite compose_left_idty.
    rewrite compose_right_idty.
    reflexivity.
Defined.

Definition acompose {C : Category} (F : Functor C C) 
    (a b c : Algebra F) : 
        AlgebraMorphism b c -> AlgebraMorphism a b -> AlgebraMorphism a c.
    intros.
        refine ({|f:=compose X X0 |}).
        rewrite <- fmap_compose.
        destruct X, X0.
        simpl.
        rewrite compose_assoc.
        rewrite H_f0.
        rewrite <- compose_assoc.
        rewrite H_f1.
        rewrite compose_assoc.
        reflexivity.
    Defined.

#[refine] Instance AlgebraCat {C : Category} (F : Functor C C) : Category := 
{
    obj := Algebra F;
    hom := AlgebraMorphism;
    idty := aid F;
    compose := acompose F
}.
Proof.
Admitted.
