From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.
From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Algebra.

(* morphisms are simply morphism of the category *)

Definition aid {C : Category} (F : Functor C C) 
    (a : Algebra F): AlgebraMorphism a a.
    refine ({|f := idty _ |}).
Proof.
    rewrite functors_preserve_identities.
    rewrite compose_left_idty.
    rewrite compose_right_idty.
    reflexivity.
Defined.

Definition acompose {C : Category} (F : Functor C C) 
    (a b c : Algebra F) : 
        AlgebraMorphism b c -> AlgebraMorphism a b -> AlgebraMorphism a c.
    intros.
        refine ({|f:=compose X X0 |}).
        rewrite <- functors_preserve_composition.
        destruct X, X0.
        simpl.
        rewrite compose_assoc.
        rewrite H_f.
        rewrite <- compose_assoc.
        rewrite H_f0.
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