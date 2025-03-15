From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.
From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Algebra.

(* morphisms are simply morphism of the category *)

Definition aid {C : Category} (F : Functor C C) 
    (a : Algebra F): AlgebraMorphism a a.
    refine ({|f := id _ |}).
Proof.
    rewrite funct_preserves_identities.
    rewrite cat_left_idty.
    rewrite cat_right_idty.
    reflexivity.
Defined.

Definition acompose {C : Category} (F : Functor C C) 
    (a b c : Algebra F) : 
        AlgebraMorphism b c -> AlgebraMorphism a b -> AlgebraMorphism a c.
    intros.
        refine ({|f:=compose X X0 |}).
        rewrite <- funct_preserves_composition.
        destruct X, X0.
        simpl.
        rewrite cat_assoc.
        rewrite H_f.
        rewrite <- cat_assoc.
        rewrite H_f0.
        rewrite cat_assoc.
        reflexivity.
    Defined.

Lemma acat_a : forall (C : Category) (F : Functor C C) (a b : Algebra F)
(f : AlgebraMorphism a b),
acompose F a a b f (aid F a) = f.
Admitted.

Lemma acat_b : forall (C : Category) (F : Functor C C) (a b : Algebra F)
(f : AlgebraMorphism a b),
acompose F a b b (aid F b) f = f.
Admitted.

Lemma acat_c : forall (C : Category) (F : Functor C C) (a b c d : Algebra F)
(f : AlgebraMorphism a b)
(g : AlgebraMorphism b c)
(h : AlgebraMorphism c d),
acompose F a c d h (acompose F a b c g f) =
acompose F a b d (acompose F b c d h g) f.
Admitted.


#[refine] Instance AlgebraCat {C : Category} (F : Functor C C) : Category := 
{
    obj := Algebra F;
    hom := AlgebraMorphism;
    id := aid F;
    compose := acompose F
}.

Proof.
- apply acat_a.
- apply acat_b.
- apply acat_c.
Defined.