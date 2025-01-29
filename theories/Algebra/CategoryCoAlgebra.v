From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.
From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Coalgebra.

(* morphisms are simply morphism of the category *)

Section Category.

    Context {C : Category} {F : Functor C C}.

    Definition id_ca (f : CoAlgebra F) : CoAlgebraMorphism f f.
    Proof.
        refine ({|coalgebramorphism_morph := idty (coalgebra_obj f)|}).
        rewrite functors_preserve_identities.
        rewrite compose_left_idty.
        rewrite compose_right_idty.
        reflexivity.
    Defined.

    Definition compose_ca (f g h : CoAlgebra F) : 
        CoAlgebraMorphism g h -> CoAlgebraMorphism f g -> CoAlgebraMorphism f h.
    Proof.
        intros .
        refine ({|coalgebramorphism_morph := compose X X0 |}).
        rewrite <- functors_preserve_composition.
        destruct X, X0.
        simpl.
        rewrite compose_assoc.
        rewrite <- H_f.
        rewrite <- compose_assoc.
        rewrite H_f0.
        rewrite compose_assoc.
        reflexivity.
    Defined.

    Lemma acat_a : forall (f g : CoAlgebra F) 
            (h : CoAlgebraMorphism f g),
                compose_ca _ _ _ h (id_ca f) = h.
    Admitted.

    Lemma acat_b : forall (f g : CoAlgebra F) 
            (h : CoAlgebraMorphism f g),
                compose_ca _ _ _ (id_ca g) h = h.
    Admitted.

    Lemma acat_c : forall 
        (f_a f_b f_c f_d : CoAlgebra F) 
        (f : CoAlgebraMorphism f_a f_b)
        (g : CoAlgebraMorphism f_b f_c)
        (h : CoAlgebraMorphism f_c f_d),
            compose_ca _ _ _ h (compose_ca _ _ _ g f) =
                compose_ca _ _ _ (compose_ca _ _ _ h g) f.
    Admitted.

    #[refine] Instance CoAlgebraCat : Category := 
    {
        obj := CoAlgebra F;
        hom := CoAlgebraMorphism;
        idty := id_ca ;
        compose := compose_ca
    }.
Proof.
- apply acat_a.
- apply acat_b.
- apply acat_c.
Defined.

End Category.

(* Lemma acat_b : forall (C : Category) (F : Functor C C) (a b : CoAlgebra F)
(f : CoAlgebraMorphism a b),
acompose F a b b (aid F b) f = f.
Admitted. *)

(* Lemma acat_c : forall (C : Category) (F : Functor C C) (a b c d : CoAlgebra F)
(f : CoAlgebraMorphism a b)
(g : CoAlgebraMorphism b c)
(h : CoAlgebraMorphism c d),
acompose F a c d h (acompose F a b c g f) =
acompose F a b d (acompose F b c d h g) f.
Admitted.


#[refine] Instance CoAlgebraCat {C : Category} (F : Functor C C) : Category := 
{
    obj := CoAlgebra F;
    hom := CoAlgebraMorphism;
    idty := aid F;
    compose := acompose F
}.

Proof.
- apply acat_a.
- apply acat_b.
- apply acat_c.
Defined. *)

(* Definition aid {C : Category} (F : Functor C C) 
    (a : CoAlgebra F): CoAlgebraMorphism a a.
    refine ({|f := idty _ |}).
Proof.
    rewrite functors_preserve_identities.
    rewrite compose_left_idty.
    rewrite compose_right_idty.
    reflexivity.
Defined. *)

(* Definition acompose {C : Category} (F : Functor C C) 
    (a b c : CoAlgebra F) : 
        CoAlgebraMorphism b c -> CoAlgebraMorphism a b -> CoAlgebraMorphism a c.
    intros.
        refine ({|f:=compose X X0 |}).
        rewrite <- functors_preserve_composition.
        destruct X, X0.
        simpl.
        rewrite compose_assoc.
        rewrite <- H_f.
        rewrite <- compose_assoc.
        rewrite H_f0.
        rewrite compose_assoc.
        reflexivity.
    Defined.

Lemma acat_a : forall (C : Category) (F : Functor C C) (a b : CoAlgebra F)
(f : CoAlgebraMorphism a b),
acompose F a a b f (aid F a) = f.
Admitted.

Lemma acat_b : forall (C : Category) (F : Functor C C) (a b : CoAlgebra F)
(f : CoAlgebraMorphism a b),
acompose F a b b (aid F b) f = f.
Admitted.

Lemma acat_c : forall (C : Category) (F : Functor C C) (a b c d : CoAlgebra F)
(f : CoAlgebraMorphism a b)
(g : CoAlgebraMorphism b c)
(h : CoAlgebraMorphism c d),
acompose F a c d h (acompose F a b c g f) =
acompose F a b d (acompose F b c d h g) f.
Admitted.


#[refine] Instance CoAlgebraCat {C : Category} (F : Functor C C) : Category := 
{
    obj := CoAlgebra F;
    hom := CoAlgebraMorphism;
    idty := aid F;
    compose := acompose F
}.

Proof.
- apply acat_a.
- apply acat_b.
- apply acat_c.
Defined.  *)