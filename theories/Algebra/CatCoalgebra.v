From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.
From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Coalgebra.

(* morphisms are simply morphism of the category *)

Section Category.

    Context {C : Category}.

    Definition id_ca {F : Functor C C} (f : CoAlgebra F) : CoAlgebraMorphism F f f.
    Proof.
        refine ({|coalgebramorphism_morph := id (coalgebra_obj f)|}).
        rewrite funct_preserves_identities.
        rewrite cat_left_idty.
        rewrite cat_right_idty.
        reflexivity.
    Defined.

    Definition compose_ca {F : Functor C C} (f g h : CoAlgebra F) : 
        CoAlgebraMorphism F g h -> CoAlgebraMorphism F f g -> CoAlgebraMorphism F f h.
    Proof.
        intros .
        refine ({|coalgebramorphism_morph := compose X X0 |}).
        rewrite <- funct_preserves_composition.
        destruct X, X0.
        simpl.
        rewrite cat_assoc.
        rewrite <- H_f.
        rewrite <- cat_assoc.
        rewrite H_f0.
        rewrite cat_assoc.
        reflexivity.
    Defined.

    Lemma acat_a : forall (F : Functor C C) (f g : CoAlgebra F) 
            (h : CoAlgebraMorphism F f g),
                compose_ca _ _ _ h (id_ca f) = h.
    Admitted.

    Lemma acat_b : forall (F : Functor C C)(f g : CoAlgebra F) 
            (h : CoAlgebraMorphism F f g),
                compose_ca _ _ _ (id_ca g) h = h.
    Admitted.

    Lemma acat_c : forall 
        (F : Functor C C)
        (f_a f_b f_c f_d : CoAlgebra F) 
        (f : CoAlgebraMorphism F f_a f_b)
        (g : CoAlgebraMorphism F f_b f_c)
        (h : CoAlgebraMorphism F f_c f_d),
            compose_ca _ _ _ h (compose_ca _ _ _ g f) =
                compose_ca _ _ _ (compose_ca _ _ _ h g) f.
    Admitted.

#[refine] Instance CoAlgebraCat (F : Functor C C) : Category := 
{
    obj := CoAlgebra F;
    hom := CoAlgebraMorphism F;
    id := id_ca ;
    compose := compose_ca
}.
Proof.
- apply acat_a.
- apply acat_b.
- apply acat_c.
Defined.

End Category.