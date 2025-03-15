From Coq.Logic Require Import ProofIrrelevance.
From Coq.Logic Require Import FunctionalExtensionality.

From Categories.Category Require Import Category Functor.

(** ** Natural transformations *)
(** A natural transformation between two functors [F G : Functor C D] for two
  categories [C] and [D] is a mapping from each object [a:C] to a a morphism
  [transform a : D (F a) (G a)] *)

Section Category.

    Context {C D : Category}.

    Record Transformation (F G : Functor C D) : Type := {
        transform (a : C) : D (F a) (G a);
        transform_spec : forall (a b : C) (f : C a b),
            (fmap G f) ∘ (transform a) = 
                (transform b)∘ (fmap F f) }.

    Coercion transform : Transformation >-> Funclass.

    Definition nf_idty (F : Functor C D) : Transformation F F.
        refine ({| 
            transform := fun (c : C) => id (F c) ; 
            transform_spec := _ |}).
    Proof.
        intros a b f.
        rewrite cat_left_idty.
        rewrite cat_right_idty.
        reflexivity. 
    Defined.

    Definition nf_compose (F G H : Functor C D)
        (N : Transformation G H) (M : Transformation F G) : 
            Transformation F H.
        refine {| 
            transform := fun (c : C) => N c ∘ M c;
            transform_spec := _ |}.
    Proof.
        intros a b f.
        destruct N, M; simpl.
        rewrite cat_assoc.
        rewrite transform_spec0.
        rewrite <- cat_assoc.
        rewrite transform_spec1.
        rewrite <- cat_assoc.
        reflexivity.
    Defined.

    Lemma transform_eq : 
        forall (F G : Functor C D) (f f' : Transformation F G),
            transform F G f = transform F G f' -> f = f'.
    Admitted.

    Require Import Setoid.
    Lemma a : forall (F G : Functor C D) (f : Transformation F G), 
        nf_compose F F G f (nf_idty F) = f.
    Proof.
        intros F G f.
        destruct f; simpl.
        unfold nf_compose, nf_idty; simpl.
        assert ((fun c => transform0 c ∘ id (F c)) = transform0).
        {
            simpl.
            assert ((fun c => transform0 c ∘ id (F c)) = fun c => transform0 c).
            {
                apply functional_extensionality_dep.
                intro c.
                rewrite cat_left_idty.
                reflexivity.
            }
            rewrite H.
            reflexivity.
        }
        apply transform_eq.
        apply H.
    Qed.
    

        (* set (f := fun c : C => transform0 c ∘ id (F c)).
        revert transform_spec0.
        rewrite <- H.  *)

        (* revert transform_spec0.
        rewrite <- H.  *
        apply proof_irrelevance. *)
    Admitted. 

Lemma b : forall (C D : Category) (F G : Functor C D) (f : Transformation F G),
nf_compose F G G (nf_idty G) f = f.
Proof.
Admitted.

Lemma c : forall (C D: Category) (F G H I : Functor C D) 
    (f : Transformation F G) (g : Transformation G H)
    (h : Transformation H I),
    nf_compose _ _ _ h
    (nf_compose _ _ _ g f) =
    nf_compose _ _ _ 
    (nf_compose _ _ _ h g) f.
Proof.
Admitted.

#[refine, export] Instance CategoryFunctor (C D : Category) : Category := {
    obj := Functor C D;
    hom := Transformation;
    id := nf_idty;
    compose := nf_compose
}.
Proof.
    - apply a.
    - apply b.
    - apply c.
Defined.