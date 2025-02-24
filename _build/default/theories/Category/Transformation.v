From Coq.Logic Require Import ProofIrrelevance.

From Categories.Category Require Import Category Functor.

(** ** Natural transformations *)
(** A natural transformation between two functors [F G : Functor C D] for two
  categories [C] and [D] is a mapping from each object [a:C] to a a morphism
  [transform a : D (F a) (G a)] *)

Record NaturalTransformation {C D : Category} (F G : Functor C D) : Type := {
transform (a : C) : D (F a) (G a);
transform_spec : forall (a b : C) (f : C a b),
    (fmap G f) ∘ (transform a) = (transform b)∘ (fmap F f) }.

Coercion transform : NaturalTransformation >-> Funclass.

Definition nf_idty {C D : Category} (F : Functor C D) : NaturalTransformation F F.
refine ({| transform := fun (c : C) => idty (F c) ; transform_spec := _ |}).
Proof.
    intros a b f.
    rewrite compose_left_idty.
    rewrite compose_right_idty.
    reflexivity. 
Qed.

Definition nf_compose {C D : Category} (F G H : Functor C D)
    (N : NaturalTransformation G H) (M : NaturalTransformation F G) : 
        NaturalTransformation F H.
    refine {| 
        transform := fun (c : C) => N c ∘ M c
    ; transform_spec := _ |}.
Proof.
    intros a b f.
    destruct N, M; simpl.
    rewrite compose_assoc.
    rewrite transform_spec0.
    rewrite <- compose_assoc.
    rewrite transform_spec1.
    rewrite <- compose_assoc.
    reflexivity.
Defined.

Lemma a : forall (C D : Category) (F G : Functor C D) (f : NaturalTransformation F G), 
    nf_compose F F G f (nf_idty F) = f.
Proof.
Admitted. 

Lemma b : forall (C D : Category) (F G : Functor C D) (f : NaturalTransformation F G),
nf_compose F G G (nf_idty G) f = f.
Proof.
Admitted.

Lemma c : forall (C D: Category) (F G H I : Functor C D) 
    (f : NaturalTransformation F G) (g : NaturalTransformation G H)
    (h : NaturalTransformation H I),
    nf_compose _ _ _ h
    (nf_compose _ _ _ g f) =
    nf_compose _ _ _ 
    (nf_compose _ _ _ h g) f.
Proof.
Admitted.


#[refine, export] Instance CategoryFunctor (C D : Category) : Category := {
    obj := Functor C D;
    hom := NaturalTransformation;
    idty := nf_idty;
    compose := nf_compose
}.
Proof.
    - apply a.
    - apply b.
    - apply c.
Defined.