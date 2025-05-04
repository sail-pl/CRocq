From Stdlib.Logic Require Import FunctionalExtensionality.
From Stdlib.Logic Require Import ProofIrrelevance.
From CRocq.Category Require Import Category Functor.


(** ** The category of small categories *)
(** We can form the Cat category whose objects are small categories  
    and morphisms are functors. *)

#[refine] Instance FunctorId (C : Category) : Functor C C := {
  fobj := fun x => x;
  fmap := fun A B f => f }.
Proof.
  - reflexivity.
  - reflexivity.
Defined.

#[refine] Instance FunctorComp (C D E : Category)
  (G : Functor D E) (F : Functor C D)  : Functor C E := {
    fobj := fun (x : C) => (G (F x));
    fmap := fun (a b : C) (f : C a b) => fmap G (fmap F f) }.
Proof.
    -   intros.
        do 2 rewrite functors_preserve_identities; reflexivity.
    -   intros.
        do 2 rewrite functors_preserve_composition; reflexivity.
Defined.

#[refine] Instance Cat : Category := {
    obj := Category;
    hom := Functor;
    idty := FunctorId;
    compose := FunctorComp }.
Proof.
    - destruct f.
      unfold FunctorId, FunctorComp.
      f_equal.
      + apply proof_irrelevance.
      + apply proof_irrelevance.
    - destruct f.
      unfold FunctorId, FunctorComp.
      f_equal.
      + apply proof_irrelevance.
      + apply proof_irrelevance.
    - destruct f, g, h.
      unfold FunctorComp; simpl.
      f_equal.
      + apply proof_irrelevance.
      + apply proof_irrelevance.
Defined.

