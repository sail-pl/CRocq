From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.
From Categories.Category Require Import Category Functor.
(** Functors are morphisms for categories *)

#[refine] Instance FunctorId (C : Category) : Functor C C :=
  {
    fobj := fun x => x;
    fmap := fun A B f => f  
  }.
Proof.
  - reflexivity.
  - reflexivity.
Defined.

(* instance ??? *)
Definition FunctorComp {C1 C2 C3 : Category}
    (G : Functor C2 C3) (F : Functor C1 C2)  : 
    Functor C1 C3.
refine ({|
    fobj := fun (x : @obj C1) => (G (F x));
    fmap := fun (A B : @obj C1) (f : @hom C1 A B) =>
                fmap (fmap f)
|}).
Proof.
    -   intros.
        do 2 rewrite fmap_identity; reflexivity.
    -   intros.
        do 2 rewrite fmap_compose; reflexivity.
Defined.

#[refine] Instance CategoryCat : Category :=
{
    obj := Category;
    hom := Functor;
    idty := FunctorId;
    compose := @FunctorComp
}.
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
