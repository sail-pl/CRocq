From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.

(* From reactive.utils Require Import Notations. *)
From Categories.Category Require Import Category.

Unset Automatic Proposition Inductives.

Class Functor (C1 : Category) (C2 : Category) : Type := 
{
  fobj : @obj C1 -> @obj C2;
  fmap : forall {A B : @obj C1}, @hom C1 A B -> @hom C2 (fobj A) (fobj B);
  fmap_identity : forall {A : @obj C1}, 
    fmap (@idty C1 A) = @idty C2 (fobj A);
  fmap_compose : forall {A B C : @obj C1} (g : @hom C1 B C) (h : @hom C1 A B),
    (fmap g ∘ fmap h) = fmap (g ∘ h)
}.

Coercion fobj : Functor >-> Funclass.

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
