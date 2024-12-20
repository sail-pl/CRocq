From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.

From Categories.Category Require Import Category.

(** * Functor *)
(** ** Definition *)
(** 
  A functor [F : Functor C D] is a mapping between the categories [C] and [D]. 
  - each object [a : C] is mapped to an object [fobj F a : D] and 
  - each morphism [f : C a b] is mapped to  a morphism [fmap F f : C (F a) (F b)] 
  This mapping must preserve identities and composition.
  The object mapping [fobj F a] is denoted by [F a].
  *)

Class Functor (C : Category) (D : Category) : Type := {
  fobj : C -> D;
  fmap {a b : C} : C a b -> D (fobj a) (fobj b);
  functors_preserve_identities {a : C} : 
    fmap (idty a) = idty (fobj a);
  functors_preserve_composition {a b c : C} : 
      forall (g : C b c) (h : C a b),
        (fmap g ∘ fmap h) = fmap (g ∘ h) }.

Arguments fmap { _ _ } Functor { _ _ }.

Coercion fobj : Functor >-> Funclass.

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

(** ** Adjonctions *)
(** An adjunction between two categories [C] and [D] is a pair 
  of functors [F : Cat C D] and [G : Cat D C] together with a natural
  transformation [iso : NaturalTransformation (idty C) (G ∘ f)]
  *)
(* Definition Adjunction {C D : Cat} (F : Cat C D) (G : Cat D C) 
  (η : NaturalTransformation (idty C) (G ∘ F)) : Type := 
    forall (x : C) (y : D) (f : C x (G y)),
    exists! (g : D (F x) y), f = (fmap G g) ∘ (η x). *)


