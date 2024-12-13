From Coq.Logic Require Import FunctionalExtensionality.
(* From reactive.utils Require Import Notations. *)
From Categories.Category Require Import Category Functor.


Instance TypeCat  : Category.
    refine (
        {|
        obj := Type;
        hom := fun A B => A -> B;
        idty := fun (A : Type) (x : A) => x;
        compose := fun (A B C : Type) (g : B -> C) (f : A -> B) x => g (f x)  
        |}
    ).
    Proof.
    -   intros.
        now apply functional_extensionality.
    -   intros.
        now apply functional_extensionality.
    -   intros.
        now apply functional_extensionality.
Defined.

Lemma empty_initial : @initial TypeCat Empty_set.
Proof.
    intro o.
    exists (fun (e : Empty_set) => match e with end).
    intro h'.
    apply functional_extensionality; intro x.
    destruct x.
Qed.

Lemma singleton_final : @final TypeCat unit.
    intro o.
    exists (fun _ => tt).
    intro h.
    apply functional_extensionality; intro x.
    destruct (h x).
    reflexivity.
Qed.

