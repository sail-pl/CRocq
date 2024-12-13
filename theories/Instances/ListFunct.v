
From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Lists Require Import List.
From Categories.Category Require Import Category Functor.
From Categories.Instances Require Import TypeCat.


Lemma map_id : forall (A : Type) (x : list A), List.map (fun x => x) x = x.
Proof.
    intros A x.
    induction x.
    -   reflexivity.
    -   simpl; rewrite IHx.
        reflexivity.
Qed.

#[export] Instance ListFun : Functor TypeCat TypeCat.
refine ({|
    fobj := list;
    fmap := List.map
|}).
Proof.
    -   intro A.
        apply functional_extensionality.
        apply map_id.
    -   intros A B C g h.
        apply functional_extensionality.
        simpl.
        intro x.
        rewrite map_map.
        reflexivity.
Qed.