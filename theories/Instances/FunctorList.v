From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Lists Require Import List.
From Categories.Category Require Import Category Functor.
From Categories.Instances Require Import CategoryType.

#[export] Instance FunctorList : Functor CategoryType CategoryType.
refine ({|
    fobj := list;
    fmap := List.map
|}).
Proof.
    -   intro A.
        apply functional_extensionality.
        apply map_id.
    -   intros A B C g h.
        apply functional_extensionality; intro x.
        simpl; rewrite map_map.
        reflexivity.
Defined.

Check (FunctorList : Cat CategoryType CategoryType).