From Coq.Logic Require Import FunctionalExtensionality.
From Categories.Category Require Import Category Functor.
From Categories.Instances Require Import CategoryType.

#[export] Instance FunctorOption : Functor Typ Typ.
refine ({|
    fobj := option;
    fmap := option_map
|}).
Proof.
    -   intro.
        apply functional_extensionality; intros [ | ]; reflexivity.
    -   intros.
        apply functional_extensionality; intros [ | ]; reflexivity.
Defined.
