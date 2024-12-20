From Coq.Logic Require Import FunctionalExtensionality.
From Categories.Category Require Import Category Functor Transformation.
From Categories.Instances Require Import CategoryType FunctorList FunctorOption.

(* #[refine] Instance TransformationListOption : NaturalTransformation FunctorList FunctorOption :=
{
    transform (a : CategoryType) := 
        fun l => match l with 
            nil => None | cons x l => Some x end
}.
Proof.
    intros a b f.
    apply functional_extensionality; intros [ | ]; reflexivity.
Defined. *)

  