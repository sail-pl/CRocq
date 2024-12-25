From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.

From Categories.Category Require Import Category Functor Transformation.

(* Must prove *)

Print Instances Category.

Parameter C : Category.
Definition a := @idty Cat C.
Check (a : Functor C C).
Check (a : @obj (CategoryFunctor C C)).

Parameter T : CategoryFunctor C C.
(* Parameter μ : NaturalTransformation ((T : Cat C C ) ∘ T) T. *)
Parameter μ : CategoryFunctor C C ((T : Cat C C ) ∘ T) T.

Check (μ : CategoryFunctor C C ((T : Cat C C ) ∘ T) T).
(* Check (fmap T μ). : Problem here, μ : C _ _ *)

Definition T2 (C : Category) (T : Functor C C) : Functor C C :=
        (T : Cat C C) ∘ T.

Definition T3 (C : Category) (T : Functor C C) : Functor C C :=
        (T : Cat C C) ∘ (T2 C T).

(* Definition FF 
    (C : Category)
    (T : CategoryFunctor C C) 
    (μ : NaturalTransformation (T2 C T) T) : 
    NaturalTransformation (T3 C T) T.
refine ({|
    transform := fun c => fobj (T : Functor C C) (μ c);
    transform_spec := _
|}).
Proof.
    - intros a b f. *)

(* Class Monad {C : Category} : Type := {
    T : CategoryFunctor C C;
    η : CategoryFunctor C C (@idty Cat C : Functor C C) T;
    (* μ : NaturalTransformation ((T : Cat C C ) ∘ T) T; *)
    μ : CategoryFunctor C C ((T : Cat C C ) ∘ T) T;
    monad_spec1 : 
        (fmap T μ ∘ μ) = (fmap T μ ∘ μ)
}. *)
