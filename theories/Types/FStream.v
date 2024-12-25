From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Setoids Require Import Setoid.

From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Coalgebra.
From Categories.Instances Require Import CategoryType.
(* From Categories.Types *)
Require Import Data.


Declare Scope stream_scope.

Open Scope stream_scope.
Open Scope type_scope.

(** Definition of streams *)
(** Type of streams *)

CoInductive stream (A : Type) : Type :=
    | nil : stream A 
    | cons : A -> stream A -> stream A.

Arguments cons [A].

Infix "⋅" := cons (at level 60, right associativity): stream_scope.    

(** CoAlgebra *)

(* Cartesian Closed Category *)
(* Ok for CategoryType *)


(* Endofunctor (F A) X = unit + A * X *)
    
#[refine] Instance fstream (A : Type) : Functor Typ Typ := 
    { 
        fobj := (FunctorSum Empty_set : Cat Typ Typ) ∘  FunctorProduct A;
        fmap := fun _ _ => fmap ((FunctorSum Empty_set: Cat Typ Typ) ∘  FunctorProduct A);
    }.
Proof.
    -   intro U.
        rewrite functors_preserve_identities.
        reflexivity.
    -   intros.
        rewrite functors_preserve_composition.
        reflexivity.
Defined.    

(* Definition Fₛ (A : Type)  := fun (X : Type) => unit + A * X. *)

(* try to do the proof with previous instances *)

(* Definition fmap_Fₛ (A : Type) := 
    fun {B C : Type} (f : B -> C) (p : Fₛ A B) => fmap _ f p. *)

(* Definition fmap_Fₛ (A : Type) := 
    fun {B C : Type} (f : B -> C) (p : Fₛ A B) => 
        match p with 
            | inl tt => inl tt 
            | inr p => inr (fst p, f (snd p))
        end.    *)
(*
#[refine] Instance functor_f2 (A : Type) : Functor CategoryType CategoryType := 
    { 
        fobj := Fₛ A;
        fmap := @fmap_Fₛ A;
    }.
Proof.
    -   intro U.
        unfold fmap_Fₛ.
        rewrite functors_preserve_identities.
        reflexivity.
        apply functional_extensionality.
Qed.
*)
(*
Proof.
#[refine] Instance functor_f (A : Type) : Functor (fun A B => A -> B) (fun A B => A -> B) (Fₛ A) := 
        { fmap := fun _ _ f p => (fst p, f (snd p)) }.
    Proof.
        -   intro U.
            apply functional_extensionality.
            intros [a u]; reflexivity.
        -   intros U B C g h.
            apply functional_extensionality.
            intros [a u]; reflexivity.
    Qed.
    
*)
(* Definition fmap_Fₛ (A : Type) := 
    fun {B C : Type} (f : B -> C) (p : Fₛ A B) => (fst p, f (snd p)). *)