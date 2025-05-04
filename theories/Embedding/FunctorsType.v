From Stdlib.Logic Require Import FunctionalExtensionality.
From Stdlib.Lists Require Import List.
From CRocq.Category Require Import Category Functor.
From CRocq.Embedding Require Import CategoryType.


#[refine] Instance FunctorConstant (A : Type) : Functor Typ Typ :=
{
    fobj := fun _ => A;
    fmap := fun B C f p => p
}.
Proof.
    -   intro a.
        apply functional_extensionality.
        reflexivity.
    -   intros.
        apply functional_extensionality.
        reflexivity.
Defined.   

(** Pairs *)

Definition fmap_product {A B C : Type} 
    (f : B -> C) (p : A * B) : A * C := (fst p, f (snd p)).

#[refine] Instance FProduct (A : Type): Functor Typ Typ :=
{
    fobj := fun B => A * B;
    fmap := fun B C f (p : A * B) => 
        match p with (x,y) => (x, f y) end
}.
Proof.
    - intro; apply functional_extensionality; 
        intros [  ]; reflexivity.  
    - intros; apply functional_extensionality; 
        intros [  ]; reflexivity.  
Defined.
        
#[refine] Instance FunctorSum (A : Type) : Functor Typ Typ :=
{
    fobj := fun B => A + B;
    fmap := fun B C f (p : A + B) => 
    match p with 
    | inl x => inl x 
    | inr x => inr (f x)
    end
}.
Proof.
    - intro; apply functional_extensionality; 
        intros [  ]; reflexivity.  
    - intros. apply functional_extensionality;
        intros [  ]; reflexivity.
Defined.

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

#[export] Instance FunctorList : Functor Typ Typ.
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