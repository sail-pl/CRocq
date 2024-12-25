From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Setoids Require Import Setoid.

From Categories.Category Require Import Category Functor.
From Categories.Instances Require Import CategoryType.
From Categories.Algebra Require Import Coalgebra.

(** Unit *)

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

#[refine] Instance FunctorProduct (A : Type): Functor Typ Typ :=
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