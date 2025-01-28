From Coq.Logic Require Import FunctionalExtensionality.
From Categories.Category Require Import Category Functor.

Open Scope type_scope.

(** Category *)

#[refine] Instance Typ  : Category :=
    {
        obj := Type;
        hom := fun A B => A -> B;
        idty := fun (A : Type) (x : A) => x;
        compose := fun (A B C : Type) (g : B -> C) (f : A -> B) x => g (f x)  
    }.
Proof.
    -   intros.
        now apply functional_extensionality.
    -   intros.
        now apply functional_extensionality.
    -   intros.
        now apply functional_extensionality.
Defined.

(** Cartesian category *)

#[refine] Instance prodProduct (a b : Type) : product a b := 
    {
        product_obj := a * b;
        π₁ := fst;
        π₂ := snd;
        product_morph := fun c f g (x : c) => (f x, g x)
    }.
Proof.
    -   intros c f g.
        split;
            apply functional_extensionality; reflexivity.
    -   intros c f g h Ha.
        destruct Ha as [Ha Hb].
        rewrite Ha, Hb; simpl.
        apply functional_extensionality.
        intro x.
        rewrite <- surjective_pairing.
        reflexivity.
Defined.

Instance CartesianType  : Cartesian := {}.


(** Cartesian Closed Category *)

#[refine] Instance singleton_terminal : terminal := 
{
    terminal_obj := unit;
    terminal_morph := fun _ _ => tt
}.
Proof.
    intros h f.
    apply functional_extensionality; intro x.
    destruct (f x); reflexivity.
Defined.

(* exponential_obj *)

#[refine] Instance ExponentialType (a b : obj) : Exponential a b := 
{
    exponential_obj := a -> b;
    eval := fun p => (fst p) (snd p)
}.
Proof.
    intros.
    exists (fun f => fun x => g (f,x)).
    split.
    +   apply functional_extensionality; simpl.
        destruct x; reflexivity.
    +   intros.
        rewrite H; simpl.
        apply functional_extensionality.
        intro f.
        apply functional_extensionality.
        reflexivity.
Defined.

Instance CartesianClosedType : CartesianClosed := {}.

(** Bicartesian closed category *)

#[refine] Instance empty_initial : initial :=
{
    initial_obj := Empty_set;
    initial_morph := 
        fun b => fun (x : Empty_set) => match x with end 
}.
Proof.
    intros.
    apply functional_extensionality.
    destruct x.
Defined.

#[refine] Instance sumCoproduct (a b : Type) : coproduct a b := 
    {
        co_product_obj := sum a b;
        ι₁ := inl;
        ι₂ := inr;
        coproduct_morph := fun c f g (x : a + b) => 
            match x with 
                | inl y => f y 
                | inr y => g y 
            end
    }.
Proof.
    -   intros c f g.
        split;
        apply functional_extensionality;
        reflexivity.
    -   intros c f g h Ha.
        destruct Ha as [Ha Hb].
        rewrite Ha, Hb; simpl.
        apply functional_extensionality.
        destruct x; reflexivity.
Defined.

Instance BiCartesianClosedType : BiCartesianClosed :={}.


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