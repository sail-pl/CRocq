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

#[refine] Instance prodProduct (a b : Type) : product Typ a b (a * b) := 
    {
        π₁ := fst;
        π₂ := snd;
        pair_f := fun c f g (x : c) => (f x, g x)
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

Instance CartesianType  : Cartesian :=
{
    product_obj := fun A B => A * B
}.

(** Cartesian Closed Category *)

#[refine] Instance singleton_terminal : terminal Typ unit := 
{
    vmorph := fun _ _ => tt
}.
Proof.
    intros h f.
    apply functional_extensionality; intro x.
    destruct (f x); reflexivity.
Defined.

#[refine] Instance ExponentialType : Exponential (hom) := 
{
    eval := fun A B => fun p => (fst p) (snd p)
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
Qed.

#[refine] Instance CartesianClosedType : CartesianClosed :=
{
    term := unit;
    exp := fun A B => A -> B;
}.

(** Bicartesian closed category *)

#[refine] Instance empty_initial : initial Typ Empty_set :=
{
    umorph := fun b => fun (x : Empty_set) => match x with end 
}.
Proof.
    intros.
    apply functional_extensionality.
    destruct x.
Defined.

#[refine] Instance sumCoproduct (a b : Type) : coproduct Typ a b (a + b) := 
    {
        ι₁ := inl;
        ι₂ := inr;
        copair_f := fun c f g (x : a + b) => 
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

#[refine] Instance BiCartesianClosedType : BiCartesianClosed :=
{
  init := Empty_set;  
  co_product_obj := sum;
}.
