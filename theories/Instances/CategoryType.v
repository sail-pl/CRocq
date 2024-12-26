From Coq.Logic Require Import FunctionalExtensionality.
From Categories.Category Require Import Category Functor.

Instance Typ  : Category.
    refine (
        {|
        obj := Type;
        hom := fun A B => A -> B;
        idty := fun (A : Type) (x : A) => x;
        compose := fun (A B C : Type) (g : B -> C) (f : A -> B) x => g (f x)  
        |}
    ).
    Proof.
    -   intros.
        now apply functional_extensionality.
    -   intros.
        now apply functional_extensionality.
    -   intros.
        now apply functional_extensionality.
Defined.

#[refine] Instance empty_initial : initial Typ Empty_set :=
{
    umorph := fun b => fun (x : Empty_set) => match x with end 
}.
Proof.
    intros.
    apply functional_extensionality.
    destruct x.
Defined.

Lemma singleton_terminal : terminal Typ unit.
    intro o.
    exists (fun _ => tt).
    intro h.
    apply functional_extensionality; intro x.
    destruct (h x).
    reflexivity.
Qed.

Open Scope type_scope.

#[refine] Instance prodProduct (a b : Type): 
    product Typ a b (a * b) := 
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

#[refine] Instance sumCoproduct (a b : Type): 
    coproduct Typ a b (a + b) := 
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

(* Category Type Cartesian, Closed *)

Instance CartesianType  : @Cartesian Typ :=
{
    product_obj := fun A B => A * B; 
}.

