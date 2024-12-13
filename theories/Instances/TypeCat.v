From Coq.Logic Require Import FunctionalExtensionality.
From Categories.Category Require Import Category Functor.

Instance TypeCat  : Category.
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

Lemma empty_initial : initial TypeCat Empty_set.
Proof.
    intro o.
    exists (fun (e : Empty_set) => match e with end).
    intro h'.
    apply functional_extensionality; intro x.
    destruct x.
Qed.

Lemma singleton_terminal : terminal TypeCat unit.
    intro o.
    exists (fun _ => tt).
    intro h.
    apply functional_extensionality; intro x.
    destruct (h x).
    reflexivity.
Qed.

Open Scope type_scope.

#[refine] Instance prodProduct (a b : Type): 
    product TypeCat a b (a * b) := 
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
    coproduct TypeCat a b (a + b) := 
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


