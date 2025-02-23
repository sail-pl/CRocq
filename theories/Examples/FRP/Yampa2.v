From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From Coq.Setoids Require Import Setoid.
From Categories.Category Require Import Category Functor CategoryCat.
From Categories.Algebra Require Import Coalgebra.
From Categories.Embedding Require Import CategoryType Arrow.
From Categories.Examples.FRP Require Import Prelim.

Open Scope stream_scope.

Section YampaSemanticsDomain.

    CoInductive sf (A B : Type) := 
        sf_ : (A -> B * sf A B) -> sf A B.

    Arguments sf_ [A B] _.

    (* CoAlgebra *)
    (**********************************************************************)

    Instance CoAlgebrasf (A B : Type) : CoAlgebra (FunctorProc A B) := 
    {
        coalgebra_obj := sf A B;
        coalgebra_morph := fun sf => match sf with sf_ f => f end 
    }.


    (* Category *)
    (**********************************************************************)

    CoFixpoint id (A : Typ) : sf A A :=
        sf_ (fun a => (a, id A)).

    CoFixpoint comp {A B C : Typ} : sf A B -> sf B C -> sf A C :=
        fun '(sf_ f) '(sf_ g) =>
        sf_ (fun a => 
            let (b, f') := f a in
            let (c, g') := g b in
            (c, comp f' g')).

    Definition decompose {A B : Typ} (f : sf A B) : sf A B :=
        match f with sf_ f => sf_ f end.

    Lemma decompose_eq : 
        forall {A B : Typ} (f : sf A B), f = decompose f.
    Proof.
        destruct f; reflexivity.
    Qed.

    Inductive R (A : Type) : relation (sf A A) :=
        | R_1 : R A (id A) (sf_ (fun a => (a, id A)))
        | R_2 : R A (id A) (id A).

    Lemma unroll_id :forall A, id A = sf_ (fun a0 : A => (a0, id A)) .
    Proof.
        intros.
        rewrite decompose_eq at 1; reflexivity.
    Qed.

    Lemma unroll_comp : 
        forall {A B C: Typ} (f : A -> B * sf A B) (g : B -> C * sf B C), 
            comp (sf_ f) (sf_ g) =  sf_ (fun a => 
            let (b, f') := f a in
            let (c, g') := g b in
            (c, comp f' g')).
    Proof.
        intros.
        rewrite decompose_eq at 1. reflexivity.
    Qed.

    #[refine] Instance CategorySF : Category :=
            {
                obj := Typ;
                hom := sf;
                idty := @id;
                compose := fun _ _ _ x y => comp y x
            }.
    Proof.
    -   intros A B [f].
        rewrite unroll_id.
        rewrite unroll_comp.
        f_equal.
        apply functional_extensionality.
        intro x.
        destruct (f x) eqn:Ha.
    Admitted.

    (* Arrow *)
    (**********************************************************************)


    (* co algebra *)
End YampaSemanticsDomain.







