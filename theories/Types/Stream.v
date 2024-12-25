From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Setoids Require Import Setoid.

From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Coalgebra.
From Categories.Instances Require Import CategoryType.
From Categories.Instances Require Import CategoryCoAlgebra.

(* From Categories.Types *)
Require Import Data.

Declare Scope stream_scope.

Open Scope stream_scope.
Open Scope type_scope.

(** Definition of streams *)
(** Type of streams *)

CoInductive stream (A : Type) : Type :=
    str : A -> stream A -> stream A.

Arguments str [A].

Infix "⋅" := str (at level 60, right associativity): stream_scope.    

(** CoAlgebra *)

(* Endofunctor (F A) X = unit + A * X *)
    
Instance Fₛ (A : Type) : Functor Typ Typ := FunctorProduct A.

Instance stream_CoAlgebra ( A : Type ) : CoAlgebra (Fₛ A) := 
{
    ca_u := stream A;
    destr := fun p => match p with str a t => (a,t) end
}.

#[refine] Instance T (A : Type) : 
    initial (CoAlgebraCat (Fₛ A)) (stream_CoAlgebra A) := {}.
Proof.
    intros.
Admitted.

Definition hd {A : Type} : stream A -> A := fst ∘ (destr (stream_CoAlgebra A)).

Definition tl {A : Type} : stream A -> stream A := snd ∘ (destr (stream_CoAlgebra A)). 

Lemma surjective_str : 
    forall (A : Type) (s : stream A), hd s ⋅ tl s = s.
Proof.
    destruct s; reflexivity.
Qed.

Definition decompose {A : Type} (s : stream A) : stream A :=
    match s with str a s => str a s end.

Lemma decomposeEq : 
    forall (A : Type) (s : stream A), s = decompose s.
Proof.
    destruct s; reflexivity.
Qed.

Section Bisimilarity.

    Variable A : Type.

    CoInductive bisimilar : stream A -> stream A -> Prop :=
        bisimilar_str : forall s1 s2,
            hd s1 = hd s2 ->
            bisimilar (tl s1) (tl s2) ->
            bisimilar s1 s2.

    Infix "∼" := bisimilar (at level 60, right associativity).
    
    Lemma bisimilar_refl : 
        forall (s : stream A), bisimilar s s.
    Proof.
        cofix Ha.
        constructor.
        -   reflexivity.
        -   exact (Ha (tl s)).
    Qed.

    Lemma bisimilar_sym : 
        forall (s1 s2 : stream A), 
        bisimilar s1 s2 -> bisimilar s2 s1.
    Proof.
        cofix Ha.
        intros s1 s2 Hb.
        destruct Hb as [? ? Hb Hc].
        constructor.
        -   congruence.
        -   exact (Ha _ _ Hc).
    Qed.

    Lemma bisimilar_trans : 
    forall (s1 s2 s3 : stream A),
        bisimilar s1 s2 ->
        bisimilar s2 s3 ->
        bisimilar s1 s3.
Proof.
    cofix Ha.
    intros s1 s2 s3 Hb Hc.
    destruct Hb as [? ? Hd He].
    destruct Hc as [? ? Hf Hg].
    constructor.
    -   congruence.
    -   exact (Ha _ _ _ He Hg).
Qed.   

End Bisimilarity.

Infix "∼" := bisimilar (at level 60, right associativity): stream_scope. 

Section Bisimulation.

    Variable A : Type.

    Record bisimulation (R : relation (stream A)) : Prop :=
        {
            bisim_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2;
            bisim_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2)
        }.

    Hypothesis R : relation (stream A).
    Hypothesis RBisim : bisimulation R.

    Theorem bisimulation_gfp : 
        forall s1 s2, R s1 s2 -> bisimilar _ s1 s2.
    Proof.
        cofix HInd.
        intros s1 s2 H_R.
        constructor.
        -   exact (bisim_hd R RBisim s1 s2 H_R).
        -   assert (R (tl s1) (tl s2)) as H_Rtl by
                exact (bisim_tl R RBisim s1 s2 H_R).
            exact (HInd (tl s1) (tl s2) H_Rtl).
    Qed.

End Bisimulation.

(** * Morphisms *)

Add Parametric Relation A : (stream A) (@bisimilar A)
    reflexivity proved by (bisimilar_refl A)
    symmetry proved by (bisimilar_sym A)
    transitivity proved by (bisimilar_trans A)
    as bisimilar_rel.

Add Parametric Morphism A : (@hd A)
    with signature (@bisimilar A) ==> (@eq A) as hd_mor.
Proof.
    intros x y [Ha]; assumption.
Qed.

Add Parametric Morphism A : (@tl A)
    with signature (@bisimilar A) ==> (@bisimilar A) as tl_mor.
Proof.
    intros x y [Ha]; assumption.
Qed.

Add Parametric Morphism A : (@str A)
    with signature (@eq A) ==> (@bisimilar A) ==> (@bisimilar A) as str_mor.
Proof.
    intros x s1 s2 H_Eq.
    constructor.
    reflexivity.
    replace (tl (str x s1)) with s1 by reflexivity.
    replace (tl (str x s2)) with s2 by reflexivity.
    exact H_Eq.
Qed.

(** ** Positions *)

Fixpoint nth_stream {A : Type} (s : stream A) (n : nat) : A :=
    match n with 0 => hd s | S n => nth_stream (tl s) n end.

Lemma same_elements_eq_str : 
    forall (A : Type) (s1 s2 : stream A),
        (forall i, nth_stream s1 i = nth_stream s2 i) -> bisimilar _ s1 s2.
Proof.
    cofix H; intros.
    constructor.    
    -   generalize (H0 0); intro.
        destruct s1, s2.
        apply H1.    
    -   assert (forall i : nat, 
                nth_stream (tl s1) i = nth_stream (tl s2) i).
        intro i.
        generalize (H0 (S i)); intro.
        destruct s1, s2.
        apply H1.
        apply H.
        apply H1.
Qed.

Lemma eq_str_same_elements : 
forall (A : Type) (s1 s2 : stream A),
    bisimilar _ s1 s2 -> (forall i, nth_stream s1 i = nth_stream s2 i).
Proof.
intros A s1 s2 H_bsim i.
revert s1 s2 H_bsim.
induction i; intros s1 s2 H_bsim.
-   inversion H_bsim as [? ? Hhd _]; subst.
    destruct s1, s2.
    exact Hhd.
-   inversion H_bsim as [ ? ? _ Htl]; subst.
    destruct s1, s2.
    exact (IHi _ _ Htl).
Qed.

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