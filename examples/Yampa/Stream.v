From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.
From Coq.Setoids Require Import Setoid.

From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Coalgebra.
From Categories.Algebra Require Import CatCoalgebra.

Import -(coercions) Coalgebra.

From Categories.Embedding Require Import CategoryType.

Declare Scope stream_scope.

Open Scope stream_scope.
Open Scope type_scope.

(* preliminary *)

Lemma coalgebra_morphism_pi : forall
    {F : Functor Typ Typ} {a b: CoAlgebra F}
        (f g :  CoAlgebraMorphism F a b),
            @coalgebramorphism_morph Typ F a b f = 
            @coalgebramorphism_morph Typ F a b g -> 
                f = g.
Proof.
    intros F a b f g HEq.
    unfold coalgebramorphism_morph in HEq.
    destruct f, g.
    revert H_f H_f0; rewrite HEq; intros.
    assert (H_f = H_f0) as HEq2 by
        apply proof_irrelevance.
    rewrite HEq2.
    reflexivity.
Qed.

    (* Lemma coalgebra_morphism_pi : forall (a: CoAlgebra Fₛ)
    (f g :  CoAlgebraMorphism Fₛ a CoAlgebraStream),
    @coalgebramorphism_morph Typ Fₛ a CoAlgebraStream f = 
        @coalgebramorphism_morph Typ Fₛ a CoAlgebraStream g -> 
            f = g.
    Proof.
        intros a f g HEq.
        unfold coalgebramorphism_morph in HEq.
        destruct f, g.
        revert H_f H_f0; rewrite HEq; intros.
        assert (H_f = H_f0) as HEq2 by
            apply proof_irrelevance.
        rewrite HEq2.
        reflexivity.
    Qed. *)

(** Definition of streams *)
(** Type of streams *)
(* besoin de la bisimulation *)

CoInductive stream (A : Type) : Type :=
    str : A -> stream A -> stream A.

Arguments str [A].

Infix "⋅" := str (at level 60, right associativity): stream_scope.    

Definition decompose {A : Type} (s : stream A) : stream A :=
match s with str a s => str a s end.

Lemma decomposeEq : 
    forall (A : Type) (s : stream A), s = decompose s.
Proof.
    destruct s; reflexivity.
Qed.


Section CoAlgebra.

    Variable (A : Type).

    #[global] Instance Fₛ : Functor Typ Typ := 
        FRProduct A.

    #[global] Instance CoAlgebraStream : 
        CoAlgebra Fₛ  := 
        {
            coalgebra_obj := stream A;
            coalgebra_morph := 
                fun p => match p with 
                    str a t => (a,t) end
        }.

    CoFixpoint iterate {X : Type} 
        (step : X -> A * X) (x : X) : stream A := 
        let (a,x') := step x in
            str a (iterate step x').

     #[refine] Instance G (X : CoAlgebra Fₛ) : 
            CoAlgebraMorphism Fₛ X CoAlgebraStream :=
        {
            coalgebramorphism_morph := 
                iterate (coalgebra_morph X)
        }.
    Proof.
        simpl.
        extensionality x.
        destruct (coalgebra_morph X x) as [a x'].
        reflexivity.
    Defined.

    Lemma b : forall (X : Type)
    (stepX : X -> A * X)
    (f : X -> stream A), 
    (* X is the carrier of a coalgebra *)
    (* f is a coalgebra morphism *)
    f = iterate stepX.
    Proof.
        intros.
        extensionality x.
        rewrite decomposeEq; simpl.
        case_eq (f x); intros.
        case_eq (stepX x); intros.
        (* unfold iterate. *)
    Admitted.


    #[refine] Instance TerminalCoRec 
        : Terminal (CoAlgebraCat Fₛ) := 
    {
        term_obj := CoAlgebraStream;
        term_morph := G 
    }.
    Proof.
        intros a h.
        simpl in *.
        destruct a as [X stepX].
        destruct h; simpl in *.
        unfold G; simpl.
        assert (coalgebramorphism_morph =
            iterate stepX).
        {
            apply b.
        }
        apply coalgebra_morphism_pi.
        apply H.
    Qed.

End CoAlgebra.
  
Definition hd {A : Type} : stream A -> A := 
    fst ∘ (coalgebra_morph (CoAlgebraStream A)).

Definition tl {A : Type} : stream A -> stream A := 
    snd ∘ (coalgebra_morph (CoAlgebraStream A)). 

Lemma surjective_str : 
    forall (A : Type) (s : stream A), hd s ⋅ tl s = s.
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

(* Infix "∼" := bisimilar (at level 60, right associativity): stream_scope.  *)

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

Arguments bisimulation [A].

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
