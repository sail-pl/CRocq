From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.
From Coq.Setoids Require Import Setoid.

From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Algebra.
From Categories.Instances Require Import CategoryType.
From Categories.Instances Require Import CategoryAlgebra.
From Categories.Types Require Import Data.

(* We define the endofunctor [Fₙ] over the category of types as 
    F X = 1 + X *)

Instance Fₙ : Functor Typ Typ := FunctorSum unit.

(* We define the Fₙ-algebra [nat_algebra] and prove that it is an
    initial Fₙ-algebra, i.e. it is an initial object for the category of Fₙ-algebra *)

Instance nat_Algebra : Algebra Fₙ  := 
{
    a_u := nat;
    constr p := match p with inl _ => 0 | inr n => S n end
}.

Definition nat_to_algebra (B : Algebra Fₙ) : Typ (a_u nat_Algebra) (a_u B) :=
    fix f n := match n with 0 => constr _ (inl tt) 
        | S n => constr _ (inr (f n)) end.    
  
Definition nat_to_algebra_m (B : Algebra Fₙ) : AlgebraMorphism nat_Algebra B.
    refine ({|
        f := nat_to_algebra B
    |}).
Proof.
    apply functional_extensionality; intro x.
    destruct x; simpl.
    -   destruct u; reflexivity.
    -   reflexivity.
Defined.

#[refine] Instance initial_ : initial (AlgebraCat Fₙ) nat_Algebra := 
{
    umorph := nat_to_algebra_m
}.
Proof.
    intros b h'.
    destruct h' as [f H_f].
    assert (nat_to_algebra b = f).
    {
        apply functional_extensionality.
        intro x.
        induction x.
        -   generalize (equal_f H_f (inl tt)); intro; simpl in *.
            assumption.
        -   generalize (equal_f H_f (inr x)); intro; simpl in *.
            congruence.
    }
    subst.
    unfold nat_to_algebra_m; simpl.
    f_equal.
    apply proof_irrelevance.
Defined.