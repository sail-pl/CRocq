From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Setoids Require Import Setoid.

From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Coalgebra.
From Categories.Algebra Require Import CategoryCoAlgebra.
From Categories.Algebra Require Import Bisimulation.

From Categories.Embedding Require Import CategoryType.
From Categories.Examples Require Import Stream.
Declare Scope stream_scope.

Open Scope stream_scope.
Open Scope type_scope.

Lemma eq_hd : forall {A : Type} (a : A) s, hd (a ⋅ s) = a.
Admitted.
Lemma eq_tl : forall {A : Type} (a : A) s, tl (a ⋅ s) = s.
Admitted.

Section Bisim.

    Variable A : Type.
    Variable R : relation (stream A).
    Variable H : bisimulation R.

    (* A bisimulation gives rise to a coalgebra *)

    Instance CoAlgebra_R : CoAlgebra (Fₛ A) := 
    {
        coalgebra_obj := {'(x,y) | R x y};
        coalgebra_morph := fun p => 
            let (hd_, tl_) := H in 
                match p with 
                    exist _ (s1, s2) H_R => 
                        (hd s1, exist _ (tl s1, tl s2) (tl_ _ _ H_R))
                end
    }.  

End Bisim.


(* (R : relation (stream A)) *)
(* relation bisimilar *)
(* {{ (x,y) | }} *)


#[refine] Instance bisim_stream (A : Type) : 
    Bisimulation.bisimulation (stream_CoAlgebra A) (stream_CoAlgebra A) := 
    {

    }.
Proof.
Admitted.

(* Class bisimulation {C : Category} {F : Functor C C} (A B : CoAlgebra F): Type := 
{

    R : CoAlgebra F;
    proj1 : CoAlgebraMorphism R A;
    proj2 : CoAlgebraMorphism R B;
    proj1_spec : (destr A) ∘ proj1 = (fmap F proj1) ∘ (destr R);
    proj2_spec : (destr B) ∘ proj2 = (fmap F proj2) ∘ (destr R) 
}. *)

    (* #[refine] Instance q_r : CoAlgebra (Fₛ A) := 
    {
        coalgebra_obj := sigT (fun p => R (fst p) (snd p));
        destr := fun p => _
    }.
    Proof.
        destruct p as [[[a s1] [b s2]] H_R]; simpl in *.
        destruct H as [hd tl].
        split.
        exact a.
        exact (existT _ (s1,s2) (tl _ _ H_R)).
    Defined. *)
