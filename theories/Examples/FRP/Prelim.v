From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Setoids Require Import Setoid.
From Categories.Category Require Import Category Functor.
From Categories.Embedding Require Import CategoryType.
From Categories.Algebra Require Import Coalgebra.

Section ProcessFunctor.

    Definition Proc (A B X : Type) : Type := A -> B * X.

    Definition fmap {A B X Y : Type} (f : X -> Y) (p : Proc A B X) : Proc A B Y :=
        fun a => 
            let (b, x) := p a in
            (b, f x).

    #[refine] Instance FunctorProc (A B : Type) : Functor Typ Typ :=
    {
        fobj := fun X => Proc A B X;
        fmap := @fmap A B
    }.
    Proof.
    -   unfold fmap.
        intro x.
        extensionality f.
        extensionality a.
        simpl.
        destruct (f a); reflexivity.
    -   unfold fmap.
        intros x y z f g.
        extensionality h.
        extensionality a.
        simpl.
        destruct (h a); reflexivity.
    Defined.

End ProcessFunctor.
    
Section Bisimilarity.

    Context {A B : Typ} {X Y : CoAlgebra (FunctorProc A B)}.

    CoInductive bisimilar :  coalgebra_obj X ->  coalgebra_obj Y -> Prop :=
        | bisimilar_ (f : coalgebra_obj X) (g : coalgebra_obj Y) : 
            (forall a b f', coalgebra_morph X f a = (b, f') -> 
                exists g', coalgebra_morph Y g a = (b, g') /\ bisimilar f' g') ->
            bisimilar f g.

End Bisimilarity.

Section BisimilarityFacts.

    Lemma bisimilar_refl : 
        forall {A B : Type} (X : CoAlgebra (FunctorProc A B)) 
            (f : coalgebra_obj X), bisimilar f f.
    Proof.
        cofix HCoInd.
        intros A B X Y.
        apply bisimilar_.
        intros a b f' H_step.
        exists f'; split; [assumption | apply HCoInd].
    Qed.
    
    Lemma bisimilar_sym : 
    forall {A B : Type} (X Y : CoAlgebra (FunctorProc A B)) 
        (f : coalgebra_obj X) (g : coalgebra_obj Y), bisimilar f g -> bisimilar g f.
    Proof.
        cofix HCoInd.
        intros A B X Y f g H_bisim.
        apply bisimilar_.
        intros a b g' H_step.
        inversion H_bisim; subst; clear H_bisim.
        destruct (coalgebra_morph X f a) as [b' f'] eqn:Heq.
        destruct (H _ _ _ Heq) as [g'' [Ha Hb]].
        assert (b = b' /\ g' = g'' ) as [Hc Hd].
        {
            rewrite Ha in H_step.
            injection H_step; intros; subst.
            split; reflexivity.
        }
        subst.
        exists f'.
        split.
        reflexivity.
        apply HCoInd; assumption.
    Qed.
    
    Lemma bisimilar_trans : 
        forall {A B : Type} (X Y Z : CoAlgebra (FunctorProc A B)) 
            (f : coalgebra_obj X) (g : coalgebra_obj Y) (h : coalgebra_obj Z),
            bisimilar f g -> bisimilar g h -> bisimilar f h.
    Proof.
        cofix HCoInd.
        intros A B X Y Z f g h Hfg Hgh.
        apply bisimilar_.
        intros a b h' H_step.
        inversion Hfg; subst; clear Hfg.
        inversion Hgh; subst; clear Hgh.
        destruct (H _ _ _ H_step) as [g' [Ha Hb]].
        destruct (H0 _ _ _ Ha) as [h'' [Hc Hd]].
        exists h''.
        split.
        assumption.
        apply HCoInd with (g := g'); assumption.
    Qed.
    
End BisimilarityFacts.


Section BisimulationProofs.

    Context {A B : Type} {X Y : CoAlgebra (FunctorProc A B)}.

    Definition bisimulation (R : coalgebra_obj X -> coalgebra_obj Y -> Prop) : Prop :=
        forall f g, R f g -> 
            forall a b f', coalgebra_morph X f a = (b, f') -> 
                    exists g', coalgebra_morph Y g a = (b, g') /\ R f' g'.

    Theorem bisimulation_gfp : 
        forall R, bisimulation R -> forall f g, R f g -> bisimilar f g.
    Proof.
        cofix CH.
        intros R H p p0 H0.
        constructor.
        intros a b f' H_eq.
        unfold bisimulation in H.
        eapply H with (g := p0) in H_eq .
        destruct H_eq as [g' [H_eq H_R]].
        exists g'.
        split.
        assumption.
        apply CH with (R := R); assumption.
        assumption.
    Qed.

End BisimulationProofs.

Add Parametric Relation (A B : Typ) (X : CoAlgebra (FunctorProc A B))  
    : (coalgebra_obj X) (@bisimilar A B X X)
    reflexivity proved by (@bisimilar_refl A B X)
    symmetry proved by (@bisimilar_sym A B X X)
    transitivity proved by (@bisimilar_trans A B X X X)
    as bisimilar_rel.

Infix "∼" := bisimilar (at level 60, right associativity): stream_scope.

