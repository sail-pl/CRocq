From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From Coq.Setoids Require Import Setoid.
From Categories.Category Require Import Category Functor CategoryCat.
From Categories.Algebra Require Import Coalgebra.
From Categories.Embedding Require Import CategoryType Arrow.
From Categories.Examples.FRP Require Import Prelim.

Open Scope stream_scope.

Section YampaLanguage.

    Inductive SF : Typ -> Typ -> Type :=
    | Arr : forall {A B : Typ}, (Typ A B) -> SF A B
    | Comp : forall {A B C : Typ}, SF A B -> SF B C -> SF A C
    | First : forall {A B C : Typ}, SF A B -> SF (A * C) (B * C)
    | Loop : forall {A B C : Typ}, C -> SF (A * C) (B * C) -> SF A B.

End YampaLanguage.

Section YampaSemanticsDomain.

    CoInductive sf (A B : Type) := 
        sf_ : (A -> B * sf A B) -> sf A B.

    #[global] Arguments sf_ [A B] _.

    Definition decompose {A B : Typ} (f : sf A B) : sf A B :=
        match f with sf_ f => sf_ f end.

    Lemma decompose_eq : 
        forall {A B : Typ} (f : sf A B), f = decompose f.
    Proof.
        destruct f; reflexivity.
    Qed.

    #[global] Instance CoAlgebrasf (A B : Type) : CoAlgebra (FunctorProc A B) := 
    {
        coalgebra_obj := sf A B;
        coalgebra_morph := fun sf => match sf with sf_ f => f end 
    }.

End YampaSemanticsDomain.

Section Category.

    CoFixpoint id (A : Typ) : sf A A :=
        sf_ (fun a => (a, id A)).

    CoFixpoint comp {A B C : Typ} : sf A B -> sf B C -> sf A C :=
        fun '(sf_ f) '(sf_ g) =>
        sf_ (fun a => 
            let (b, f') := f a in
            let (c, g') := g b in
            (c, comp f' g')).

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

    Inductive R_bisim_id_comp (A B : Typ): relation (sf A B) :=
    R_bisim_id_comp_ : 
        forall (f : sf A B), R_bisim_id_comp _ _ (comp (id A) f) f.


    Lemma R_bisim_id_comp_bisim : 
        forall (A B : Typ), bisimulation (R_bisim_id_comp A B).
    Proof.
        intros A B.
        unfold bisimulation.
        intros f g H_eq1 x y f' H_eq2.
        inversion H_eq1; subst.
        simpl in *.
        destruct g.
        destruct (p x) eqn:Ha.
        injection H_eq2; intros; subst.
        exists s.
        split.
        reflexivity.
        apply R_bisim_id_comp_.
    Qed.

    Lemma csf1 :
        forall (a b : Typ) (f : sf a b), comp (id a) f ∼ f.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_id_comp a b).
        - apply R_bisim_id_comp_bisim.
        - constructor. 
    Qed.

    Lemma csf2 : 
        forall (a b : Typ) (f : sf a b), comp f (id b) ∼ f.
    Admitted.

    Lemma csf3 : 
    forall (a b c d : Typ) (f : sf a b) (g : sf b c) (h : sf c d),
        comp (comp f g) h ∼ comp f (comp g h).
    Admitted.

    #[refine] Global Instance CategorySF : Category :=
            {
                obj := Typ;
                hom := sf;
                idty := @id;
                compose := fun _ _ _ x y => comp y x
            }.
    Proof.
    -   intros A B sf.
        apply (bisimulation_extentionality A B (CoAlgebrasf A B)).
        apply csf1.
    -   intros A B sf.
        apply (bisimulation_extentionality A B (CoAlgebrasf A B)).
        apply csf2.
    -   intros A B C D f g h.
        apply (bisimulation_extentionality A D (CoAlgebrasf A D)).
        apply csf3.
    Defined.

End Category.

Section Semantics.

    CoFixpoint arr {A B : Typ} : (Typ A B) -> sf A B := 
        fun f => sf_ (fun a => (f a, arr f)).

    CoFixpoint first {A B C : Type} (f : sf A B) : sf (A * C) (B * C) :=
        match f with sf_ f =>
            sf_ (fun '(a,c) => 
                let (b, f') := f a in
                ((b,c), first f'))
            end. 

    CoFixpoint loop {A B C : Type} (c : C) (f : sf (A * C) (B * C)) : sf A B :=
        sf_ (fun a => 
        match f with sf_ f =>
            let '((b,c'), f') := f (a, c) in
            (b, loop c' f')
            end).

    Inductive R_bisim_ff1 (A : Typ) : relation (sf A A) :=
    R_bisim_ff1_ : R_bisim_ff1 _ (arr (idty A)) (idty _).

    Lemma ff1 : forall a : Typ, arr (idty a) = idty _.
    Proof. 
        intro A.
        apply (bisimulation_extentionality A A (CoAlgebrasf A A)).
        apply bisimulation_gfp with (R := R_bisim_ff1 A).
        - intros f g H_bisim a b f' g'.
            simpl in *.
            inversion H_bisim; subst.
            simpl in *.
            inversion g'; subst; clear g'.
            exists (id A).
            split.
            -- reflexivity.
            -- apply R_bisim_ff1_.
        - constructor.
    Qed.

    Inductive R_bisim_ff2 (A B C : Typ) : relation (sf A C) :=
    R_bisim_ff2_ : forall (f : Typ A B) (g : Typ B C), 
        R_bisim_ff2 _ _ _ (arr g ∘ arr f) (arr (g ∘ f)).

    Lemma ff2 : forall (A B C : Typ) (g : Typ B C) (h : Typ A B),
        arr g ∘ arr h = arr (g ∘ h).
    Proof.
        intros A B C g h.
        apply (bisimulation_extentionality A C (CoAlgebrasf A C)).
        apply bisimulation_gfp with (R := R_bisim_ff2 A B C).
        - intros f1 f2 H_bisim a b f1' H_eq.
          simpl in *.
          inversion H_bisim; subst.
          simpl in *.
          inversion H_eq; subst; clear H_eq.
          exists (arr (fun x : A => g0 (f x))).
          split.
          -- reflexivity.
          -- apply R_bisim_ff2_.
        - constructor.
    Qed.
        
    #[refine] Global Instance FunctorF : Functor Typ CategorySF :=
    {
        fobj := fun X => X;
        fmap := @arr
    }.
    - apply ff1.
    - apply ff2.
    Defined.    

    Fixpoint sem {A B : Typ} (f : SF A B) : sf A B :=
        match f with
            | Arr h => arr h
            | Comp f1 f2 => sem f2 ∘ sem f1 (* comp (sem f1) (sem f2) *)
            | First f => first (sem f)
            | Loop c f => loop c (sem f)
        end.
            
    CoInductive stream (A : Typ) : Typ :=
        | Cons : A -> stream A -> stream A.

    Arguments Cons [A] _ _.

    CoFixpoint run {A B : Type} (f : sf A B) (s : stream A) : stream B :=
        match f with sf_ f =>
            match s with 
                | Cons a s => 
                    let (b, f') := f a in
                    Cons b (run f' s)
            end
        end.

    Definition equiv {A B : Typ} : SF A B -> SF A B -> Prop :=
        fun f g => sem f ∼ sem g.

End Semantics.

Infix "≡" := equiv (at level 60, right associativity): stream_scope.

Section Congruence.

    Inductive R_bisim_comp (A B : Typ): relation (sf A B) :=
    R_bisim_comp_ : 
        forall C (f1 f2 : sf A C) (g1 g2 : sf C B), f1 ∼ f2 -> g1 ∼ g2 ->
        R_bisim_comp _ _ (comp f1 g1) (comp f2 g2).

    Lemma R_bisim_comp_bisim : forall (A B : Typ), bisimulation (R_bisim_comp A B).
    Proof.
    Admitted.
            
    Lemma bisimilar_comp : forall (A B C : Typ) (f1 f2 : sf A B) (g1 g2 : sf B C),
        f1 ∼ f2 -> g1 ∼ g2 -> comp f1 g1 ∼ comp f2 g2.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_comp A C).
        apply R_bisim_comp_bisim.
        apply R_bisim_comp_; assumption.
    Qed.

    Inductive R_bisim_first (A B C : Typ): relation (sf (A * C) (B * C)) :=
    R_bisim_first_ : 
        forall (f g : sf A B), f ∼ g -> 
            R_bisim_first A B C (first f) (first g).

    Lemma R_bisim_first_bisim : forall (A B C : Typ), bisimulation (R_bisim_first A B C).
    Admitted.

    Lemma bisimilar_first : forall (A B C : Typ) (f g : sf A B),
        f ∼ g -> @first _ _ C f ∼ first g.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_first A B C).
        apply R_bisim_first_bisim.
        apply R_bisim_first_; assumption.
    Qed.

    Inductive R_bisim_loop (A B : Typ): relation (sf A B) :=
        R_bisim_loop_ : forall (C : Typ)
            (f g : sf (A * C) (B * C)) (c : C), f ∼ g -> 
                R_bisim_loop A B (loop c f) (loop c g).

    Lemma R_bisim_loop_bisim : 
        forall (A B : Typ), bisimulation (R_bisim_loop A B).
    Admitted.

    Lemma bisimilar_loop : forall (A B C : Typ) (x : C)
        (f g : sf (A * C) (B * C)),
        f ∼ g -> loop x f ∼ loop x g.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_loop A B).
        apply R_bisim_loop_bisim.
        apply R_bisim_loop_; assumption.
    Qed.

    #[global]Add Parametric Morphism (A B C : Typ) : 
        (@first A B C)
        with 
            signature (@bisimilar A B (CoAlgebrasf A B) (CoAlgebrasf A B)) ==> 
                (@bisimilar (A * C) (B * C) (CoAlgebrasf (A * C) (B * C)) 
                    (CoAlgebrasf (A * C) (B * C))) 
        as tl_mor.
    Proof.
        apply bisimilar_first.
    Qed.

    #[global] Add Parametric Morphism (A B C : Typ) : (@comp A B C)
        with 
            signature (@bisimilar A B (CoAlgebrasf A B) (CoAlgebrasf A B)) ==> 
            (@bisimilar B C (CoAlgebrasf B C) (CoAlgebrasf B C) ) ==> 
            (@bisimilar A C (CoAlgebrasf A C) (CoAlgebrasf A C)) as comp_mor.
    Proof.
        intros x y H_equiv1 z w H_equiv2.
        now apply bisimilar_comp.
    Qed.

    #[global] Add Parametric Morphism (A B C : Typ) : (@loop A B C)
        with signature eq ==> 
            (@bisimilar (A * C) (B * C) _ _) ==> 
            (@bisimilar A B _ _) as loop_mor.
    Proof.
        apply bisimilar_loop.
    Qed.

    Context {A B C : Typ}.

    Lemma equiv_first : 
    forall (f g : SF A B),
        f ≡ g -> @First _ _ C f ≡ First g.
    Proof.
        unfold equiv; simpl; intros.
        rewrite H.
        reflexivity.
    Qed.

    Lemma equiv_comp : 
        forall (f1 f2 : SF A B) (g1 g2 : SF B C),
            f1 ≡ f2 -> g1 ≡ g2 -> Comp f1 g1 ≡ Comp f2 g2.
    Proof.
    Admitted.

    Lemma equiv_loop : 
        forall (c : C) (f g : SF (A * C) (B * C)),
            f ≡ g -> Loop c f ≡ Loop c g.
    Proof.
        unfold equiv; simpl; intros.
        rewrite H.
        reflexivity.
    Qed.

End Congruence.

Section ArrowProperties.

    Definition assoc {A B C : Typ} : (A * B) * C -> A * (B * C) :=
    fun '((a,b),c) => (a,(b,c)).

    Definition unassoc {A B C : Typ} : A * (B * C) -> (A * B) * C :=
    fun '(a,(b,c)) => ((a,b),c).

    Inductive R_eq_2a (A B: Typ) : relation (sf A B) :=
        R_eq_2a_ : forall (a : sf A B),
            R_eq_2a _ _ (comp (arr (idty _)) a) a.
    
    Lemma arrow_eq_2a : forall (A B : Typ) (a : sf A B), 
        comp (arr (idty A)) a ∼ a.
    Proof.
        intros.
        assert (bisimulation (R_eq_2a A B)).
        {
            unfold bisimulation.
            intros f g H_eq1 x y f' H_eq2.
            inversion H_eq1; subst.
            simpl in *.
            destruct g.
            destruct (p x) eqn:Ha.
            injection H_eq2; intros; subst.
            exists s.
            split.
            reflexivity.
            apply R_eq_2a_.
        }
        now apply bisimulation_gfp with (R := R_eq_2a A B).
    Qed.

    Lemma arrow_eq_2b : forall (A B : Typ) (a : sf A B),
        comp a (arr (fun x => x)) ∼ a.
    Admitted.

    Lemma arrow_eq_2c : 
        forall (A B C D: Typ) (sf1 : sf A B) (sf2 : sf B C) (sf3 : sf C D),
            comp (comp sf1 sf2) sf3 ∼ comp sf1 (comp sf2 sf3).
    Admitted.

    Lemma arrow_eq_2d : 
        forall (A B C : Typ) (f : Typ A B) (g : Typ B C),
            arr (fun x => g (f x)) ∼ comp (arr f) (arr g).
    Admitted.

    Lemma arrow_eq_2e :
        forall (A B C : Typ) (sf : sf A B),
            comp (@first _ _ C sf) (arr (fun '(x,y) => x)) ∼ 
                comp (arr (fun '(x,y) => x)) sf.
    Admitted.

    Lemma arrow_eq_2f : 
        forall (A B : Typ) (sf : sf A B) (f : Typ A B),
            comp (first sf) (arr (fun '(x,y) => (x, f y))) ∼
                comp (arr (fun '(x,y) => (x,f y))) (first sf).
    Admitted.

    Lemma arrow_eq_2g : 
        forall (A B C D : Typ) (sf : sf A B),
            comp (@first _ _ D (@first _ _ C sf)) (arr assoc) ∼ 
            comp (arr assoc) (first sf).
    Admitted.

    Lemma arrow_eq_2h :     
        forall (A B C : Typ) (f : Typ A B),
        @first _ _ C (arr f) ∼ arr (fun '(x,y) => (f x, y)).
    Admitted.

    Lemma arrow_eq_2i : forall (A B C D : Type) (a : sf A B) (b : sf B C),
        @first _ _ D (comp a b) ∼ comp (first a) (first b).
    Proof.
    Admitted.

    Lemma arrow_eq_3a :
        forall (A B C D : Typ) (c : D) (sf1 : sf A B) (sf2 : sf (B * D) (C * D)),
            loop c (comp (first sf1) sf2) ∼ @comp _ _ C sf1 (loop c sf2).
    Admitted.

    Lemma arrow_eq_3b :
        forall (A B C D : Typ) (c : D) (sf1 : sf (A * D) (B * D)) (sf2 : sf B C),
            loop c (comp sf1 (first sf2)) ∼ comp (loop c sf1) sf2.
    Admitted.

    Lemma arrow_eq_3c :
        forall (A B C D : Typ) (sf : sf ((A * C) * D) ((B * C) * D)) (c : C) (d : D), 
        loop c (loop d sf) ∼ 
            loop (c,d) (comp (arr unassoc) (comp sf (arr assoc))).
    Admitted.

End ArrowProperties.

Section Simplification.
    Lemma simplify : 
        forall (A B : Typ) (sf : SF A B),
            exists (C : Typ) (v : C) (f : Typ (A * C) (B * C)),
            sf ≡ Loop v (Arr f).
    Proof.
        intros A B sf.
        induction sf.
        -   exists unit. exists tt.
            exists (fun '(a,_) => (h a, tt)).
            unfold equiv.
            admit.
        -   destruct IHsf1 as [C1 [v1 [f1 H1]]].
            destruct IHsf2 as [C2 [v2 [f2 H2]]].
            exists (C1 * C2). exists (v1, v2).
            exists (fun '(a, (c1, c2)) => 
                let (b, c1') := f1 (a, c1) in
                let (c, c2') := f2 (b, c2) in
                (c, (c1', c2'))).
            admit.
        -   destruct IHsf as [D [v [f H]]].
            exists D. exists v.
            exists (fun '((a, d), c) => 
                let (b, c') := f (a, c) in
                ((b, d), c')).
            admit.
    Admitted.

End Simplification.




