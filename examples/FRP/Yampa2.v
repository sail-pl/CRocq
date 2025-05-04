From Stdlib.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From Stdlib.Setoids Require Import Setoid.
From CRocq.Category Require Import Category Functor CategoryCat.
From CRocq.Algebra Require Import Coalgebra.
From CRocq.Embedding Require Import CategoryType Arrow.
From Examples.FRP Require Import Prelim.

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

    Inductive R_bisim_csf1 (A B : Typ): relation (sf A B) :=
    R_bisim_csf1_ : 
        forall (f : sf A B), R_bisim_csf1 _ _ (comp (id A) f) f.


    Lemma R_bisim_csf1_bisim : 
        forall (A B : Typ), bisimulation (R_bisim_csf1 A B).
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
        apply R_bisim_csf1_.
    Qed.

    Lemma csf1 :
        forall (A B : Typ) (f : sf A B), comp (id A) f ∼ f.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_csf1 A B).
        - apply R_bisim_csf1_bisim.
        - constructor. 
    Qed.

    Inductive R_bisim_csf2 (A B : Typ): relation (sf A B) :=
    R_bisim_csf2_ : 
        forall (f : sf A B), R_bisim_csf2 _ _ (comp f (id B)) f.

    Lemma csf2 : 
        forall (A B : Typ) (f : sf A B), comp f (id B) ∼ f.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_csf2 A B).
        - intros g h H_bisim a b g' H_eq.
          simpl in *.
          inversion H_bisim; subst.
          destruct h; simpl in *.
          destruct (p a).
          inversion H_eq; subst; clear H_eq.
          exists s.
          split.
          -- reflexivity.
          -- apply R_bisim_csf2_. 
        - constructor. 
    Qed.

    Inductive R_bisim_csf3 (A B C D : Typ): relation (sf A D) :=
    R_bisim_csf3_ : 
        forall (f : sf A B) (g : sf B C) (h : sf C D),  
            R_bisim_csf3 _ _ _ _ (comp (comp f g) h) (comp f (comp g h)).

    Lemma csf3 : 
    forall (A B C D : Typ) (f : sf A B) (g : sf B C) (h : sf C D),
        comp (comp f g) h ∼ comp f (comp g h).
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_csf3 A B C D).
        - intros f1 f2 H_bisim a b f' H_eq.
          simpl in *.
          inversion H_bisim; subst.
          destruct h0, f0, g0; simpl in *.
          destruct (p0 a), (p1 b0), (p c).
          inversion H_eq; subst; clear H_eq.
          exists (comp s (comp s0 s1)).
          split.
          -- reflexivity.
          -- apply R_bisim_csf3_. 
        - constructor. 
    Qed.

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

    Lemma ff1 : forall a : Typ, arr (idty a) ∼ idty _.
    Proof. 
        intro A.
        apply bisimulation_gfp with (R := R_bisim_ff1 A).
        - intros f g H_bisim a b f' H_eq.
            simpl in *.
            inversion H_bisim; subst.
            simpl in *.
            inversion H_eq; subst; clear H_eq.
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
        arr g ∘ arr h  ∼ arr (g ∘ h).
    Proof.
        intros A B C g h.
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
    - intro A.
      apply (bisimulation_extentionality A A (CoAlgebrasf A A)).
      apply ff1.
    - intros A B C g h.
      apply (bisimulation_extentionality A C (CoAlgebrasf A C)).
      apply ff2.
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
        intros A B f g H_bisim a c f' H_eq.
        inversion H_bisim; subst; clear H_bisim.
        simpl in *.
        inversion H; subst; simpl in *.
        destruct f1 as [p1].
        destruct (p1 a) eqn:H_res1.
        specialize (H1 a c0 s H_res1).
        destruct f2 as [p2].
        destruct H1 as [s' [H_res1' H_bisim1]].
        clear H.
        inversion H0; subst; simpl in *.
        destruct g1 as [q1].
        rewrite H_res1 in H_eq.
        destruct (q1 c0) eqn:H_res2.
        inversion H_eq; subst; clear H_eq.
        specialize (H c0 c s0 H_res2).
        destruct g2 as [q2].
        destruct H as [s0' [H_res2' H_bisim2]].
        rewrite H_res1'.
        rewrite H_res2'.
        exists (comp s' s0').
        split.
        - reflexivity.
        - now apply R_bisim_comp_.
    Qed.
            
    Lemma bisimilar_comp : forall (A B C : Typ) (f1 f2 : sf A B) (g1 g2 : sf B C),
        f1 ∼ f2 -> g1 ∼ g2 -> comp f1 g1 ∼ comp f2 g2.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_comp A C).
        - apply R_bisim_comp_bisim.
        - apply R_bisim_comp_; assumption.
    Qed.

    Inductive R_bisim_first (A B C : Typ): relation (sf (A * C) (B * C)) :=
    R_bisim_first_ : 
        forall (f g : sf A B), f ∼ g -> 
            R_bisim_first A B C (first f) (first g).

    Lemma R_bisim_first_bisim : forall (A B C : Typ), bisimulation (R_bisim_first A B C).
    Proof.
        intros A B C f g H_bisim a b h H_eq.
        inversion H_bisim; subst.
        simpl in *.
        destruct f0, a.
        destruct (p a) eqn:H_res.
        inversion H_eq; subst; clear H_eq.
        inversion H; subst; simpl in *.
        destruct g0 as [p'].
        specialize (H0 a b0 s H_res).
        destruct H0 as [s' [H_res' H_bisim']].
        rewrite H_res'.
        exists (first s').
        split.
        - reflexivity.
        - now apply R_bisim_first_.
    Qed.

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
    Proof.
        intros A B f g H_bisim a b h H_eq.
        inversion H_bisim; subst.
        simpl in *.
        destruct f0 as [p].
        destruct (p (a, c)) eqn:H_res.
        destruct p0 as [a' c'].
        inversion H_eq; subst; clear H_eq.
        inversion H; subst.
        simpl in *.
        specialize (H0 (a,c) (b,c') s H_res).
        destruct g0 as [p'].
        destruct H0 as [s' [H_res' H_bisim']].
        rewrite H_res'.
        exists (loop c' s').
        split.
        - reflexivity.
        - now apply R_bisim_loop_.
    Qed.

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
        unfold equiv; simpl; intros.
        now apply bisimilar_comp.
    Qed.

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
    
    Lemma arrow_eq_4a : forall (A B : Typ) (a : sf A B), 
        comp (arr (idty A)) a ∼ a.
    Proof.
        intros.
        transitivity (comp (id A) a).
        - apply bisimilar_comp.
          -- apply ff1.
          -- reflexivity.
        - apply csf1.
    Qed.

    Lemma arrow_eq_4b : forall (A B : Typ) (a : sf A B),
        comp a (arr (idty B)) ∼ a.
    Proof.
        intros.
        transitivity (comp a (id B)).
        - apply bisimilar_comp.
          -- reflexivity.
          -- apply ff1.
        - apply csf2.
    Qed.

    Lemma arrow_eq_4c : 
        forall (A B C D: Typ) (sf1 : sf A B) (sf2 : sf B C) (sf3 : sf C D),
            comp (comp sf1 sf2) sf3 ∼ comp sf1 (comp sf2 sf3).
    Proof.
        intros.
        apply csf3.
    Qed.

    Lemma arrow_eq_4d : 
        forall (A B C : Typ) (f : Typ A B) (g : Typ B C),
            arr (fun x => g (f x)) ∼ comp (arr f) (arr g).
    Proof.
        intros.
        transitivity (arr (g ∘ f)).
        - reflexivity.
        - symmetry. 
          apply ff2.
    Qed.

    Inductive R_bisim_eq_4e (A B C : Typ): relation (sf (A * C) B) :=
        R_bisim_eq_4e_ : forall (sf : sf A B), 
                R_bisim_eq_4e _ _ _ 
                    (comp (@first _ _ C sf) (arr (fun '(x,y) => x)))
                    (comp (arr (fun '(x,y) => x)) sf).

    Lemma arrow_eq_4e :
        forall (A B C : Typ) (sf : sf A B),
            comp (@first _ _ C sf) (arr (fun '(x,y) => x)) ∼ 
                comp (arr (fun '(x,y) => x)) sf.
    Proof.
        intros A B C sf.
        apply bisimulation_gfp with (R := R_bisim_eq_4e A B C).
        - intros f g H_bisim [a c] b h H_eq.
          inversion H_bisim; subst; clear H_bisim.
          simpl in *.
          destruct sf0.
          simpl in *.
          destruct (p a) eqn:H_res.
          inversion H_eq; subst; clear H_eq.
          exists (comp (arr (fun '(x,_) => x)) s).
          split.
          -- reflexivity.
          -- apply R_bisim_eq_4e_.
        - constructor.
    Qed.

    Inductive R_bisim_eq_4f (A B C D : Typ): relation (sf (A * C) (B * D)) :=
    R_bisim_eq_4f_ : forall (sf : sf A B) (f : Typ C D), 
            R_bisim_eq_4f _ _ _ _ 
                (comp (first sf) (arr (fun '(x,y) => (x, f y))))
                (comp (arr (fun '(x,y) => (x,f y))) (first sf)).

    Lemma arrow_eq_4f : 
        forall (A B C D : Typ) (sf : sf A B) (f : Typ C D),
            comp (first sf) (arr (fun '(x,y) => (x, f y))) ∼
                comp (arr (fun '(x,y) => (x,f y))) (first sf).
    Proof.
        intros A B C D sf f.
        apply bisimulation_gfp with (R := R_bisim_eq_4f A B C D).
        - intros h g H_bisim [a c] b f' H_eq.
            inversion H_bisim; subst; clear H_bisim.
            simpl in *.
            destruct sf0.
            simpl in *.
            destruct (p a) eqn:H_res.
            inversion H_eq; subst; clear H_eq.
            exists (comp (arr (fun '(x, y) => (x, f0 y))) (first s)).
            split.
            -- reflexivity.
            -- apply R_bisim_eq_4f_.
        - constructor.
    Qed.

    Inductive R_bisim_eq_4g (A B C D : Typ): relation (sf (A * C * D) (B * (C* D))) :=
    R_bisim_eq_4g_ : forall (sf : sf A B), 
            R_bisim_eq_4g _ _ _ _ 
                (comp (@first _ _ D (@first _ _ C sf)) (arr assoc))
                (comp (arr assoc) (first sf)).

    Lemma arrow_eq_4g : 
        forall (A B C D : Typ) (sf : sf A B),
            comp (@first _ _ D (@first _ _ C sf)) (arr assoc) ∼ 
            comp (arr assoc) (first sf).
    Proof.
        intros A B C D sf.
        apply bisimulation_gfp with (R := R_bisim_eq_4g A B C D).
        - intros h g H_bisim [[a c] d] b f' H_eq.
          inversion H_bisim; subst; clear H_bisim.
          simpl in *.
          destruct sf0.
          simpl in *.
          destruct (p a) eqn:H_res.
          inversion H_eq; subst; clear H_eq.
          exists (comp (arr assoc) (first s)).
          split.
          -- reflexivity.
          -- apply R_bisim_eq_4g_.
        - constructor.
    Qed.        

    Inductive R_bisim_eq_4h (A B C : Typ): relation (sf (A * C) (B * C)) :=
    R_bisim_eq_4h_ : forall (f : Typ A B), 
        R_bisim_eq_4h _ _ _  (@first _ _ C (arr f)) (arr (fun '(x,y) => (f x, y))).

    Lemma arrow_eq_4h :     
        forall (A B C : Typ) (f : Typ A B),
        @first _ _ C (arr f) ∼ arr (fun '(x,y) => (f x, y)).
    Proof.
        intros A B C f.
        apply bisimulation_gfp with (R := R_bisim_eq_4h A B C).
        - intros h g H_bisim [a c] [b c'] f' H_eq.
          inversion H_bisim; subst; clear H_bisim.
          simpl in *.
          inversion H_eq; subst; clear H_eq.
          exists (arr (fun '(x, y) => (f0 x, y))).
          split.
          -- reflexivity.
          -- apply R_bisim_eq_4h_.
        - constructor.
    Qed.  

    Inductive R_bisim_eq_4i (A B C D : Typ): relation (sf (A * D) (C * D)) :=
    R_bisim_eq_4i_ : forall (sf1 : sf A B) (sf2 : sf B C), 
        R_bisim_eq_4i _ _ _ _ 
                      (@first _ _ D (comp sf1 sf2)) 
                      (comp (first sf1) (first sf2)).

    Lemma arrow_eq_4i : forall (A B C D : Type) (a : sf A B) (b : sf B C),
        @first _ _ D (comp a b) ∼ comp (first a) (first b).
    Proof.
        intros A B C D sf1 sf2.
        apply bisimulation_gfp with (R := R_bisim_eq_4i A B C D).
        - intros h g H_bisim [a d] [b d'] f' H_eq.
          inversion H_bisim; subst; clear H_bisim.
          simpl in *.
          destruct sf0, sf3.
          simpl in *.
          destruct (p a) eqn:H_res.
          destruct (p0 b0) eqn:H_res'.
          inversion H_eq; subst; clear H_eq.
          exists (comp (first s) (first s0)).
          split.
          -- reflexivity.
          -- apply R_bisim_eq_4i_.
        - constructor.
    Qed.

    Inductive R_bisim_eq_3a (A B C D : Typ): relation (sf A C) :=
    R_bisim_eq_3a_ : forall (c : D) (sf1 : sf A B) (sf2 : sf (B * D) (C * D)), 
        R_bisim_eq_3a _ _ _ _ 
                      (loop c (comp (first sf1) sf2)) 
                      (@comp _ _ C sf1 (loop c sf2)).

    Lemma arrow_eq_3a :
        forall (A B C D : Typ) (c : D) (sf1 : sf A B) (sf2 : sf (B * D) (C * D)),
            loop c (comp (first sf1) sf2) ∼ @comp _ _ C sf1 (loop c sf2).
    Proof.
        intros A B C D c sf1 sf2.
        apply bisimulation_gfp with (R := R_bisim_eq_3a A B C D).
        - intros h g H_bisim a b f' H_eq.
          inversion H_bisim; subst; clear H_bisim.
          simpl in *.
          destruct sf0, sf3.
          simpl in *.
          destruct (p a) eqn:H_res.
          destruct (p0 (b0,c0)) eqn:H_res'.
          destruct p1.
          inversion H_eq; subst; clear H_eq.
          exists (comp s (loop d s0)).
          split.
          -- reflexivity.
          -- apply R_bisim_eq_3a_.
        - constructor.
    Qed. 

    Inductive R_bisim_eq_3b (A B C D : Typ): relation (sf A C) :=
    R_bisim_eq_3b_ : forall (c : D) (sf1 : sf (A * D) (B * D)) (sf2 : sf B C), 
        R_bisim_eq_3b _ _ _ _ 
                      (loop c (comp sf1 (first sf2))) 
                      (comp (loop c sf1) sf2).

    Lemma arrow_eq_3b :
        forall (A B C D : Typ) (c : D) (sf1 : sf (A * D) (B * D)) (sf2 : sf B C),
            loop c (comp sf1 (first sf2)) ∼ comp (loop c sf1) sf2.
    Proof.
        intros A B C D c sf1 sf2.
        apply bisimulation_gfp with (R := R_bisim_eq_3b A B C D).
        - intros h g H_bisim a b f' H_eq.
          inversion H_bisim; subst; clear H_bisim.
          simpl in *.
          destruct sf0, sf3.
          simpl in *.
          destruct (p (a,c0)) eqn:H_res.
          destruct p1.
          destruct (p0 b0) eqn:H_res'.
          inversion H_eq; subst; clear H_eq.
          exists (comp (loop d s) s0).
          split.
          -- reflexivity.
          -- apply R_bisim_eq_3b_.
        - constructor.
    Qed. 

    Inductive R_bisim_eq_3c (A B C D : Typ): relation (sf A B) :=
    R_bisim_eq_3c_ : forall (c : C) (d : D) (sf : sf ((A * C) * D) ((B * C) * D)), 
        R_bisim_eq_3c _ _ _ _ 
                      (loop c (loop d sf)) 
                      (loop (c,d) (comp (arr unassoc) (comp sf (arr assoc)))).

    Lemma arrow_eq_3c :
        forall (A B C D : Typ) (sf : sf ((A * C) * D) ((B * C) * D)) (c : C) (d : D), 
        loop c (loop d sf) ∼ 
            loop (c,d) (comp (arr unassoc) (comp sf (arr assoc))).
    Proof.
        intros A B C D sf c d.
        apply bisimulation_gfp with (R := R_bisim_eq_3c A B C D).
        - intros h g H_bisim a b f' H_eq.
          inversion H_bisim; subst; clear H_bisim.
          simpl in *.
          destruct sf0.
          simpl in *.
          destruct (p ((a,c0), d0)) eqn:H_res.
          destruct p0 as [[b' c'] d'].
          inversion H_eq; subst; clear H_eq.
          simpl.
          exists (loop (c', d') (comp (arr unassoc) (comp s (arr assoc)))).
          split.
          -- reflexivity.
          -- apply R_bisim_eq_3c_.
        - constructor.
    Qed.         

End ArrowProperties.


Section Simplification.

    Inductive R_bisim_simp_arr (A B : Typ) : relation (sf A B) :=
    R_bisim_simp_arr_ : forall (f : Typ A B), 
        R_bisim_simp_arr _ _ (arr f) (loop tt (arr (fun '(a, _) => (f a, tt)))).

    Lemma simplify_arr : 
        forall (A B : Typ) (f : Typ A B),
            arr f ∼ loop tt (arr (fun '(a, _) => (f a, tt))).
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_simp_arr A B).
        - intros h g H_bisim a b f' H_eq.
        inversion H_bisim; subst; clear H_bisim.
        simpl in *.
        inversion H_eq; subst; clear H_eq.
        exists (loop tt (arr (fun '(a0, _) => (f0 a0, tt)))).
        split.
        -- reflexivity.
        -- apply R_bisim_simp_arr_.
        - constructor.
    Qed.
    
    Inductive R_bisim_simp_first (A B C D : Typ) : relation (sf (A * C) (B * C)) :=
    R_bisim_simp_first_ : forall (d : D) (sf : sf A B) (f : Typ (A * D) (B * D)), 
        sf ∼ loop d (arr f) ->
        R_bisim_simp_first _ _ _ _ 
            (first sf) (loop d (arr (fun '(a, d, c) => let (b, c') := f (a, c) in (b, d, c')))).

    Lemma R_bisim_simp_first_bisim (A B C D : Typ) : bisimulation (R_bisim_simp_first A B C D).
    Proof.
        intros h g H_bisim a b f' H_eq.
        inversion H_bisim; subst; clear H_bisim.
        simpl in *.
        destruct sf0.
        destruct a as [a c].
        destruct b as [b c'].
        destruct (p a) eqn:H_res.
        inversion H_eq; subst; clear H_eq.
        inversion H; subst.
        simpl in *.
        specialize (H0 a b s H_res).
        destruct (f (a,d)) eqn:H_res'.
        destruct H0 as [s' [H_eq H_bisim]].
        inversion H_eq; subst; clear H_eq.
        exists (loop d0 (arr (fun '(a0, d1, c) => 
                    let (b0, c'0) := f (a0, c) in (b0, d1, c'0)))).
        split.
        - reflexivity.
        - now apply R_bisim_simp_first_.
    Qed.

    Lemma simplify_first (A B C D : Typ) :
        forall (sf : sf A B) (d : D) (f : A * D -> B * D), 
            sf ∼ loop d (arr f) ->
            @first _ _ C sf ∼ 
            loop d (arr (fun '(a, d, c) => let (b, c') := f (a, c) in (b, d, c'))).
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_simp_first A B C D).
        -- apply R_bisim_simp_first_bisim.
        -- now apply R_bisim_simp_first_.
    Qed.

    Inductive R_bisim_simp_comp (A B C D E : Typ) : relation (sf A C) :=
    R_bisim_simp_comp_ : forall (d : D) (e : E)
                                (sf1 : sf A B) 
                                (sf2 : sf B C) 
                                (f1 : Typ (A * D) (B * D))
                                (f2 : Typ (B * E) (C * E)), 
        sf1 ∼ loop d (arr f1) ->
        sf2 ∼ loop e (arr f2) ->
        R_bisim_simp_comp _ _ _ _ _
            (comp sf1 sf2) 
            (loop (d, e) (arr (fun '(a, (c1, c2)) =>
                let (b, c1') := f1 (a, c1) in 
                let (c, c2') := f2 (b, c2) in (c, (c1', c2'))))).

    Lemma R_bisim_simp_comp_bisim (A B C D E : Typ) : 
        bisimulation (R_bisim_simp_comp A B C D E).
    Proof.
        intros h g H_bisim a b f' H_eq.
        inversion H_bisim; subst; clear H_bisim.
        simpl in *.
        destruct sf1, sf2.
        destruct (p a) eqn:H_res.
        destruct (p0 b0) eqn:H_res'.
        inversion H_eq; subst; clear H_eq.
        inversion H; subst.
        simpl in *.
        specialize (H1 a b0 s H_res).
        destruct (f1 (a,d)) eqn:H_res1.
        destruct H1 as [s' [H_eq H_bisim]].
        inversion H_eq; subst; clear H_eq.
        inversion H0; subst.
        simpl in *.
        specialize (H1 b0 b s0 H_res').
        destruct (f2 (b0,e)) eqn:H_res2.
        destruct H1 as [s0' [H_eq H_bisim']].
        inversion H_eq; subst; clear H_eq.
        exists (loop (d0, e0) 
                     (arr (fun '(a0, (c1, c2)) => 
                        let (b1, c1') := f1 (a0, c1) in 
                        let (c, c2') := f2 (b1, c2) in (c, (c1', c2'))))).
        split.
        - reflexivity.
        - now apply R_bisim_simp_comp_.
    Qed.

    Lemma simplify_comp (A B C D E : Typ) :
        forall  (d : D) (e : E)
                (sf1 : sf A B) 
                (sf2 : sf B C) 
                (f1 : Typ (A * D) (B * D))
                (f2 : Typ (B * E) (C * E)), 
            sf1 ∼ loop d (arr f1) -> sf2 ∼ loop e (arr f2) ->
            (comp sf1 sf2) ∼
            (loop (d, e) (arr (fun '(a, (c1, c2)) =>
                let (b, c1') := f1 (a, c1) in 
                let (c, c2') := f2 (b, c2) in (c, (c1', c2'))))).
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_simp_comp A B C D E).
        - apply R_bisim_simp_comp_bisim.
        - now constructor.
    Qed.


    Inductive R_bisim_simp_loop (A B C D : Typ) : relation (sf (A * (B * C)) (D * (B * C))) :=
    R_bisim_simp_loop_ : forall (f : (A * B * C) -> (D * B * C)),
        R_bisim_simp_loop _ _ _ _
            (comp (arr unassoc) (comp (arr f) (arr assoc))) 
            (arr (fun '(a, (c0, c1)) => let '(b, c', c0') := f (a, c0, c1) in (b, (c', c0')))).
    
    Lemma R_bisim_simp_loop_bisim (A B C D : Typ) : 
        bisimulation (R_bisim_simp_loop A B C D).
    Proof.
        intros h g H_bisim a b f' H_eq.
        inversion H_bisim; subst; clear H_bisim.
        simpl in *.
        inversion H_eq; subst; clear H_eq.
        destruct a as [a [b c]].
        destruct (f (a, b, c)) eqn:H_res.
        destruct p as [b' c'].
        simpl in *.
        exists (arr (fun '(a0, (c1, c2)) => 
                    let '(b0, c'0, c0') := f (a0, c1, c2) in (b0, (c'0, c0')))).
        split.
        - rewrite H_res. 
          simpl in *. 
          reflexivity.
        - now apply R_bisim_simp_loop_.
    Qed.

    Lemma simplify_loop (A B C D : Typ) :
        forall (f : (A * B * C) -> (D * B * C)), 
            (comp (arr unassoc) (comp (arr f) (arr assoc))) ∼
            (arr (fun '(a, (c0, c1)) => let '(b, c', c0') := f (a, c0, c1) in (b, (c', c0')))).
    Proof.
        intros.
        apply bisimulation_gfp with (R := R_bisim_simp_loop A B C D).
        - apply R_bisim_simp_loop_bisim.
        - now constructor.
    Qed.

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
            simpl.
            apply simplify_arr.
        -   destruct IHsf1 as [C1 [v1 [f1 H1]]].
            destruct IHsf2 as [C2 [v2 [f2 H2]]].
            exists (C1 * C2). exists (v1, v2).
            exists (fun '(a, (c1, c2)) => 
                let (b, c1') := f1 (a, c1) in
                let (c, c2') := f2 (b, c2) in
                (c, (c1', c2'))).
            unfold equiv in *.
            simpl in *.
            now apply simplify_comp.
        -   destruct IHsf as [D [v [f H]]].
            exists D. exists v.
            exists (fun '((a, d), c) => 
                let (b, c') := f (a, c) in
                ((b, d), c')).
            unfold equiv in *.
            simpl in *.
            now apply simplify_first.
        - destruct IHsf as [C0 [v [f H]]].
          exists (C * C0), (c,v).
          exists (fun '(a,(c,c0)) =>
                    let '((b,c'),c0') := f (a,c,c0) in (b,(c',c0'))).
          unfold equiv in *.
          simpl in *.
          transitivity (loop c (loop v (arr f))).
          -- now apply bisimilar_loop.
          -- transitivity ((loop (c,v) (comp (arr unassoc) (comp (arr f) (arr assoc))))).
             + apply arrow_eq_3c.
             + apply bisimilar_loop.
               apply simplify_loop.
    Qed.

End Simplification.




