Require Import Coq.Logic.FunctionalExtensionality.
From Coq.Setoids Require Import Setoid.
From Coq Require Import ProofIrrelevance.
Require Import Categories.Category.Category.
Require Import Categories.Category.Functor.
Require Import Categories.Embedding.CategoryType.
Require Import Categories.Category.CategoryCat.
Require Import Categories.Embedding.Arrow.  

(*****************************************************************************)
(** * Prelude *)
(*****************************************************************************)


Lemma UIP_refl : 
  forall (a : Type) (x0 : a = a), (@eq (@eq Type a a) x0 (@eq_refl Type a)).
Proof. intros; apply UIP. Qed.

Ltac projT2_ H := 
  rewrite eq_sigT_uncurried_iff in H;
  simpl in H;
  let a := fresh "Heq" in
  inversion H as [HeqT a]; clear H;
  unfold eq_rect in a;
  rewrite (UIP_refl _ HeqT) in a;
  clear HeqT.

Ltac double_projT2_ H := 
  rewrite eq_sigT_uncurried_iff in H;
  simpl in H;
  let a := fresh "Heq" in
  inversion H as [HeqT Htmp]; clear H;
  unfold eq_rect in Htmp;
  rewrite (UIP_refl _ HeqT) in Htmp;
  rewrite eq_sigT_uncurried_iff in Htmp;
  simpl in *;
  inversion Htmp as [HeqT' a]; clear Htmp;
  unfold eq_rect in a;
  rewrite (UIP_refl _ HeqT') in a;
  clear HeqT HeqT'.

Section YampaSemantics.

    CoInductive sf (A B : Type) := 
        sf_ : (A -> B * sf A B) -> sf A B.

    Arguments sf_ [A B] _.

    (* Yampa defines a functor *)

    Definition F (A B : Typ) : Type := B * sf A B.

    CoFixpoint map {A B C : Typ} (f : B -> C) : sf A B -> sf A C :=
        fun '(sf_ g) =>
        sf_ (fun a => 
            let (b, g') := g a in
            (f b, map f g')).

    Definition fmap {A B C : Typ} (f : B -> C) : F A B -> F A C :=
        fun '(b, sf) => (f b, map f sf).

    #[refine] Instance FunctorF (A : Set) : Functor Typ Typ :=
    {
        fobj := fun B => B * sf A B;
        fmap := @fmap A
    }.
    Admitted.


    (* Yampa defines a category *)
    CoFixpoint id (A : Typ) : sf A A :=
    sf_ (fun a => (a, id A)).

    CoFixpoint comp {A B C : Typ} : sf A B -> sf B C -> sf A C :=
        fun '(sf_ f) '(sf_ g) =>
        sf_ (fun a => 
            let (b, f') := f a in
            let (c, g') := g b in
            (c, comp f' g')).

    #[refine] Instance CategorySF : Category :=
            {
                obj := Typ;
                hom := sf;
                idty := @id;
                compose := fun _ _ _ x y => comp y x
            }.
            Admitted.
        
    (* Yampa defines an arrow *)

    CoFixpoint arr {A B : Typ} (f : A -> B) : sf A B :=
        sf_ (fun a => (f a, arr f)).

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
        
End YampaSemantics.

Arguments sf_ [A B] _.


Section YampaBisimulation.

    CoInductive bisimilar : forall {A B : Typ}, sf A B -> sf A B -> Prop :=
    | bisimilar_sf : forall {A B : Typ} (f g : A -> B * sf A B),
        (forall a, fst (f a) = fst (g a)) ->
        (forall a, bisimilar (snd (f a)) (snd (g a))) ->
        bisimilar (sf_ f) (sf_ g).

    Lemma bisimilar_refl : forall {A B : Typ} (f : sf A B), bisimilar f f.
    Proof.
        cofix Ha.
        intros.
        destruct f.
        constructor.
    -   reflexivity.
    -   intro a.
        exact (Ha _ _ (snd (p a))).
    Qed.

    Lemma bisimilar_sym : forall {A B : Typ} (f g : sf A B), bisimilar f g -> bisimilar g f.
    Proof.
        cofix Ha.
        intros.
        destruct H.
        constructor.
        -   symmetry.
            apply H.
        -   intro a.
            apply Ha.
            apply H0.
    Qed.

    Lemma bisimilar_trans : forall {A B : Typ} (f g h : sf A B),
        bisimilar f g -> bisimilar g h -> bisimilar f h.
    Proof.
        cofix Ha.
        intros.
        inversion H; subst.
        inversion H0; subst.
        projT2_ H1.
        projT2_ H2.
        projT2_ H3.
        projT2_ H4.
        projT2_ Heq.
        projT2_ Heq0.
        projT2_ Heq1.
        projT2_ Heq2.
        subst.
        injection Heq0; intros; subst.
        constructor.
        -   congruence.
        -   
            intro a.
            apply Ha with (g := snd (g0 a)).
            apply H6.
            apply H10.
Qed.

    Infix "∼" := bisimilar (at level 60, right associativity): stream_scope.

Open Scope stream_scope.
    Context {A B C : Typ}.


    Record bisimulation (R : relation (sf A B)) : Prop :=
        {
            bisim_hd : forall sf1 sf2 a, 
                R (sf_ sf1) (sf_ sf2) -> 
                    fst (sf1 a) = fst (sf2 a);
            bisim_tl : forall sf1 sf2 a, 
                    R (sf_ sf1) (sf_ sf2) -> R (snd (sf1 a)) (snd (sf2 a))
        }.

    Theorem bisimulation_gfp : 
        forall R, bisimulation R -> forall f g, R f g -> f ∼ g.
    Proof.
        cofix CH.
        intros R H p p0 H0.
        destruct p, p0.
        constructor.
        -   intro.
            now apply bisim_hd with (R := R).
        -   intro.
            apply CH with (R := R).
            assumption.
            now apply bisim_tl.
    Qed.

End YampaBisimulation.

Infix "∼" := bisimilar (at level 60, right associativity): stream_scope.

Open Scope stream_scope.

Section bisimulation.


    Context {A B C : Set}.

    Lemma a : 
    arr (fun x : A => x) = sf_ (fun a => (a, arr (fun x : A => x))).
    Admitted.
    
    Lemma unroll_arr : 
    arr (fun x : A => x) = sf_ (fun a => (a, arr (fun x : A => x))).
    Admitted.

    Lemma unroll_comp : 
    forall {A B C : Type} (f : A -> B * sf A B) (g : B -> C * sf B C),
        comp (sf_ f) (sf_ g) = sf_ (fun a => 
            let (b, f1') := f a in
            let (c, g1') := g b in
            (c, comp f1' g1')).
    Admitted.

    Lemma unroll_first : 
    forall (f : A -> B * sf A B),
        @first _ _ C (sf_ f) = sf_ (fun '(a,c) => 
            let (b, f') := f a in
            ((b,c), first f')).
    Admitted.

    Lemma unroll_loop : 
    forall (c : C) (f : A * C -> (B * C) * sf (A * C) (B * C)),
        loop c (sf_ f) = sf_ (fun a => 
            let '((b, c'), f') := f (a, c) in
            (b, loop c' f')).
    Admitted.

        Lemma bisimilar_id : id A ∼ id A.
        Proof.
            apply bisimilar_refl.
        Qed.

        Inductive R_bisim_comp (A B : Set): relation (sf A B) :=
            R_bisim_comp_ : 
                forall C (f1 f2 : sf A C) (g1 g2 : sf C B), f1 ∼ f2 -> g1 ∼ g2 ->
                R_bisim_comp _ _ (comp f1 g1) (comp f2 g2).

        Lemma R_bisim_comp_bisim : forall (A B : Set), bisimulation (R_bisim_comp A B).
        Proof.
            constructor.
            -   intros.
                inversion H; subst; clear H.
                destruct f1, f2, g1, g2.
                rewrite (unroll_comp p p1) in H0.
                rewrite (unroll_comp p0 p2) in H1.
                injection H0; injection H1; intros; subst; clear H0 H1.
                destruct (p a0) eqn:Heq1.
                destruct (p1 c) eqn:Heq2.
                destruct (p0 a0) eqn:Heq3.
                destruct (p2 c0) eqn:Heq4.
                simpl.
                assert (c = c0).
                {
                    inversion H2; subst.
                    projT2_ H.
                    projT2_ H0.
                    projT2_ Heq.
                    projT2_ Heq0.
                    subst.
                    generalize (H5 a0); intro.
                    rewrite Heq1 in H.
                    rewrite Heq3 in H.
                    simpl in H.
                    assumption.
                }
                assert (b = b0).
                {
                    inversion H3; subst.
                    projT2_ H0.
                    projT2_ H1.
                    projT2_ Heq.
                    projT2_ Heq0.
                    subst.
                    generalize (H6 c0); intro.
                    rewrite Heq2 in H.
                    rewrite Heq4 in H.
                    simpl in H.
                    assumption.
                }
                assumption.
    -           intros.
                inversion H; subst; clear H.
                destruct f1, f2, g1, g2.
                rewrite (unroll_comp p p1) in H0.
                rewrite (unroll_comp p0 p2) in H1.
                injection H0; injection H1; intros; subst; clear H0 H1.
                destruct (p a0) eqn:Heq1.
                destruct (p1 c) eqn:Heq2.
                destruct (p0 a0) eqn:Heq3.
                destruct (p2 c0) eqn:Heq4.
                simpl.
                constructor.
                +   inversion H2; subst.
                    projT2_ H.
                    projT2_ H0.
                    projT2_ Heq.
                    projT2_ Heq0.
                    subst.
                    generalize (H6 a0); intro.
                    rewrite Heq1 in H.
                    rewrite Heq3 in H.
                    simpl in H.
                    assumption.
                +   assert (c = c0).
                    {
                        inversion H2; subst.
                        projT2_ H.
                        projT2_ H0.
                        projT2_ Heq.
                        projT2_ Heq0.
                        subst.
                        generalize (H5 a0); intro.
                        rewrite Heq1 in H.
                        rewrite Heq3 in H.
                        simpl in H.
                        assumption.
                    }
                    inversion H3; subst.
                    projT2_ H0.
                    projT2_ H1.
                    projT2_ Heq.
                    projT2_ Heq0.
                    subst.
                    generalize (H7 c0); intro.
                    rewrite Heq2 in H.
                    rewrite Heq4 in H.
                    simpl in H.
                    assumption.
        Qed.
                

        Lemma bisimilar_comp : forall (f1 f2 : sf A B) (g1 g2 : sf B C),
            f1 ∼ f2 -> g1 ∼ g2 -> comp f1 g1 ∼ comp f2 g2.
        Proof.
            intros.
            apply bisimulation_gfp with (R := R_bisim_comp A C).
            apply R_bisim_comp_bisim.
            apply R_bisim_comp_; assumption.
        Qed.

        Lemma bisimilar_map : forall (f g : B -> B) (sf1 sf2 : sf A B),
            sf1 ∼ sf2 -> map f sf1 ∼ map g sf2.
        Admitted.

        Lemma bisimilar_arr : forall (f g : A -> B),
            (forall a, f a = g a) -> arr f ∼ arr g.
        Admitted.

        Inductive R_bisim_first (A B C : Set): relation (sf (A * C) (B * C)) :=
            R_bisim_first_ : 
                forall (f g : sf A B), f ∼ g -> 
                    R_bisim_first A B C (first f) (first g).

        Lemma R_bisim_first_bisim : forall (A B C : Set), bisimulation (R_bisim_first A B C).
        Admitted.

        Lemma bisimilar_first : forall (f g : sf A B),
            f ∼ g -> @first _ _ C f ∼ first g.
        Proof.
            intros.
            apply bisimulation_gfp with (R := R_bisim_first A B C).
            apply R_bisim_first_bisim.
            apply R_bisim_first_; assumption.
        Qed.

        Inductive R_bisim_loop (A B : Set): relation (sf A B) :=
            R_bisim_loop_ : forall (C : Set)
                (f g : sf (A * C) (B * C)) (c : C), f ∼ g -> 
                    R_bisim_loop A B (loop c f) (loop c g).

        Lemma R_bisim_loop_bisim : 
            forall (A B : Set), bisimulation (R_bisim_loop A B).
        Admitted.

        Lemma bisimilar_loop : forall (x : C)
            (f g : sf (A * C) (B * C)),
            f ∼ g -> loop x f ∼ loop x g.
        Proof.
            intros.
            apply bisimulation_gfp with (R := R_bisim_loop A B).
            apply R_bisim_loop_bisim.
            apply R_bisim_loop_; assumption.
        Qed.

    Axiom bisim_eq : forall (A B : Set) (f g : sf A B), 
        f ∼ g -> f = g.


    
    End bisimulation.


Infix "∼" := bisimilar (at level 60, right associativity): stream_scope.

Open Scope stream_scope.

Add Parametric Relation A B : (sf A B) (@bisimilar A B)
    reflexivity proved by (@bisimilar_refl A B)
    symmetry proved by (@bisimilar_sym A B)
    transitivity proved by (@bisimilar_trans A B)
    as bisimilar_rel.

Add Parametric Morphism (A B C : Set) : (@first A B C)
    with signature (@bisimilar A B) ==> (@bisimilar (A * C) (B * C)) as tl_mor.
Proof.
    apply bisimilar_first.
Qed.

Add Parametric Morphism (A B C : Set) : (@comp A B C)
    with signature (@bisimilar A B) ==> (@bisimilar B C) ==> (@bisimilar A C) as comp_mor.
Proof.
    intros x y H_equiv1 z w H_equiv2.
    now apply bisimilar_comp.
Qed.

Add Parametric Morphism (A B C : Set) : (@loop A B C)
    with signature eq ==> (@bisimilar (A * C) (B * C)) ==> (@bisimilar A B) as loop_mor.
Proof.
    apply bisimilar_loop.
Qed.


Section YampaProperties.

    Parameters A B C D : Set.

    Inductive R1 : relation (sf A B) :=
        R1_ : forall f, R1 (comp (arr (fun x => x)) f) f.

    Lemma ax : 
        arr (fun x : A => x) = sf_ (fun a => (a, arr (fun x : A => x))).
    Admitted.

    Lemma b : forall (f : A -> B * sf A B) a, 
        match comp (arr (fun x:A => x)) (sf_ f) with 
            sf_ g => 
            fst (g a) = fst (f a)
        end.
    Proof.
        intros.
        replace (arr (fun x :A => x)) with 
            (sf_ (fun a => (a, arr (fun x : A => x)))).
        simpl.
        destruct (f a0) eqn:Ha.
        reflexivity.
        symmetry.
        apply ax.
Qed.

Lemma c : forall (f : A -> B * sf A B) a, 
match comp (arr (fun x:A => x)) (sf_ f) with 
    sf_ g => 
    R1 (snd (g a)) (snd (f a))
end.
Proof.
intros.
replace (arr (fun x :A => x)) with 
    (sf_ (fun a => (a, arr (fun x : A => x)))).
simpl.
destruct (f a0) eqn:Ha.
simpl.
apply R1_.
symmetry.
apply ax.
Qed.
    Lemma R1_bisim : bisimulation R1.
    Proof.
        constructor; intros.
        -   inversion H; subst.
            simpl.
            generalize (b sf2 a0); intro.
            rewrite H1 in H0.
            assumption.
        -   inversion H; subst.
            generalize (c sf2 a0); intro.
            rewrite H1 in H0.
            assumption.
    Qed.

    Open Scope category_scope.

    Lemma bisim_eq1 : 
        forall  (sf : sf A B),
            comp (arr (fun x => x)) sf ∼ sf.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R1).
        apply R1_bisim.
        apply R1_.
    Qed.

    Lemma bisim_eq2 : forall (sf : sf A B),
        comp sf (arr (fun x => x)) ∼ sf.
    Admitted.

    Lemma bisim_eq3 : 
        forall (sf1 : sf A B) (sf2 : sf B C) (sf3 : sf C D),
            comp (comp sf1 sf2) sf3 ∼ comp sf1 (comp sf2 sf3).
    Admitted.

    Lemma bisim_eq4 : 
        forall (f : A -> B) (g : B -> C),
            arr (fun x => g (f x)) ∼ comp (arr f) (arr g).
    Admitted.

    Lemma bisim_eq5 :
        forall (sf : sf A B),
            comp (@first _ _ C sf) (arr (fun '(x,y) => x)) ∼ 
                comp (arr (fun '(x,y) => x)) sf.
    Admitted.

    Lemma bisim_eq6 : 
        forall (sf : sf A B) (f : A -> B),
            comp (first sf) (arr (fun '(x,y) => (x, f y))) ∼
                comp (arr (fun '(x,y) => (x,f y))) (first sf).
    Admitted.

    Definition assoc {A B C : Set} : (A * B) * C -> A * (B * C) :=
        fun '((a,b),c) => (a,(b,c)).

    Definition unassoc {A B C : Set} : A * (B * C) -> (A * B) * C :=
        fun '(a,(b,c)) => ((a,b),c).

    Lemma bisim_eq7 : 
        forall (sf : sf A B),
        comp (@first _ _ D (@first _ _ C sf)) (arr assoc) ∼ 
            comp (arr assoc) (first sf).
    Admitted.
    
    Lemma bisim_eq8 : 
        forall (f : A -> B),
            @first _ _ C (arr f) ∼ arr (fun '(x,y) => (f x, y)).
        Admitted.

    Lemma bisim_eq9 :
        forall (sf1 : sf A B) (sf2 : sf B C),
         @first _ _ C (comp sf1 sf2) ∼ comp (first sf1) (first sf2).
    Admitted.

    Lemma bisim_eq10 :
        forall (c : D) (sf1 : sf A B) (sf2 : sf (B * D) (C * D)),
            loop c (comp (first sf1) sf2) ∼ @comp _ _ C sf1 (loop c sf2).
    Admitted.

    Lemma bisim_eq11 :
        forall (c : D) (sf1 : sf (A * D) (B * D)) (sf2 : sf B C),
            loop c (comp sf1 (first sf2)) ∼ comp (loop c sf1) sf2.
    Admitted.

    Lemma bisim_eq12 :
        forall (sf : sf ((A * C) * D) ((B * C) * D)) (c : C) (d : D), 
        loop c (loop d sf) ∼ 
            loop (c,d) (comp (arr unassoc) (comp sf (arr assoc))).
    Admitted.

End YampaProperties.

Section YampaLanguage.

    Inductive SF : Set -> Set -> Type :=
    | Arr : forall {A B : Set}, (A -> B) -> SF A B
    | Comp : forall {A B C : Set}, SF A B -> SF B C -> SF A C
    | First : forall {A B C : Set}, SF A B -> SF (A * C) (B * C)
    | Loop : forall {A B C : Set}, C -> SF (A * C) (B * C) -> SF A B.

    Fixpoint sem {A B : Set} (f : SF A B) : sf A B :=
        match f with
        | Arr h => arr h
        | Comp f1 f2 => comp (sem f1) (sem f2)
        | First f => first (sem f)
        | Loop c f => loop c (sem f)
        end.

    Definition equiv {A B : Set} : SF A B -> SF A B -> Prop :=
        fun f g => sem f ∼ sem g.

    Infix "≡" := equiv (at level 60, right associativity): stream_scope.

End YampaLanguage.

Infix "≡" := equiv (at level 60, right associativity): stream_scope.


Section YampaEquivalence.
    
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
        rewrite H, H0.
        reflexivity.
    Qed.
    
    Lemma equiv_loop : 
        forall (c : C) (f g : SF (A * C) (B * C)),
            f ≡ g -> Loop c f ≡ Loop c g.
    Proof.
        unfold equiv; simpl; intros.
        rewrite H.
        reflexivity.
    Qed.

Check tt.

    Inductive R_simpl_eq1 : 
        relation (sf A B) :=
    | R_simpl_eq1_ :
        forall (f : A -> B), 
            R_simpl_eq1 (arr f) (loop tt (arr (fun '(x,y) => (f x,y)))).
            
    Lemma R_simpl_eq1_bisim : bisimulation R_simpl_eq1.
    Proof.
    Admitted.

    Lemma simplification : 
        forall (f : SF A B),
            exists (C : Set) (c : C) (g : A * C -> B * C), f ≡ Loop c (Arr g).
    Proof.
        intro f.
        induction f.
        -   exists unit.
            exists tt.
            exists (fun '(x,y) => (b0 x, y)).
            unfold equiv; simpl.
            generalize (bisimulation_gfp _ R_simpl_eq1_bisim ); intro.
            (* modifier la définition de bisimulation pour ne pas forcer
                à avoir des éléments de la forme sf_ f *)
    Admitted.



End YampaEquivalence.
