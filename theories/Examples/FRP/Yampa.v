Require Import Coq.Logic.FunctionalExtensionality.
From Coq.Setoids Require Import Setoid.
Require Import Categories.Category.Category.
Require Import Categories.Category.Functor.
Require Import Categories.Embedding.CategoryType.
Require Import Categories.Category.CategoryCat.

Module Type WithCategory.

    Declare Instance C : Category.
    Declare Instance CC : CartesianClosed C.

End WithCategory.

Module Yampa (Import W : WithCategory).

    CoInductive sf (A B : Type) := 
        sf_ : (A -> B * sf A B) -> sf A B.

    Arguments sf_ [A B] _.

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

    Definition t (A B : Set) := A -> F A B.

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
        

    (* arrow *)

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
    


    (* map id -> id *)



    Inductive SF : Type -> Type -> Type :=
    | Arr : forall {A B : Set}, (A -> B) -> SF A B
    | Comp : forall {A B C : Set}, SF A B -> SF B C -> SF A C
    | First : forall {A B C : Set}, SF A B -> SF (A * C) (B * C)
    | Loop : forall {A B C : Set}, C -> SF (A * C) (B * C) -> SF A B.

    Fixpoint sem {A B : Typ} (f : SF A B) : sf A B :=
        match f with
        | Arr h => arr h
        | Comp f1 f2 => comp (sem f1) (sem f2)
        | First f => first (sem f)
        | Loop c f => loop c (sem f)
        end.

    CoInductive bisimilar : forall {A B : Typ}, sf A B -> sf A B -> Prop :=
    | bisimilar_sf : forall {A B : Typ} (f g : A -> B * sf A B),
        (forall a, fst (f a) = fst (g a)) ->
        (forall a, bisimilar (snd (f a)) (snd (g a))) ->
        bisimilar (sf_ f) (sf_ g).

    Lemma bisimilar_refl : forall {A B : Typ} (f : sf A B), bisimilar f f.
    Admitted.

    Lemma bisimilar_sym : forall {A B : Typ} (f g : sf A B), bisimilar f g -> bisimilar g f.
    Admitted.

    Lemma bisimilar_trans : forall {A B : Typ} (f g h : sf A B),
        bisimilar f g -> bisimilar g h -> bisimilar f h.
    Admitted.

    Infix "∼" := bisimilar (at level 60, right associativity): stream_scope.
    
    Open Scope stream_scope.

    Section bisimulation.

        Context {A B C : Typ}.

        Lemma bisimilar_id : id A ∼ id A.
        Admitted.

        Lemma bisimilar_comp : forall (f1 f2 : sf A B) (g1 g2 : sf B C),
            f1 ∼ f2 -> g1 ∼ g2 -> comp f1 g1 ∼ comp f2 g2.
        Admitted.

        Lemma bisimilar_map : forall (f g : B -> B) (sf1 sf2 : sf A B),
            sf1 ∼ sf2 -> map f sf1 ∼ map g sf2.
        Admitted.

        Lemma bisimilar_arr : forall (f g : A -> B),
            (forall a, f a = g a) -> arr f ∼ arr g.
        Admitted.

        Lemma bisimilar_first : forall (f g : sf A B),
            f ∼ g -> @first _ _ C f ∼ first g.
        Admitted.

        Lemma bisimilar_loop : forall (x : C)
            (f g : sf (A * C) (B * C)),
            f ∼ g -> loop x f ∼ loop x g.
        Admitted.

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
        -   now apply bisim_hd with (R := R).
        -   apply CH with (R := R).
            assumption.
            now apply bisim_tl.

        constructor; intros.
        -   now apply bisim_hd with (R := R).
        -   apply CH with (R := R).
            assumption.
            now apply bisim_tl.
    Qed.
       

    Inductive R1 : relation (sf A B) :=
        R1_ : forall f, R1 (comp (arr (fun x => x)) f) f.

    Lemma a : 
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
        apply a.
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
apply a.
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

    Lemma bisim_eq1 : forall  (f : sf A B),
        comp (arr (fun x => x)) f ∼ f.
    Proof.
        intros.
        apply bisimulation_gfp with (R := R1).
        apply R1_bisim.
        apply R1_.
    Qed.

    End bisimulation.

End Yampa.
