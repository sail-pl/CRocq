Require Import Coq.Logic.FunctionalExtensionality.
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

    Definition t (A B : Set) := A -> F A B.

    CoFixpoint id (A : Typ) : sf A A :=
    sf_ (fun a => (a, id A)).

    CoFixpoint comp {A B C : Typ} : sf A B -> sf B C -> sf A C :=
        fun '(sf_ f) '(sf_ g) =>
        sf_ (fun a => 
            let (b, f') := f a in
            let (c, g') := g b in
            (c, comp f' g')).

    (* arrow *)
    CoFixpoint map {A B C : Typ} (f : B -> C) : sf A B -> sf A C :=
        fun '(sf_ g) =>
        sf_ (fun a => 
            let (b, g') := g a in
            (f b, map f g')).

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

    Definition fmap {A B C : Typ} (f : B -> C) : F A B -> F A C :=
        fun '(b, sf) => (f b, map f sf).

    #[refine] Instance FunctorF (A : Set) : Functor Typ Typ :=
    {
        fobj := fun B => B * sf A B;
        fmap := @fmap A
    }.
    Admitted.

    #[refine] Instance CategorySF : Category :=
    {
        obj := Typ;
        hom := sf;
        idty := @id;
        compose := fun _ _ _ x y => comp y x
    }.
    Admitted.

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





End Yampa.
(* Inductive SF (A B : Set) := *)