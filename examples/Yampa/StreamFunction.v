From Stdlib.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From Stdlib.Setoids Require Import Setoid.
From CRocq.Category Require Import Category Functor CategoryCat.
From CRocq.Algebra Require Import Coalgebra CatCoalgebra.
From CRocq.Embedding Require Import Arrow.
From CRocq.Embedding Require Import CategoryType.
From CRocq.Embedding Require Import ArrowType.


CoInductive corec (A B : Type) := 
    corec_ : (A -> B * corec A B) -> corec A B.
    
Arguments corec_ [A B] _.

Section CoAlgebra.

    Variables (A B : Type).

    #[refine] Instance FCorec : Functor Typ Typ :=
    {
        fobj := fun X => A -> B * X;
        fmap := fun {X Y} (f : X -> Y) p a => second f (p a)
    }.
    Proof.
    -   intro x.
        extensionality f.
        extensionality a.
        simpl.
        destruct (f a); simpl. 
        reflexivity.
    -   intros x y z f g.
        extensionality h.
        extensionality a.
        simpl.
        destruct (h a); simpl.
        reflexivity.
    Defined.

    (* corec A B is a coalgebra for FCorec A B *)

    Instance CoAlgebrasf : CoAlgebra FCorec := 
    {
        coalgebra_obj := corec A B;
        coalgebra_morph := 
            fun sf => match sf with corec_ f => f end 
    }.

    (* corec A B is terminal in the categoty of 
        FCorec A B - algebras *)

    (* iterate step X is the unique morphism from 
        X to corec A B ... *)

    CoFixpoint iterate {X : Type} 
        (step : X -> A -> B * X) (x : X) : corec A B := 
            corec_ (fun a => let (b,x') := step x a in
        (b, iterate step x')).

    #[refine] Instance G (X : CoAlgebra FCorec) : 
            CoAlgebraMorphism FCorec X CoAlgebrasf :=
        {
            coalgebramorphism_morph := 
                iterate (coalgebra_morph X)
        }.
    Admitted.

    #[refine] Instance TerminalCoRec 
        : terminal (CoAlgebraCat FCorec) := 
    {
        terminal_obj := CoAlgebrasf;
        terminal_morph := G
    }.
    Proof.
    Admitted.

End CoAlgebra.

