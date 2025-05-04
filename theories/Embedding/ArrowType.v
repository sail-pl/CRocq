From Stdlib.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From Stdlib.Setoids Require Import Setoid.
From CRocq.Category Require Import Category Functor CategoryCat.
From CRocq.Algebra Require Import Coalgebra.
From CRocq.Embedding Require Import CategoryType Arrow.

#[refine] Instance ArrowType : Arrow :=
{
    Ar := fun A B => A -> B;
    arr {A B : Type} := idty (A -> B);
    arrcomp {A B C : Type} := 
        fun x y => compose y x;
    first {A B C : Type} := 
        fun f x => (f (fst x), snd x);
  }. 
Proof.
    all : 
        intros; 
        extensionality x; 
        first [ reflexivity |
                destruct x as [x y]; 
                try destruct x; reflexivity].
Defined.

#[refine] Instance ArrowLoopType : ArrowLoop :=
{
    loop := fun {A B C : Type} (c : C) (f : Ar (A * C) (B * C)) =>
        fun (a : A) => fst (f (a, c))
}.
Proof.
    -   intros.
        reflexivity.
    -   intros.
        reflexivity.
    -   intros.
        extensionality u; simpl.
        destruct (f (u,x,y)) as [[] ] eqn:Heq.
        reflexivity.
Defined.
