From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From Coq.Setoids Require Import Setoid.
From Categories.Category Require Import Category Functor CategoryCat.
From Categories.Algebra Require Import Coalgebra.
From Categories.Embedding Require Import CategoryType Arrow.

#[refine] Instance ArrowType : Arrow :=
{
    Ar := fun A B => A -> B;
    arr {A B : Type} := id (A -> B);
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
