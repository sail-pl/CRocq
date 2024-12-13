From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.

From Categories.Category Require Import Category.

Class Functor (C1 : Category) (C2 : Category) : Type := 
{
  fobj : @obj C1 -> @obj C2;
  fmap : forall {A B : @obj C1}, @hom C1 A B -> @hom C2 (fobj A) (fobj B);
  fmap_identity : forall {A : @obj C1}, 
    fmap (@idty C1 A) = @idty C2 (fobj A);
  fmap_compose : forall {A B C : @obj C1} (g : @hom C1 B C) (h : @hom C1 A B),
    (fmap g ∘ fmap h) = fmap (g ∘ h)
}.

Coercion fobj : Functor >-> Funclass.