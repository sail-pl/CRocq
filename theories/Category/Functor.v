From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.

From Categories.Category Require Import Category.

(** * Functor *)
(** ** Definition *)
(** 
  A functor [F : Functor C D] is a mapping between the categories [C] and [D]. 
  - each object [a : C] is mapped to an object [fobj F a : D] and 
  - each morphism [f : C a b] is mapped to  a morphism [fmap F f : C (F a) (F b)] 
  This mapping must preserve identities and composition.
  The object mapping [fobj F a] is denoted by [F a].
  *)

Class Functor (C : Category) (D : Category) : Type := {
  fobj : C -> D;
  fmap {a b : C} : C a b -> D (fobj a) (fobj b);
  functors_preserve_identities {a : C} : 
    fmap (idty a) = idty (fobj a);
  functors_preserve_composition {a b c : C} : 
      forall (g : C b c) (h : C a b),
        (fmap g ∘ fmap h) = fmap (g ∘ h) }.

Arguments fmap { _ _ } Functor { _ _ }.

Coercion fobj : Functor >-> Funclass.
