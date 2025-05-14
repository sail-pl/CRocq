From CRocq.Category Require Import Category Functor Transformation.
From CRocq.Category Require Import CategoryCat.


(* formal definition of monad in Category theory with morphisms as naturals transitions *)
Class FormalMonadHom (C : Category) := {
  T : Functor C C; 
  eta : forall (a : C), hom a (T a);
  mu  : forall (a : C), hom (T (T a)) (T a);

  eta_right_unicity : forall (a : C),
    mu a ∘ eta (T a) = idty (T a);

  eta_left_unicity : forall (a : C),
    mu a ∘ (fmap T (eta a)) = idty (T a);

  mu_associativity : forall (a : C),
    mu a ∘ (fmap T (mu a)) = mu a ∘ mu (T a);
}.
(*
Instance IdFunctor (C : Category) : Functor C C := {
  fobj {a : C} := C  C ;
  fmap {a b : C} := C a b -> C a b; 
}.


Class CompFunctor (C D E : Category) (F : Functor C D) (G : Functor D E) : Type := {
  fobj : C -> E ;
  fmap {a b : C} : forall (f : C a b) ,  C a b -> E (fobj (D (fobj a) (fobj b))) (fobj (D (fobj a) (fobj b))); 


}.


(* formal definition of monad *)
Class FormalMonad (C : Category) := {
  U : Functor C C;
  etaU : NaturalTransformation (FunctorId C) U;  
  muU : forall {F : Functor C C}, NaturalTransformation (FunctorComp C C C F) U;
}.
*)
