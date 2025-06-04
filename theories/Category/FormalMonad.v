From CRocq.Category Require Import Category Functor Transformation.
From CRocq.Category Require Import CategoryCat.

(* formal definition of monad in Category theory with morphisms as naturals transitions *)
Class FormalMonadHom (C : Category) := {
  U : Functor C C; 
  etaU : forall (a : C), hom a (U a);
  muU  : forall (a : C), hom (U (U a)) (U a);

  etaU_right_unicity : forall (a : C),
    muU a ∘ etaU (U a) = idty (U a);

  etaU_left_unicity : forall (a : C),
    muU a ∘ (fmap U (etaU a)) = idty (U a);

  muU_associativity : forall (a : C),
    muU a ∘ (fmap U (muU a)) = muU a ∘ muU (U a);
}.

Section ComposeIdentities.
  Context {C D : Category}.
  Context (F : Functor C D).

  Program Definition Nf_F_id_left : NaturalTransformation F (@compose Cat C D D (FunctorId D) F) := 
  {|
      transform := fun c => idty (F c);
  |}.
  Next Obligation.
    intros. simpl.
    rewrite compose_left_idty.
    rewrite compose_right_idty.
    reflexivity.
  Qed.

  Program Definition Nf_F_id_right : NaturalTransformation F (@compose Cat C C D F (FunctorId C)):=
  {|
      transform := fun c => idty (F c);
  |}.
  Next Obligation.
    intros. simpl.
    rewrite compose_left_idty.
    rewrite compose_right_idty.
    reflexivity.
  Qed.

End ComposeIdentities.

Section test1.

  Context (C D E B : Category).
  Context (F : Functor C D).
  Context (G : Functor D E).
  Context (H : Functor E B).

Program Definition F_compose_assoc : NaturalTransformation (@compose Cat C D B (@compose Cat D E B H G) F) 
  (@compose Cat C E B H (@compose Cat C D E G F)) :=
  {|
    transform := fun c => idty ((@compose Cat C D B (@compose Cat D E B H G) F) c);
  |}.
  Next Obligation.
  intros. simpl.
  rewrite compose_right_idty.
  rewrite compose_left_idty.
  reflexivity.
Qed.

End test1.

(*formal definition of monad *)
Class FormalMonad (C : Category) := {
  T : Functor C C;
  eta : NaturalTransformation (FunctorId C) T;  
  mu : NaturalTransformation (@compose Cat C C C T T) T;

  eta_left_unicity :
    nf_compose _ _ _ (nf_compose _ _ _ mu (nf_compose_hor (nf_idty T) eta)) (@Nf_F_id_left C C T)
      = nf_idty T;

  eta_right_unicity :
    nf_compose _ _ _ (nf_compose _ _ _ mu (nf_compose_hor eta (nf_idty T))) (@Nf_F_id_right C C T) 
      = nf_idty T;

  mu_associativity : 
    nf_compose _ _ _ mu (nf_compose_hor (nf_idty T) mu) 
    = nf_compose _ _ _ (nf_compose _ _ _ mu (nf_compose_hor mu (nf_idty T))) (@F_compose_assoc C C C C T T T) ;
}.

