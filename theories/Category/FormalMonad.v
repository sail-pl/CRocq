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

Definition whiskering_left {C D E : Category} {F G : Functor D E}
  (N : NaturalTransformation F G) (H : Functor C D) :
    NaturalTransformation (FunctorComp _ _ _ F H) (FunctorComp _ _ _ G H).
  refine {|
    transform := fun a => N (H a);
    transform_spec := _ ;
  |}.
Proof.

Definition whiskering_right {C D E : Category} {F G : Functor C D}
  (N : NaturalTransformation F G) (H : Functor D E) : 
    NaturalTransformation (FunctorComp _ _ _ H F) (FunctorComp _ _ _ H G).
  refine {|
    transform := fun a => fmap H (transform N a); 
    transform_spec := _ ;
  |}.
Proof.


(*formal definition of monad *)
Class FormalMonad (C : Category) := {
  U : Functor C C;
  etaU : NaturalTransformation (FunctorId C) U;  
  muU : NaturalTransformation (FunctorComp C C C U U) U;

  eta_right_unicity_U :
    nf_compose U (FunctorComp C C C U U) U muU (NaturalTransformation (FunctorComp _ _ _ U (FunctorId C)) (FunctorComp _ _ _ U U))
      = nf_idty U;  
}.

