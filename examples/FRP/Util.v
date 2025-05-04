From Stdlib.Logic Require Import FunctionalExtensionality ProofIrrelevance.

Lemma UIP_refl : 
  forall (a : Set) (x0 : a = a), (@eq (@eq Set a a) x0 (@eq_refl Set a)).
Proof. intros; apply UIP. Qed.

Ltac projT2_ H := 
  rewrite eq_sigT_uncurried_iff in H;
  simpl in H;
  let a := fresh "Heq" in
  inversion H as [HeqT a]; clear H;
  unfold eq_rect in a;
  rewrite (UIP_refl _ HeqT) in a;
  clear HeqT.

Ltac double_projT2_ H := 
  rewrite eq_sigT_uncurried_iff in H;
  simpl in H;
  let a := fresh "Heq" in
  inversion H as [HeqT Htmp]; clear H;
  unfold eq_rect in Htmp;
  rewrite (UIP_refl _ HeqT) in Htmp;
  rewrite eq_sigT_uncurried_iff in Htmp;
  simpl in *;
  inversion Htmp as [HeqT' a]; clear Htmp;
  unfold eq_rect in a;
  rewrite (UIP_refl _ HeqT') in a;
  clear HeqT HeqT'.
