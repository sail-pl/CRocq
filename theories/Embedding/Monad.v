From Stdlib.Logic Require Import FunctionalExtensionality.
Require Import CRocq.Category.Category.
Require Import CRocq.Category.Functor.
Require Import CRocq.Category.Transformation.
Require Import CRocq.Category.CategoryCat.
Require Import CRocq.Embedding.CategoryType.
Require Import CRocq.Category.FormalMonad.
Reserved Infix ">>=" (at level 42, left associativity).

(* only for categories with functions as arrows *)
Class Monad  := 
{
    M : Functor Typ Typ;
    ret {a : Typ} : a -> M a;
    bind {a b : Typ} : M a -> (a -> M b) -> M b;
    monad_prop1 : forall {a b : Typ} (f : a -> M b) (x : a),
        bind (ret x) f = f x;
    monad_prop2 : forall {a : Typ} (m : M a),
        bind m ret = m;
    monad_prop3 : forall {a b c : Typ} (m : M a) (f : a -> M b) (g : b -> M c),
        bind (bind m f) g = bind m (fun x => bind (f x) g)
}.

Notation  "t1 '>>=' t2"    := (bind t1 t2) (at level 42, left associativity).


Coercion M : Monad >-> Functor.

#[refine] Instance Klesli (M : Monad) : Category := 
{
    obj := Typ;
    hom := fun a b => a -> M b;
    idty := fun a => ret;
    compose := fun (a b c : Typ) (g : b -> M c) (f : a -> M b) => 
        fun (x : a) => bind (f x) g
}.
Proof.
    - intros a b f.
      apply functional_extensionality.
      intro x.
      apply monad_prop1.
    - intros a b f.
      apply functional_extensionality.
      intro x.
      apply monad_prop2.
    - intros.
      apply functional_extensionality.
      intro x.
      apply monad_prop3.
Defined.    


(* Proof that the 'haskell' monads definition is a particular case of 
the categorical definition (FormalMonad).
*)
Section MonadInNaturalTransformation.
  Context(m : Monad).
  Context(C : Category).
  Context(fm : FormalMonad Typ).

 (* join, an other rule for the fonctionnals monads *)
  Definition join {a : Typ} (mma : m (m a)) : m a :=
  bind mma (fun x => x).

  (* trivial laws 
  fmap m f (ret x) 
    = fmap g b (with g : b -> mb)
    = mb
  ret (f x) = ret b = mb 
  *)
  Lemma fmap_ret_compat : 
    forall {a b : Typ} (f : a -> b) (x : a),
     fmap m f (ret x) = ret (f x).
  Proof.
    intros.
  Admitted.

  (* trivial too but need to be defined in Monad *)
  Lemma fmap_join_compat : 
    forall {a b : Typ} (f : a -> b) (x : m (m a)),
      fmap m f (join x) = join (fmap m (fmap m f) x).
    Proof.
    intros.  
  Admitted.
    
(*Link between ret and eta, a NT using ret *)
Program Definition eta_m : NaturalTransformation (FunctorId Typ) m.(M) :=
  {|
    transform := fun x => m.(ret);
  |}.
Next Obligation.
  intros. simpl.
  apply functional_extensionality. intro.
  rewrite fmap_ret_compat.
  reflexivity.
Qed.

(* link between join and mu, a NT using join*)
Program Definition mu_m : NaturalTransformation (@compose Cat _ _ _ m.(M) m.(M)) m.(M) :=
  {|
    transform := fun x => join;
  |}.
Next Obligation.
  intros. simpl.
  apply functional_extensionality.
  intro.
  rewrite fmap_join_compat.
  reflexivity.
Qed.

#[refine] Instance ParticularMonad : FormalMonad Typ := 
{
  T := m.(M);
  eta := eta_m; 
  mu := mu_m;
}.
Proof. 
  -  
  rewrite (@eta_left_unicity Typ fm) . 

    (*admit.*)
    unfold nf_compose_hor.
    rewrite fid_m_eq_m.
    rewrite eta_left_unicity.
    
  - admit.
  - admit.
Admitted.
  
End MonadInNaturalTransformation.
