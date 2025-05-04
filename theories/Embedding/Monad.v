From Stdlib.Logic Require Import FunctionalExtensionality.
Require Import CRocq.Category.Category.
Require Import CRocq.Category.Functor.
Require Import CRocq.Embedding.CategoryType.
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