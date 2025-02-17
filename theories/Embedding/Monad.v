Require Import Categories.Category.Category.
Require Import Categories.Category.Functor.
Require Import Categories.Embedding.CategoryType.
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
