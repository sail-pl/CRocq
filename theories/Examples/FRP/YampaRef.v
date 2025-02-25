
Require Import Categories.Category.Category.
Require Import Categories.Category.Functor.
Require Import Categories.Embedding.CategoryType.
Require Import Categories.Embedding.Monad.

Open Scope type_scope.

Notation  "t1 '>>=' t2" := (bind t1 t2) (at level 42, left associativity).
Notation  "t1 '>>-' t2"  := (bind t1 (fun x => t2)) (at level 42, left associativity).


Inductive Tag := 
    | Internal : Typ -> Tag
    | Input : Typ -> Tag
    | Output : Typ -> Tag.

Definition type (t : Tag) := 
    match t with
    | Internal t => t
    | Input t => t
    | Output t => t
    end.

Definition state (s : Tag) := 
    match s with
    | Internal t => t
    | Input t => option t
    | Output t => option t
    end.

Inductive ref : Type -> Type := 
    | Ref_ : forall (t : Tag), nat -> ref (type t). 

Definition id_of_ref {A : Type} (r : ref A) : nat := 
    match r with
    | Ref_ _ id => id
    end.
    
Inductive Cell : Type :=
    | Cell_ : forall (t : Tag), 
        type t -> state t -> Cell.

Definition Memory := nat -> Type.

Axiom read : forall (A : Typ), ref A -> Memory -> option (A * Memory).
Axiom write : forall (A : Typ), ref A -> Memory -> A -> option Memory.

Definition St (A : Typ) := Memory -> option (A * Memory).

Lemma functor_prop1 : 
    forall a : Typ,
    (fun (a0 : St a) (m : Memory) =>
    match a0 m with
    | Some (a1, m') => Some (idty a a1, m')
    | None => None
    end) = idty (St a).
Admitted.

Lemma functor_prop2 :
    forall (a b c : Typ) (g : Typ b c) (h : Typ a b),
    (fun (a0 : St b) (m : Memory) =>
    match a0 m with
    | Some (a1, m') => Some (g a1, m')
    | None => None
    end)
    ∘ (fun (a0 : St a) (m : Memory) =>
    match a0 m with
    | Some (a1, m') => Some (h a1, m')
    | None => None
    end) =
    (fun (a0 : St a) (m : Memory) =>
    match a0 m with
    | Some (a1, m') => Some ((g ∘ h) a1, m')
    | None => None
    end).
Admitted.

#[refine] Instance Functor_St : Functor Typ Typ := 
{
    fobj := St;
    fmap := fun A B f => fun a m => match a m with
    | Some (a, m') => Some (f a, m')
    | None => None
    end;
}.
Proof.
- exact functor_prop1.
- exact functor_prop2.
Defined.

Definition ret {A : Typ} : Typ A (St A) := 
    fun a m => Some (a, m).

Definition bind {A B : Typ} (a : St A) (f : A -> St B) : St B :=
    fun m => match a m with
    | Some (a, m') => f a m'
    | None => None
    end.

Definition get {A : Typ} (r : ref A) : St A :=
    fun m => read A r m.

Definition set {A : Typ} (r : ref A) (a : A) : St unit :=
    fun m => match write A r m a with
    | Some m' => Some (tt, m')
    | None => None
    end.

Lemma monad_prop1 : 
    forall (a b : Typ) (f : a -> Functor_St b) (x : a), 
        bind (ret x) f = f x.
Admitted.

Lemma monad_prop2 : forall (a : Typ) (m : Functor_St a), bind m ret = m.
Admitted.

Lemma monad_prop3 : forall (a b c : Typ) (m : Functor_St a) (f : a -> Functor_St b)
    (g : b -> Functor_St c),
        bind (bind m f) g = bind m (fun x : a => bind (f x) g).
Admitted.

#[refine] Instance Monad_St : Monad := {
    ret := @ret;
    bind := @bind;
}.
Proof.
- exact monad_prop1.
- exact monad_prop2.
- exact monad_prop3.
Defined.

Lemma monad_prop8 : 
    forall (A B : Typ) (r : ref A) (r' : ref B),
    get r >>= (fun _ => get r') = 
        get r' >>= (fun x => get r >>= (fun y => ret x)).
Admitted.

Lemma monad_prop9 : 
    forall (A B : Typ) (r : ref A) (r' : ref B) (x : A) (y : B),
        get r >>= (fun _ => set r' y) = 
        set r' y >>= (fun tt => get r >>= (fun _ => ret tt)).


Lemma monad_prop4 : 
    forall (A : Typ) (r : ref A),
    get r >>= (fun _ => get r) = get r.
Admitted.

Lemma monad_prop5 : 
    forall (A : Typ) (r : ref A),
    get r >>= set r = ret tt.
Admitted.

Lemma monad_prop6 : 
    forall (A : Typ) (r : ref A) (x : A),
    set r x >>= (fun tt => get r) = set r x >>= (fun tt => ret x).
Admitted.

Lemma monad_prop7 : 
    forall (A : Typ) (r : ref A) (x y : A),
    set r x >>= (fun tt => set r y) = set r y.
Admitted.


    (set r x) (fun tt => get r') = 
        bind (get r') (fun y => bind (set r x) (fun tt => ret y)).


(* notation bind *)