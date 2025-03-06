
Require Import Categories.Category.Category.
Require Import Categories.Category.Functor.
Require Import Categories.Embedding.CategoryType.
Require Import Categories.Embedding.Monad.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Arith Require Import PeanoNat.

Open Scope type_scope.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Axiom ltb : nat -> nat -> bool.

Notation  "t1 '>>=' t2" := (bind t1 t2) (at level 42, left associativity).
(* Notation  "t1 '>>-' t2"  := (bind t1 (fun x => t2)) (at level 42, left associativity). *)

Definition fmap_productLeft {A B X : Type} 
    (f : A -> B) (p : A * X) : B * X := (f (fst p), snd p).

#[refine] Instance FunctorProductLeft (X : Type) : Functor Typ Typ :=
{
    fobj := fun A => A * X;
    fmap := fun A B => @fmap_productLeft A B X
}.
Proof.
-   intros A. extensionality p. destruct p. reflexivity.
-   intros A B C g f. extensionality p. destruct p. reflexivity.
Defined.

Definition fmap_option := 
    fun {A B : Type} (f : A -> B) (a : option A) => 
        match a with
        | Some a => Some (f a)
        | None => None
        end.

#[refine] Instance FunctorOption : Functor Typ Typ :=
{
    fobj := option;
    fmap := @fmap_option;
}.
Proof.
    -   intros A. extensionality a. destruct a; reflexivity.
    -   intros A B C g f. extensionality a. destruct a; reflexivity.
Defined.

#[refine] Instance MonadOption : Monad :=
{
    M := FunctorOption;
    ret := fun A a => Some a;
    bind := fun A B m f => 
        match m with
        | Some a => f a
        | None => None
        end;
}.
Proof.
-   reflexivity.
-   intros. destruct m; reflexivity.
-   intros. destruct m; reflexivity.
Defined.

Inductive Tag  : Type := 
    | Internal : Type -> Tag
    | Input : Type -> Tag
    | Output : Type -> Tag.

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
        state t -> Cell.

Definition Memory : Type := nat -> option Cell.

Axiom read : forall (A : Type), ref A -> Memory -> option (A * Memory).
Axiom write : forall (A : Type), ref A -> Memory -> A -> option Memory.

Definition St (A : Type) : Type := Memory -> option (A * Memory).

Definition fmap_St {A B : Type} (f : Typ A B) : St A -> St B  := 
    fun st => fun m => 
        (fmap _ ∘ (fmap (FunctorProductLeft Memory))) f (st m).

Check (fmap FunctorOption).

Lemma functor_prop1 : forall A : Type, fmap_St (idty A) = idty (St A).
Proof.
    intro A.
    unfold fmap_St.
    extensionality a.
    extensionality m.
    simpl.
    unfold fmap_option.
    destruct (a m) eqn:H_some; auto.
    f_equal.
    unfold fmap_productLeft.
    destruct p; simpl.
    reflexivity.
Qed.

Lemma functor_prop2 :
forall (A B C : Type) (g : B -> C) (h : A -> B),
    fmap_St g ∘ fmap_St h = fmap_St (g ∘ h).
Proof.
    intros A B C g h.
    simpl.
    extensionality a.
    unfold fmap_St.
    extensionality m.
    simpl.
    destruct (a m) eqn:H_some; auto.
Qed.

#[refine] Instance Functor_St : Functor Typ Typ := 
{
    fobj := St;
    fmap := @fmap_St;
}.
Proof.
- exact functor_prop1.
- exact functor_prop2.
Defined.

Definition ret_st {A : Type} : Typ A (St A) := 
    fun a m => Some (a, m).

Definition bind_st {A B : Type} (a : St A) (f : A -> St B) : St B :=
    fun m => match a m with
    | Some (a, m') => f a m'
    | None => None
    end.

Lemma monad_prop1 : 
forall (a b : Typ) (f : a -> Functor_St b) (x : a), 
    bind_st (ret_st x) f = f x.
Admitted.

Lemma monad_prop2 : forall (a : Typ) (m : Functor_St a), bind_st m ret_st = m.
Admitted.

Lemma monad_prop3 : forall (a b c : Typ) (m : Functor_St a) (f : a -> Functor_St b)
    (g : b -> Functor_St c),
        bind_st (bind_st m f) g = bind_st m (fun x : a => bind_st (f x) g).
Admitted.

#[refine] Instance Monad_St : Monad := {
    ret := @ret_st;
    bind := @bind_st;
}.
Proof.
- exact monad_prop1.
- exact monad_prop2.
- exact monad_prop3.
Defined.

Definition mget {A : Type} (r : ref A) : St A :=
    read A r.

Definition mset {A : Type} (r : ref A) (a : A) : St unit :=
    fun m => fmap FunctorOption (fun m => ((tt,m))) (write A r m a).


Section st_eq.

    Definition is_internal {A : Type} (r : ref A) (σ : Memory) := 
        match σ (id_of_ref r) with
        | Some (Cell_ (Internal _) _) => True
        | _ => False
        end.

    Lemma read_internal_defined :
        forall (A : Type) (r : ref A) σ,
        is_internal r σ -> read A r σ <> None.
    Admitted.

    Lemma read_read : 
    forall (A : Type) (r : ref A) σ (a : A) σ',
        is_internal r σ ->
        read A r σ = Some (a, σ') -> σ = σ'.
    Admitted.

    Lemma read_write : forall (A : Type) (r : ref A) σ (a : A) σ',
    is_internal r σ ->
    read A r σ = Some (a, σ') ->
        write A r σ' a = Some σ.
    Admitted.


    Lemma write_read : 
        forall (A : Type) (r : ref A) σ (a : A) σ',
        write A r σ a = Some σ' -> read A r σ' = Some (a, σ').
    Admitted. 

    Variables (A : Type).
    Variables (r : ref A).
    Variables (x y : A).
    Variable (σ : Memory).

    (* internal *)
    Lemma st_get_get_eq : 
        is_internal r σ ->
        (mget r >>= (fun _ => mget r)) σ = mget r σ.
    Proof.
        intro.
        unfold mget; simpl.
        unfold bind_st; simpl.
        destruct (read A r σ) as [[a σ''] | ] eqn:Heq. 
        -   now replace σ'' with σ in * by now
                (apply read_read in Heq).
        -   reflexivity.
    Qed.
    
    Lemma st_get_set_eq : 
        is_internal r σ ->
            (mget r >>= (mset r)) σ = ret tt σ.
    Proof.
        intro.
        unfold mget, mset; simpl.
        unfold bind_st, ret_st; simpl.
        destruct (read A r σ) as [[a σ'] | ] eqn:Heq. 
        -   destruct (write A r σ' a) as [σ'' | ] eqn:Heq'; simpl.
            +   do 2 f_equal.
                rewrite read_write with (σ := σ) in Heq'. 
                injection Heq'; intros; subst.
                reflexivity.
                assumption.
                assumption.
            +   rewrite read_write with (σ := σ) in Heq'.
                discriminate.
                assumption.
                assumption. 
        -   apply read_internal_defined in H.
            contradiction.
    Qed.

    Lemma st_set_get_eq : 
        is_internal r σ ->
        mset r x >>= (fun tt => mget r) = mset r x >>= (fun tt => ret x).
    Proof.
        intro.
        unfold mset, mget; simpl.
        unfold bind_st, ret_st; simpl.
        apply functional_extensionality; intro m.
        destruct (write A r m x) as [σ' | ] eqn:Heq; simpl.
        apply write_read in Heq.
        assumption.
        reflexivity.
    Qed.

    Lemma st_set_set_eq : 
        is_internal r σ ->
        mset r x >>= (fun tt => mset r y) = mset r y.
    Proof.
        intro.
        unfold mset; simpl.
        unfold bind_st; simpl.
        apply functional_extensionality; intro m; simpl.
        destruct (write A r m x) as [σ' | ] eqn:Heq; simpl.
    Admitted.

    Lemma st_get_eq : 
        is_internal r σ ->
        (mget r >>= (fun _ => ret x)) σ = ret x σ.
    Proof.
        intro.
        unfold mget, ret_st; simpl.
        unfold bind_st; simpl.
        destruct (read A r σ) as [[a σ'] | ] eqn:Heq.
        -   apply read_read in Heq.
            subst.
            reflexivity.
            assumption.
        -   apply read_internal_defined in H.
            contradiction.
    Qed.

End st_eq.

Section st_neq.

    Variables (A B : Type).
    Variables (r : ref A).
    Variables (r' : ref B).
    Variable  (H_neq : id_of_ref r <> id_of_ref r').
    Variables (x : A) (y : B).

    Lemma st_get_get_neq : 
        mget r >>= (fun _ => mget r') = 
            mget r' >>= (fun x => mget r >>= (fun _ => ret x)).
    Proof.
    Admitted.

    Lemma st_get_set_neq : 
        mget r >>= (fun _ => mset r' y) = 
            mset r' y >>= (fun tt => mget r >>= (fun _ => ret tt)).
    Admitted.

    Lemma st_set_get_neq :
        mset r x >>= (fun tt => mget r') = 
            mget r' >>= (fun y => mset r x >>= (fun tt => ret y)).
    Admitted.

    Lemma st_set_set_neq :
        mset r x >>= (fun tt => mset r' y) = 
            mset r' y >>= (fun tt => mset r x).
    Admitted.
End st_neq.


(* erasing *)

Lemma monad_get_ignore : 
    forall (A : Typ) (r : ref A) (x : A),
    mget r >>= (fun _ => ret x) = ret x.
Proof. Admitted.

Definition rsf (A B : Type) := A -> St B.

Definition arr {A B : Type} (f : A -> B) := fun x => ret (f x).

Definition compose {A B C : Type} (f : rsf B C) (g : rsf A B) : rsf A C :=
    fun x => g x >>= f.

Definition first {A B C : Type} (f : rsf A B) : rsf (A * C) (B * C) :=
    fun '(x, z) => 
        f x >>= (fun y => ret (y, z)).

Definition rsfget {A B : Type} (r : ref B) : rsf A (A * B) :=
    fun x => mget r >>= (fun y => ret (x, y)).

Definition rsfset {A B : Type} (r : ref B) : rsf (A * B) A :=
    fun '(x, y) => mset r y >>= (fun tt => ret x).

Inductive RSF : Type -> Type -> Type := 
    | RArr : forall (A B : Type), (A -> B) -> RSF A B
    | RCompose : forall (A B C : Type), RSF A B -> RSF B C -> RSF A C
    | RFirst : forall (A B C : Type), RSF A B -> RSF (A * C) (B * C)
    | RGet : forall (A B : Type), ref B -> RSF A (A * B)
    | RSet : forall (A B : Type), ref B -> RSF (A * B) A.

Fixpoint step {A B : Type} (f : RSF A B) : rsf A B :=
    match f with
    | RArr A B f => arr f
    | RCompose A B C f g => compose (step g) (step f)
    | RFirst A B C f => first (step f)
    | RGet A B r => rsfget r
    | RSet A B r => rsfset r
    end.

Inductive TValue : Type := 
    | TVal : forall (A : Type), A -> TValue.

Record Program := {
    inputs : list Type;
    outputs : list Type;
    internals : list TValue;
    body : RSF unit unit
}.

Fixpoint build (l : list Type) : Type :=
    match l with
    | nil => unit
    | cons A l => A * build l
    end.

Definition k (p : Program) := List.length (internals p).
Definition k_in (p : Program) := List.length (inputs p).
Definition k_out (p : Program) := List.length (outputs p).

Definition init (p : Program) : Memory :=
    fun n => 
        if ltb (k_in p) n && ltb n (k_in p + k p) then 
            match List.nth_error (internals p) (n - k_in p) with
            | Some (TVal A v) => Some (Cell_ (Internal A) v)
            | None => None
            end
        else None.

Definition pull (p : Program) (l : list TValue) : Memory :=
    fun n => 
        if ltb n (k_in p) then 
            match List.nth_error l n with
            | Some (TVal A v) => Some (Cell_ (Input A) (Some v))
            | None => None
            end
        else None.

Definition push (p : Program) (m : Memory) : list TValue :=
    List.map (fun n => 
        match m n with
        | Some (Cell_ (Output A) (Some v)) => TVal A v
        | _ => TVal unit tt
        end) (List.seq (k_in p + k p) (k_out p)).

CoInductive Stream (A : Type) : Type :=
    | Cons : A -> Stream A -> Stream A.

Axiom typed : forall (A B : Type), rsf A B -> A -> Memory -> B * Memory.

Definition typed_step {A B : Type} (f : RSF A B) := 
    typed A B (step f).

CoFixpoint run (p : Program) (m : Memory) (inputs : Stream (list TValue)) : 
    Stream (list TValue) :=
    match inputs with 
    Cons _ v l => 
        match typed_step p.(body) tt (pull p v) with
            (tt, m') => (Cons _ (push p m') (run p m' l))
        end
    end.