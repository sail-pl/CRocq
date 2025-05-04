Require Import CRocq.Category.Category.
Require Import CRocq.Category.Functor.
Require Import CRocq.Embedding.CategoryType.
Require Import CRocq.Embedding.Monad.
Require Import Map Util.
From Stdlib.Logic Require Import FunctionalExtensionality.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ProofIrrelevance.

(** * Memory modelisation *)

(** ** Option monad *)

Notation  "t1 '>>=' t2" := (bind t1 t2) (at level 42, left associativity).

Definition fmap_option {A B : Type} (f : A -> B) (a : option A) :=
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
  - intro A.
    apply functional_extensionality.
    now intros []; simpl.
  - intros A B C g h.
    apply functional_extensionality.
    now intros []; simpl.
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
  - reflexivity.
  - intros. destruct m; reflexivity.
  - intros. destruct m; reflexivity.
Defined.

(** ** Tag *)

Inductive Tag  : Type := 
  | Internal : Type -> Tag
  | Input : Type -> Tag
  | Output : Type -> Tag.


Definition type_of_tag (s : Tag) :=
  match s with
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

(** ** Reference *)


Inductive ref : Type -> Type := Ref_ : forall (t : Tag), nat -> ref (type_of_tag t). 

Definition id_of_ref {A : Type} (r : ref A) : nat :=
  let (_,id) := r in id.

Definition tag_of_ref {A : Type} (r : ref A) : Tag :=
  let (t,_) := r in t.

(** ** Concrete memory cell*)

Inductive Cell : Type := Cell_ : forall (t : Tag), state t -> Cell.

Definition type_of_cell (c : Cell) :=
  match c with
    Cell_ t _ => type_of_tag t
  end. 

(** ** Concrete memory *)

Definition Memory : Type := @partial_map Cell.

Axiom typ_dec : forall (A B : Type), {A = B} + {A <> B}. 

(** *** read *)

Definition read {A : Type} (r : ref A) (mem : Memory) : option (A * Memory) :=
match mem (id_of_ref r) with
  | Some (Cell_ (Internal B) v) => 
    match typ_dec B A with
      | left eq => Some (eq_rect B (fun t => t) v A eq, mem)
      | right _ => None
    end
  | Some (Cell_ (Input B) (Some v)) =>
    match typ_dec B A with
      | left eq =>  let mem' := ((id_of_ref r) ↦ (Cell_ (Input B) None) ; mem)%pm in
                    Some (eq_rect B (fun t => t) v A eq, mem')
      | right _ => None
    end
  | _ => None
end.

Lemma read_mem_spec {A : Type} (r : ref A)  (v: A) (mem mem' : Memory) : 
  read r mem = Some (v, mem') -> 
    mem' = mem \/
    mem' = ((id_of_ref r) ↦ (Cell_ (Input A) None) ; mem)%pm.
Proof.
  unfold read; intro H_read.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c as [t].
    destruct t.
    -- destruct (typ_dec T A); subst.
       + simpl in *.
         inversion H_read; subst; clear H_read.
         now left.
       + inversion H_read.
    -- destruct s. 
       + destruct (typ_dec T A); subst.
         ++ simpl in *.
            inversion H_read; subst; clear H_read.
            now right.
         ++ inversion H_read.
       + inversion H_read.
    -- inversion H_read.
  - inversion H_read.
Qed. 

Lemma read_internal_spec {A : Type} (r : ref A) (v: A) (mem : Memory) :
  mem (id_of_ref r) = Some (Cell_ (Internal A) v) -> read r mem = Some (v, mem).
Proof.
  unfold read; intro H_read.
  rewrite H_read.
  destruct (typ_dec A A); subst.
  - do 2 f_equal.
    unfold eq_rect.
    assert (@eq _ e (eq_refl)).
    -- apply UIP.
    -- now rewrite H.
  - exfalso.
    apply n.
    reflexivity.
Qed.

Lemma read_input_spec {A : Type} (r : ref A) (v: A) (mem : Memory) :
  mem (id_of_ref r) = Some (Cell_ (Input A) (Some v)) -> 
  read r mem = Some (v, ((id_of_ref r) ↦ (Cell_ (Input A) None) ; mem)%pm).
Proof.
  unfold read; intro H_read.
  rewrite H_read.
  destruct (typ_dec A A); subst.
  - do 2 f_equal.
    unfold eq_rect.
    assert (@eq _ e (eq_refl)).
    -- apply UIP.
    -- now rewrite H.
  - exfalso.
    apply n.
    reflexivity.
Qed.

Lemma read_update_neq {A : Type} (r : ref A) (v : A) (c : Cell) 
                      (r' : ref (type_of_cell c)) (mem mem' : Memory) :
  (id_of_ref r) <> (id_of_ref r') ->
  read r mem = Some (v,mem') ->
  read r (id_of_ref r' ↦ c; mem)%pm = Some (v,(id_of_ref r' ↦ c; mem')%pm).
Proof.
  unfold read.
  intros H_neq H_read.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c0,t.
    -- rewrite p_update_neq; auto.
       rewrite H_get.
       destruct (typ_dec T A); subst.
       + simpl in *.
         inversion H_read; subst.
         reflexivity.
       + inversion H_read.
    -- rewrite p_update_neq; auto.
       destruct s;
       rewrite H_get.
       + destruct (typ_dec T A); subst.
         ++ simpl in *.
            inversion H_read; subst.
            do 2 f_equal.
            apply p_update_permute.
            auto.
         ++ inversion H_read.
       + inversion H_read.
    -- inversion H_read.
  - inversion H_read. 
Qed.

(** *** write *)

Definition write {A : Type} (r : ref A) (v : A) (mem : Memory) : option Memory :=
match mem (id_of_ref r) with
  | Some (Cell_ (Internal B) _) => 
    match typ_dec B A with
      | left eq => Some ((id_of_ref r) ↦ (Cell_ (Internal A) v) ; mem)%pm
      | right _ => None
    end
  | Some (Cell_ (Output B) None) =>
    match typ_dec B A with
      | left eq => Some ((id_of_ref r) ↦ (Cell_ (Output A) (Some v)) ; mem)%pm
      | right _ => None
    end
  | _ => None
end.

Lemma write_mem_spec {A : Type} (r : ref A)  (v: A) (mem mem' : Memory) : 
  write r v mem = Some mem' -> 
    mem' = ((id_of_ref r) ↦ (Cell_ (Internal A) v) ; mem)%pm \/
    mem' = ((id_of_ref r) ↦ (Cell_ (Output A) (Some v)) ; mem)%pm.
Proof.
  unfold write; intro H_write.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c as [t].
    destruct t.
    -- destruct (typ_dec T A); subst.
       + simpl in *.
         inversion H_write; subst; clear H_write.
         now left.
       + inversion H_write.
    -- inversion H_write.
    -- destruct s. 
       + inversion H_write.
       + destruct (typ_dec T A); subst.
         ++ simpl in *.
            inversion H_write; subst; clear H_write.
            now right.
         ++ inversion H_write.
  - inversion H_write.
Qed. 

Lemma write_internal_spec {A : Type} (r : ref A) (v v': A) (mem : Memory) :
  mem (id_of_ref r) = Some (Cell_ (Internal A) v') -> 
  write r v mem = Some ((id_of_ref r) ↦ (Cell_ (Internal A) v) ; mem)%pm.
Proof.
  unfold write; intro H_write.
  rewrite H_write.
  destruct (typ_dec A A); subst.
  - reflexivity.
  - exfalso.
    apply n.
    reflexivity.
Qed.

Lemma write_output_spec {A : Type} (r : ref A) (v : A) (mem : Memory) :
  mem (id_of_ref r) = Some (Cell_ (Output A) None) -> 
  write r v mem = Some ((id_of_ref r) ↦ (Cell_ (Output A) (Some v)) ; mem)%pm.
Proof.
  unfold write; intro H_write.
  rewrite H_write.
  destruct (typ_dec A A); subst.
  - reflexivity.
  - exfalso.
    apply n.
    reflexivity.
Qed.

(** ** Compatible *)

Definition is_compat {A : Type} (r : ref A) (mem : Memory) :=
  match mem (id_of_ref r) with
    | Some (Cell_ (Internal B) _) => B = A 
    | Some (Cell_ (Input B) (Some _)) => B = A
    | Some (Cell_ (Output B) None) => B = A
    | _ => False
  end.

(** ** being internal *)

Definition is_internal {A : Type} (r : ref A) (mem : Memory) := 
    match mem (id_of_ref r) with
      | Some (Cell_ (Internal B) _) => True
      | _ => False
    end.

Lemma read_internal_defined : forall (A : Type) (r : ref A) (mem : Memory),
    is_compat r mem -> is_internal r mem -> read r mem <> None.
Proof.
  unfold is_compat, is_internal.
  intros A r mem H_compat H_internal.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c, t; try contradiction.
    subst.
    rewrite (read_internal_spec _ s); auto.
    intro H_c.
    inversion H_c.
  - contradiction.
Qed.

Lemma read_none_spec {A : Type} (r : ref A) (mem : Memory) :
  mem (id_of_ref r) = None -> read r mem = None.
Proof.
  unfold read; intro H_read.
  rewrite H_read.
  reflexivity.
Qed.

Lemma read_none_update_spec {A : Type} (r : ref A) (c : Cell) 
                            (r' : ref (type_of_cell c)) (mem : Memory) :
  (id_of_ref r) <> (id_of_ref r') ->
  read r mem = None -> 
  read r (((id_of_ref r') ↦ c ; mem)%pm) = None.
Proof.
  unfold read.
  intros H_neq H_read.
  rewrite p_update_neq; auto.
  destruct (mem (id_of_ref r)) eqn:H_get; auto.
  destruct c0,t; auto.
  - destruct (typ_dec T A); subst; simpl in *; auto.
    inversion H_read.
  - destruct s; auto.
    destruct (typ_dec T A); subst; simpl in *; auto.
    inversion H_read.
Qed.

Lemma read_read_internal (A : Type) (r : ref A) (a : A) (mem mem' : Memory) :
  is_compat r mem -> 
  is_internal r mem ->
  read r mem = Some (a, mem') -> mem = mem'.
Proof.
  unfold is_compat, is_internal.
  intros H_compat H_internal H_read.
  destruct (mem (id_of_ref r)) eqn:H_get; 
  try contradiction.
  destruct c, t; try contradiction.
  subst.
  rewrite (read_internal_spec _ s) in H_read; auto.
  inversion H_read; subst.
  reflexivity.
Qed.

Lemma write_internal_defined : forall (A : Type) (r : ref A) (v : A) (mem : Memory),
    is_compat r mem -> is_internal r mem -> write r v mem <> None.
Proof.
  unfold is_compat, is_internal, write.
  intros A r v mem H_compat H_internal.
  destruct (mem (id_of_ref r)) eqn:H_get;
  try contradiction.
  destruct c, t; try contradiction.
  subst.
  destruct (typ_dec A A).
  - intro c.
    inversion c.
  - exfalso.
    apply n.
    reflexivity.
Qed.

Lemma read_write_internal (A : Type) (r : ref A) (a : A) (mem mem' : Memory) :
  is_compat r mem -> 
  is_internal r mem ->
  read r mem = Some (a, mem') ->
  write r a mem' = Some mem.
Proof.
  unfold is_compat, is_internal.
  intros H_compat H_internal H_read.
  destruct (mem (id_of_ref r)) eqn:H_get; 
  try contradiction.
  destruct c, t; try contradiction.
  subst.
  rewrite (read_internal_spec _ s) in H_read; auto.
  inversion H_read; subst; clear H_read H_internal.
  rewrite (write_internal_spec _ _ a); auto.
  f_equal.
  extensionality k.
  destruct (Nat.eq_dec k (id_of_ref r)) as [| H_neq]; subst.
  - rewrite p_update_eq.
    symmetry.
    exact H_get.
  - rewrite p_update_neq; auto.
Qed.

Lemma write_read_internal (A : Type) (r : ref A) (a : A) (mem mem' : Memory) :
  is_compat r mem -> 
  is_internal r mem ->
  write r a mem = Some mem' -> 
  read r mem' = Some (a, mem').
Proof.
  unfold is_compat, is_internal.
  intros H_compat H_internal H_write.
  destruct (mem (id_of_ref r)) eqn:H_get;
  try contradiction.
  destruct c,t; try contradiction.
  subst.
  rewrite (write_internal_spec _ a s) in H_write; auto.
  inversion H_write; subst; clear H_write.
  rewrite (read_internal_spec _ a); auto.
  rewrite p_update_eq.
  reflexivity.
Qed. 

Lemma write_none_spec {A : Type} (r : ref A) (v : A) (mem : Memory) :
  mem (id_of_ref r) = None -> write r v mem = None.
Proof.
  unfold write; intro H_write.
  rewrite H_write.
  reflexivity.
Qed.


Lemma write_write_internal (A : Type) (r : ref A) (a a' : A) (mem mem' : Memory) :
  is_compat r mem ->
  is_internal r mem ->
  write r a mem = Some mem' ->
  write r a' mem = write r a' mem'.
Proof.
  unfold is_compat, is_internal.
  intros H_compat H_internal H_write.
  destruct (mem (id_of_ref r)) eqn:H_get; 
  try contradiction.
  destruct c, t; try contradiction.
  subst.
  rewrite (write_internal_spec _ a s) in H_write; auto.
  inversion H_write; subst; clear H_write.
  rewrite (write_internal_spec _ a' s); auto.
  rewrite (write_internal_spec _ a' a).
  - f_equal. 
    symmetry. 
    apply p_update_shadow.
  - now rewrite p_update_eq.
Qed. 