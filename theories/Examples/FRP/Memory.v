Require Import Categories.Category.Category.
Require Import Categories.Category.Functor.
Require Import Categories.Embedding.CategoryType.
Require Import Categories.Embedding.Monad.
Require Import Map Util.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq Require Import PeanoNat.
From Coq Require Import ProofIrrelevance.

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

(** ** being internal *)

Definition is_internal {A : Type} (r : ref A) (mem : Memory) := 
    match mem (id_of_ref r) with
      | Some (Cell_ (Internal B) _) => B = A
      | _ => False
    end.

Lemma read_internal_defined : forall (A : Type) (r : ref A) (mem : Memory),
    is_internal r mem -> read r mem <> None.
Proof.
  unfold is_internal, read.
  intros A r mem H_internal.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c, t.
    -- destruct (typ_dec T A); subst.
       + intro c.
         inversion c.
       + exfalso.
         apply n.
         reflexivity.
    -- contradiction.
    -- contradiction.
  - contradiction.
Qed.

Lemma read_none_spec {A : Type} (r : ref A) (mem : Memory) :
  mem (id_of_ref r) = None -> read r mem = None.
Proof.
  unfold read; intro H_read.
  rewrite H_read.
  reflexivity.
Qed.

Lemma read_read_internal (A : Type) (r : ref A) (a : A) (mem mem' : Memory) :
  is_internal r mem ->
  read r mem = Some (a, mem') -> mem = mem'.
Proof.
  intros H_internal H_read.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c, t.
    -- unfold is_internal in H_internal.
       rewrite H_get in *.
       subst.
       rewrite (read_internal_spec _ s) in H_read.
       + inversion H_read; subst.
         reflexivity.
       + simpl.
         exact H_get.
    -- unfold is_internal in H_internal.
       rewrite H_get in *.
       contradiction.
    -- unfold is_internal in H_internal.
       rewrite H_get in *.
       contradiction.
  - rewrite read_none_spec in H_read; auto.
    inversion H_read.
Qed.


Lemma write_internal_defined : forall (A : Type) (r : ref A) (v : A) (mem : Memory),
    is_internal r mem -> write r v mem <> None.
Proof.
  unfold is_internal, write.
  intros A r v mem H_internal.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c, t.
    -- destruct (typ_dec T A); subst.
       + intro c.
         inversion c.
       + exfalso.
         apply n.
         reflexivity.
    -- contradiction.
    -- contradiction.
  - contradiction.
Qed.

Lemma read_write_internal (A : Type) (r : ref A) (a : A) (mem mem' : Memory) :
  is_internal r mem ->
  read r mem = Some (a, mem') ->
  write r a mem' = Some mem.
Proof.
  intros H_internal H_read.
  unfold is_internal in *.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c, t; try contradiction.
    subst.
    rewrite (read_internal_spec _ s) in H_read; auto.
    inversion H_read; subst; clear H_read.
    unfold write.
    rewrite H_get.
    destruct (typ_dec A A); subst.
    -- f_equal.
       extensionality k.
       destruct (Nat.eq_dec k (id_of_ref r)) as [| H_neq]; subst.
       + rewrite p_update_eq.
         symmetry.
         exact H_get.
       + rewrite p_update_neq; auto.
    -- exfalso.
       apply n.
       reflexivity.
  - contradiction.
Qed.

Lemma write_read_internal (A : Type) (r : ref A) (a : A) (mem mem' : Memory) :
  is_internal r mem ->
  write r a mem = Some mem' -> 
  read r mem' = Some (a, mem').
Proof.
  intros H_internal H_write.
  unfold is_internal in *.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c,t; try contradiction.
    subst.
    rewrite (write_internal_spec _ a s) in H_write; auto.
    inversion H_write; subst; clear H_write.
    rewrite (read_internal_spec _ a); auto.
    rewrite p_update_eq.
    reflexivity.
  - contradiction.
Qed. 

Lemma write_none_spec {A : Type} (r : ref A) (v : A) (mem : Memory) :
  mem (id_of_ref r) = None -> write r v mem = None.
Proof.
  unfold write; intro H_write.
  rewrite H_write.
  reflexivity.
Qed.


Lemma write_write_internal (A : Type) (r : ref A) (a a' : A) (mem mem' : Memory) :
  is_internal r mem ->
  write r a mem = Some mem' ->
  write r a' mem = write r a' mem'.
Proof.
  intros H_internal H_write.
  destruct (mem (id_of_ref r)) eqn:H_get.
  - destruct c, t.
    -- unfold is_internal in H_internal.
       rewrite H_get in H_internal; subst.
       apply (write_internal_spec _ a) in H_get as H_eq.
       rewrite H_write in *.
       inversion H_eq; subst; clear H_eq.
       apply (write_internal_spec _ a') in H_get as H_eq.
       rewrite H_eq; clear H_eq.
       rewrite (write_internal_spec _ a' a).
       + f_equal. 
         symmetry. 
         apply p_update_shadow.
       + now rewrite p_update_eq.
    -- unfold is_internal in H_internal.
       rewrite H_get in H_internal.
       contradiction.
    -- unfold is_internal in H_internal.
       rewrite H_get in H_internal.
       contradiction.
  - apply (write_none_spec _ a) in H_get.
    rewrite H_get in *.
    inversion H_write. 
Qed. 



(** ** State Monad *)

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

Definition St (A : Type) : Type := Memory -> option (A * Memory).

Definition fmap_St {A B : Type} (f : Typ A B) : St A -> St B  := 
    fun st => fun m => 
        (fmap _ ∘ (fmap (FunctorProductLeft Memory))) f (st m).

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
  forall (A B : Typ) (f : A -> Functor_St B) (x : A), 
    bind_st (ret_st x) f = f x.
Proof.
  intros A B f x.
  unfold bind_st.
  extensionality m.
  now simpl.
Qed.

Lemma monad_prop2 : forall (A : Typ) (m : Functor_St A), bind_st m ret_st = m.
Proof.
  intros A m.
  extensionality s.
  unfold bind_st.
  destruct (m s) eqn:H_some.
  - destruct p as [a m'].
    unfold ret_st.
    reflexivity.
  - reflexivity.
Qed.

Lemma monad_prop3 : forall (A B C : Typ) (m : Functor_St A) (f : A -> Functor_St B)
    (g : B -> Functor_St C),
        bind_st (bind_st m f) g = bind_st m (fun x : A => bind_st (f x) g).
Proof.
  intros A B C m f g.
  unfold bind_st.
  extensionality s.
  destruct (m s) eqn:H_some.
  - destruct p as [a s'].
    reflexivity.
  - reflexivity.
Qed.

#[refine] Instance Monad_St : Monad := {
    ret := @ret_st;
    bind := @bind_st;
}.
Proof.
- exact monad_prop1.
- exact monad_prop2.
- exact monad_prop3.
Defined.

Definition mget {A : Type} (r : ref A) : St A := read r.

Definition mset {A : Type} (r : ref A) (v : A) : St unit :=
  fun (m : Memory) => fmap (FunctorOption) (fun (m : Memory) => (tt,m)) (write r v m).

Section st_eq.

  Variables (A : Type).
  Variables (r : ref A).
  Variables (x y : A).
  Variable (σ : Memory).

  Lemma eq_9a : 
    is_internal r σ ->
    (mget r >>= (fun _ => mget r)) σ = mget r σ.
  Proof.
    intro H_internal.
    unfold mget; simpl.
    unfold bind_st; simpl.
    destruct (read r σ) eqn:H_read.
    - destruct p as [a σ']. 
      apply (read_read_internal _ _ _ _ _ H_internal) in H_read as H_eq.
      subst.
      exact H_read.
    -   reflexivity.
  Qed.

  Lemma eq_9b : 
    is_internal r σ ->
    (mget r >>= (mset r)) σ = ret tt σ.
  Proof.
    intro H_internal.
    unfold mget, mset; simpl.
    unfold bind_st, ret_st; simpl.
    destruct (read r σ) eqn:H_read.
    - destruct p as [a σ'].
      apply (read_read_internal _ _ _ _ _ H_internal) in H_read as H_eq.
      subst.
      unfold fmap_option.
      apply (read_write_internal _ _ _ _ _ H_internal) in H_read.
      now rewrite H_read.
    - apply read_internal_defined in H_internal.
      contradiction.
  Qed.

  Lemma eq_9c : 
    is_internal r σ ->
    (mset r x >>= (fun tt => mget r)) σ = (mset r x >>= (fun tt => ret x)) σ.
  Proof.
    intro H_internal.
    unfold mset, mget; simpl.
    unfold bind_st, ret_st; simpl.
    destruct (write r x σ) as [σ'| ] eqn:H_write; simpl.
    - apply (write_read_internal _ _ _ _ _ H_internal) in H_write.
      exact H_write.
    - reflexivity.
  Qed.

  Lemma eq_9d : 
    is_internal r σ ->
    (mset r x >>= (fun tt => mset r y)) σ = (mset r y) σ.
  Proof.
    intro H_internal.
    unfold mset, mget; simpl.
    unfold bind_st, ret_st; simpl.
    destruct (write r x σ) as [σ'| ] eqn:H_write; simpl.
    - unfold fmap_option.
      destruct (write r y σ) as [σ''| ] eqn:H_write'; simpl.
      -- rewrite <- (write_write_internal _ _ x _ σ σ'); auto.
         rewrite H_write'.
         reflexivity.
      -- apply (write_internal_defined _ _ y) in H_internal.
         contradiction.
    - apply (write_internal_defined _ _ x) in H_internal.
      contradiction.
  Qed.

  Lemma eq_9e : 
    is_internal r σ ->
    (mget r >>= (fun _ => ret x)) σ = ret x σ.
  Proof.
    intro H_internal.
    unfold mget, ret_st; simpl.
    unfold bind_st; simpl.
    destruct (read r σ) as [[a σ'] | ] eqn:Heq.
    - apply (read_read_internal _ _ _ _ _ H_internal) in Heq.
      subst.
      reflexivity.
    - apply read_internal_defined in H_internal.
      contradiction.
  Qed.

End st_eq.

Section st_neq.

    Variables (A B : Type).
    Variables (r : ref A).
    Variables (r' : ref B).
    Variable  (H_neq : id_of_ref r <> id_of_ref r').
    Variables (x : A) (y : B).

    Lemma eq_9f : 
      mget r >>= (fun _ => mget r') = mget r' >>= (fun x => mget r >>= (fun _ => ret x)).
    Proof.
      unfold mget, ret_st; simpl.
      unfold bind_st; simpl.
      unfold read; simpl.
      extensionality σ.
      destruct (σ (id_of_ref r)) eqn:H_get.
      - destruct c, t.
        -- destruct (typ_dec T A).
           + destruct (σ (id_of_ref r')) eqn:H_get'; auto.
             destruct c, t; auto.
             ++ destruct (typ_dec T0 B); auto.
                subst.
                rewrite H_get.
                destruct (typ_dec A A).
                * unfold ret_st.
                  reflexivity.
                * exfalso.
                  apply n.
                  reflexivity.
             ++ destruct s0; auto.
                destruct (typ_dec T0 B); auto.
                subst; simpl.
                rewrite p_update_neq; auto.
                rewrite H_get.
                destruct (typ_dec A A).
                * unfold ret_st.
                  reflexivity.
                * exfalso.
                  apply n.
                  reflexivity.
             + destruct (σ (id_of_ref r')) eqn:H_get'; auto.
               destruct c, t; auto.
               ++ destruct (typ_dec T0 B); auto.
                  subst.
                  rewrite H_get.
                  destruct (typ_dec T A).
                  * contradiction.
                  * reflexivity.
               ++ destruct s0; auto.
                  destruct (typ_dec T0 B); auto.
                  subst.
                  simpl.
                  rewrite p_update_neq; auto.
                  rewrite H_get.
                  destruct (typ_dec T A).
                  * contradiction.
                  * reflexivity.
        -- destruct s.
           + destruct (typ_dec T A).
             ++ subst.
                rewrite p_update_neq; auto.
                destruct (σ (id_of_ref r')) eqn:H_get'; auto.
                destruct c, t0; auto.
                * destruct (typ_dec T B); auto.
                  rewrite H_get.
                  destruct (typ_dec A A).
                  ** unfold ret_st.
                     reflexivity.
                  ** exfalso.
                     apply n.
                     reflexivity.
                * destruct s; auto.
                  destruct (typ_dec T B); auto.
                  subst; simpl.
                  rewrite p_update_neq; auto.
                  rewrite H_get.
                  destruct (typ_dec A A).
                  ** unfold ret_st.
                     do 2 f_equal.
                     now apply p_update_permute.
                  ** exfalso.
                     apply n.
                     reflexivity.
             ++  destruct (σ (id_of_ref r')) eqn:H_get'; auto.
                 destruct c, t0; auto.
                 * destruct (typ_dec T0 B); auto.
                   subst.
                   rewrite H_get.
                   destruct (typ_dec T A); auto.
                   contradiction.
                 * destruct s; auto.
                   destruct (typ_dec T0 B); auto.
                   rewrite p_update_neq; auto.
                   rewrite H_get.
                   destruct (typ_dec T A); auto.
                   contradiction.
          + destruct (σ (id_of_ref r')) eqn:H_get'; auto.
            destruct c, t; auto.
            ++ destruct (typ_dec T0 B); auto.
               rewrite H_get.
               reflexivity.
            ++ destruct s; auto.
               destruct (typ_dec T0 B); auto.
               rewrite p_update_neq; auto.
               rewrite H_get.
               reflexivity.
        -- destruct (σ (id_of_ref r')) eqn:H_get'; auto.
           destruct c, t; auto.
           + destruct (typ_dec T0 B); auto.
             subst.
             rewrite H_get.
             reflexivity.
           + destruct s0; auto.
             destruct (typ_dec T0 B); auto.
             rewrite p_update_neq; auto.
             rewrite H_get.
             reflexivity.
      - destruct (σ (id_of_ref r')) eqn:H_get'; auto.
        destruct c, t; auto.
        -- destruct (typ_dec T B); auto.
           subst.
           rewrite H_get.
           reflexivity.
        -- destruct s; auto.
           destruct (typ_dec T B); auto.
           rewrite p_update_neq; auto.
           rewrite H_get.
           reflexivity.
    Qed.

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