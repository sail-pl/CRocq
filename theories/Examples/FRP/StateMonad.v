Require Import Categories.Category.Category.
Require Import Categories.Category.Functor.
Require Import Categories.Embedding.CategoryType.
Require Import Categories.Embedding.Monad.
Require Import Util Map Memory.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq Require Import PeanoNat.
From Coq Require Import ProofIrrelevance.

(** * State Monad *)

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
  Hypothesis H_compat : is_compat r σ.
  Hypothesis H_internal : is_internal r σ.

  Lemma eq_8a : 
    (mget r >>= (fun _ => mget r)) σ = mget r σ.
  Proof.
    unfold mget; simpl.
    unfold bind_st; simpl.
    destruct (read r σ) eqn:H_read.
    - destruct p as [a σ']. 
      apply (read_read_internal _ _ _ _ _ H_compat H_internal) in H_read as H_eq.
      subst.
      exact H_read.
    -   reflexivity.
  Qed.

  Lemma eq_8b : 
    (mget r >>= (mset r)) σ = ret tt σ.
  Proof.
    unfold mget, mset; simpl.
    unfold bind_st, ret_st; simpl.
    destruct (read r σ) eqn:H_read.
    - destruct p as [a σ'].
      apply (read_read_internal _ _ _ _ _ H_compat H_internal) in H_read as H_eq.
      subst.
      unfold fmap_option.
      apply (read_write_internal _ _ _ _ _ H_compat H_internal) in H_read.
      now rewrite H_read.
    - apply read_internal_defined in H_internal; auto.
      contradiction.
  Qed.

  Lemma eq_8c : 
    (mset r x >>= (fun tt => mget r)) σ = (mset r x >>= (fun tt => ret x)) σ.
  Proof.
    unfold mset, mget; simpl.
    unfold bind_st, ret_st; simpl.
    destruct (write r x σ) as [σ'| ] eqn:H_write; simpl.
    - apply (write_read_internal _ _ _ _ _ H_compat H_internal) in H_write.
      exact H_write.
    - reflexivity.
  Qed.

  Lemma eq_8d : 
    (mset r x >>= (fun tt => mset r y)) σ = (mset r y) σ.
  Proof.
    unfold mset, mget; simpl.
    unfold bind_st, ret_st; simpl.
    destruct (write r x σ) as [σ'| ] eqn:H_write; simpl.
    - unfold fmap_option.
      destruct (write r y σ) as [σ''| ] eqn:H_write'; simpl.
      -- rewrite <- (write_write_internal _ _ x _ σ σ'); auto.
         rewrite H_write'.
         reflexivity.
      -- apply (write_internal_defined _ _ y) in H_internal; auto.
         contradiction.
    - apply (write_internal_defined _ _ x) in H_internal; auto.
      contradiction.
  Qed.

  Lemma eq_8e : 
    (mget r >>= (fun _ => ret x)) σ = ret x σ.
  Proof.
    unfold mget, ret_st; simpl.
    unfold bind_st; simpl.
    destruct (read r σ) as [[a σ'] | ] eqn:Heq.
    - apply (read_read_internal _ _ _ _ _ H_compat H_internal) in Heq.
      subst.
      reflexivity.
    - apply read_internal_defined in H_internal; auto.
      contradiction.
  Qed.

End st_eq.

Section st_neq.

    Variables (A B : Type).
    Variables (r : ref A).
    Variables (r' : ref B).
    Variable  (H_neq : id_of_ref r <> id_of_ref r').
    Variables (x : A) (y : B).

    Lemma eq_8f : 
      mget r >>= (fun _ => mget r') = mget r' >>= (fun x => mget r >>= (fun _ => ret x)).
    Proof.
      unfold mget, ret_st; simpl.
      unfold bind_st; simpl.
      extensionality σ.
      destruct (read r σ) eqn:H_read;
      destruct (read r' σ) eqn:H_read'; auto.
      - destruct p as [v σ'];
        destruct p0 as [v' σ''].
        apply read_mem_spec in H_read as H_eq.
        apply read_mem_spec in H_read' as H_eq'.
        destruct H_eq as [H_eq | H_eq]; subst;
        destruct H_eq' as [H_eq' | H_eq']; subst.
        -- rewrite H_read, H_read'.
           now unfold ret_st.
        -- rewrite H_read'.
           apply (read_update_neq _ _ (Cell_ (Input B) None) r' σ) in H_read; auto.
           simpl in *.
           rewrite H_read.
           reflexivity.
        -- rewrite H_read.
           apply (read_update_neq _ _ (Cell_ (Input A) None) r σ) in H_read'; auto.
        -- apply (read_update_neq _ _ (Cell_ (Input B) None) r' σ) in H_read; auto.
           apply (read_update_neq _ _ (Cell_ (Input A) None) r σ) in H_read'; auto.
           simpl in *.
           rewrite H_read, H_read'.
           unfold ret_st.
           do 2 f_equal.
           apply p_update_permute; auto.
      - destruct p as [v σ'].
        apply read_mem_spec in H_read as H_eq.
        destruct H_eq as [H_eq | H_eq]; subst; auto.
        unfold read.
        unfold read in H_read'.
        rewrite p_update_neq; auto.
        destruct (σ (id_of_ref r')) eqn:H_get; auto.
        destruct c, t; auto.
        -- destruct (typ_dec T B); subst; simpl in *; auto.
           inversion H_read'.
        -- destruct (typ_dec T B); subst; simpl in *; auto.
           destruct s; auto.
           inversion H_read'.
      - destruct p as [v σ'].
        apply read_mem_spec in H_read' as H_eq.
        destruct H_eq as [H_eq | H_eq]; subst.
        -- unfold read.
           unfold read in H_read.
           destruct (σ (id_of_ref r)) eqn:H_get; auto.
           destruct c, t; auto.
           + destruct (typ_dec T A); subst; simpl in *; auto.
             inversion H_read.
           + destruct (typ_dec T A); subst; simpl in *; auto.
             ++ destruct s; auto.
                inversion H_read.
             ++ destruct s; auto.
        -- unfold read.
           unfold read in H_read.
           rewrite p_update_neq; auto.
           destruct (σ (id_of_ref r)) eqn:H_get; auto.
           destruct c, t; auto.
           + destruct (typ_dec T A); subst; simpl in *; auto.
             inversion H_read.
           + destruct (typ_dec T A); subst; simpl in *; auto.
             ++ destruct s; auto.
               inversion H_read.
             ++ destruct s; auto.
    Qed.
      
    Lemma eq_8h : 
        mget r >>= (fun _ => mset r' y) = 
            mset r' y >>= (fun tt => mget r >>= (fun _ => ret tt)).
    Proof.
      unfold bind; simpl.
      unfold bind, bind_st, mget, mset; simpl.
      extensionality σ.
      destruct (read r σ) eqn:H_read;
      destruct (write r' y σ) eqn:H_write; auto.
      - destruct p as [v σ'].
        apply read_mem_spec in H_read as H_eq.
        destruct H_eq; subst; simpl.
        -- rewrite H_write; simpl.
           apply write_mem_spec in H_write as H_eq.
           destruct H_eq; subst.
           + apply (read_update_neq _ _ (Cell_ (Internal B) y) r') in H_read; auto.
             simpl in *.
             rewrite H_read.
             reflexivity.
           + apply (read_update_neq _ _ (Cell_ (Output B) (Some y)) r') in H_read; auto.
             simpl in *.
             rewrite H_read.
             reflexivity.
        -- admit.
      - destruct p as [v σ'].
         admit.
      - simpl.
        apply write_mem_spec in H_write as H_eq.
        destruct H_eq; subst.
        -- apply (read_none_update_spec _ (Cell_ (Internal B) y) r') in H_read; auto.
           simpl in *.
           rewrite H_read.
           reflexivity.
        -- apply (read_none_update_spec _ (Cell_ (Output B) (Some y)) r') in H_read; auto.
           simpl in *.
           rewrite H_read.
           reflexivity.
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

Lemma monad_get_ignore : 
    forall (A : Type) (r : ref A) (x : A),
    mget r >>= (fun _ => ret x) = ret x.
Proof. Admitted.

Definition rsf (A B : Type) := A -> St B.

Definition arr {A B : Type} (f : A -> B) := fun x => ret (f x).

Definition compose {A B C : Type} (f : rsf B C) (g : rsf A B) : rsf A C :=
    fun x => g x >>= f.

Notation  "t1 '>>>' t2" := (compose t2 t1) (at level 42, left associativity).

Definition first {A B C : Type} (f : rsf A B) : rsf (A * C) (B * C) :=
    fun '(x, z) => 
        f x >>= (fun y => ret (y, z)).

Definition rsfget {A B : Type} (r : ref B) : rsf A (A * B) :=
    fun x => mget r >>= (fun y => ret (x, y)).

Definition rsfset {A B : Type} (r : ref B) : rsf (A * B) A :=
    fun '(x, y) => mset r y >>= (fun tt => ret x).

Definition perm {A B C : Type} := 
  fun (xyz : (A * B) * C) =>  let '((x,y),z) := xyz in ((x,z),y).

Goal forall {A B C D : Type} (rsf : rsf A D), 
  (arr (@perm A B C)) >>> (first (first rsf)) >>> (arr perm) = first (first rsf).
Proof.
  intros A B C D rsf.
  unfold arr,first,compose.
  extensionality x.
  destruct x as [[x y] z].
  simpl.
  extensionality mem.
  unfold bind_st, ret_st.
  destruct (rsf x mem) eqn:H_eval.
  destruct p as [w mem']; auto.
  reflexivity.
Qed.
