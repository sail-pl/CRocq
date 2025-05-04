From Stdlib Require Import PeanoNat.
From Stdlib Require Import FunctionalExtensionality.

Declare Scope total_map_scope.
Delimit Scope total_map_scope with tm.

Definition total_map {A : Type} := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map :=
  fun _ => v.

Definition t_update {A : Type} (m : total_map) (k : nat) (v : A) :=
  fun k' => if Nat.eq_dec k k' then v else m k'.

Notation "'_' '↦' v" := (t_empty v) 
(at level 100, right associativity) : total_map_scope.

Notation "x '↦' v ';' m" := (t_update m x v)
(at level 100, v at next level, right associativity) : total_map_scope.

Lemma t_update_eq {A : Type} (k : nat) (v : A) (m : total_map) :
  (k ↦ v ; m)%tm k = v.
Proof.
  unfold t_update.
  destruct (Nat.eq_dec k k); auto.
  contradiction.
Qed.

Lemma t_update_neq {A : Type} (k k' : nat) (v : A) (m : total_map) :
  k <> k' -> (k ↦ v ; m)%tm k' = m k'.
Proof.
  intro H_neq. 
  unfold t_update.
  destruct (Nat.eq_dec k k'); auto.
  contradiction.
Qed.

Lemma t_update_shadow {A : Type} (k : nat) (v v' : A) (m : total_map) :
  (k ↦ v ; k ↦ v' ; m)%tm = (k ↦ v ; m)%tm.
Proof.
  unfold t_update.
  apply functional_extensionality.
  intro k'.
  now destruct (Nat.eq_dec k k').
Qed.

Lemma t_update_id {A : Type} (k : nat) (m : @total_map A) :
  (k ↦ (m k); m)%tm = m.
Proof.
  unfold t_update.
  apply functional_extensionality.
  intro k'.
  now destruct (Nat.eq_dec k k'); subst.
Qed.

Declare Scope partial_map_scope.
Delimit Scope partial_map_scope with pm.

Definition partial_map {A : Type} := nat -> option A.

Definition p_empty {A : Type} (v : A) : partial_map := t_empty (@None A).

Definition p_update {A : Type} (m : partial_map) (k : nat) (v : A) :=
  (k ↦ Some v ; m)%tm.

Notation "∅" := (p_empty) 
(at level 100, right associativity) : partial_map_scope.

Notation "x '↦' v" := (p_update p_empty x v)
(at level 100, v at next level, right associativity) : partial_map_scope.

Notation "x '↦' v ';' m" := (p_update m x v)
(at level 100, v at next level, right associativity) : partial_map_scope.

Lemma p_update_eq {A : Type} (k : nat) (v : A) (m : partial_map) :
  (k ↦ v ; m)%pm k = Some v.
Proof.
  unfold p_update.
  apply t_update_eq.
Qed.

Lemma p_update_neq {A : Type} (k k' : nat) (v : A) (m : partial_map) :
  k <> k' -> (k ↦ v ; m)%pm k' = m k'.
Proof.
  intro H_neq. 
  unfold p_update.
  now apply t_update_neq.
Qed.

Lemma p_update_shadow {A : Type} (k : nat) (v v' : A) (m : partial_map) :
  (k ↦ v ; k ↦ v' ; m)%pm = (k ↦ v ; m)%pm.
Proof.
  unfold p_update.
  apply t_update_shadow.
Qed.

Lemma p_update_id {A : Type} (k : nat) (v : A) (m : @partial_map A) :
  m k = Some v -> (k ↦ v; m)%pm = m.
Proof.
  intro H_get.
  unfold p_update, t_update.
  apply functional_extensionality.
  intro k'.
  now destruct (Nat.eq_dec k k'); subst.
Qed.

Lemma p_update_permute {A : Type} (k k' : nat) (v v' : A) (m : @partial_map A) :
  k <> k' ->
  (k' ↦ v'; k ↦ v; m)%pm = (k ↦ v; k' ↦ v'; m)%pm.
Proof.
  intro H_neq.
  unfold p_update, t_update.
  apply functional_extensionality.
  intro k''.
  destruct (Nat.eq_dec k' k''); subst.
  - destruct (Nat.eq_dec k k''); subst; auto.
    contradiction.
  - reflexivity. 
Qed.