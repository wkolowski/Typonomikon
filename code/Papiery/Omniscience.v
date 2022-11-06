(** This file is based on the paper "Infinite sets that satisfy the principle
    of omniscience in any variety of constructive mathematics" by
    Martin Escardó. *)

Definition omniscient (X : Type) : Prop :=
  forall p : X -> bool,
    (exists x : X, p x = false) \/ forall x : X, p x = true.

(*
Inductive leb_bool : bool -> bool -> Prop :=
| leb_bool_refl : forall b : bool, leb_bool b b
| leb_bool_ft : leb_bool false true.
*)

Definition leb_bool (x y : bool) : Prop :=
  x = false \/ y = true.

Definition selection_function {X : Type} (e : (X -> bool) -> X) : Prop :=
  forall p : X -> bool, p (e p) = true -> forall x : X, p x = true.

Definition searchable (X : Type) : Prop :=
  exists e : (X -> bool) -> X, selection_function e.

(** Lemma 2.2 *)
Lemma searchable_omniscient :
  forall X : Type,
    searchable X -> omniscient X.
Proof.
  unfold searchable, selection_function, omniscient.
  intros X [e H] p.
  specialize (H p). case_eq (p (e p)); intros.
    right. apply H. assumption.
    left. exists (e p). assumption.
Qed.

(** Lemma 2.3 *)
Lemma lemma_2_3 :
  forall (X : Type) (e : (X -> bool) -> X) (p : X -> bool),
    selection_function e ->
      (exists x : X, p x = false) <-> p (e p) = false.
Proof.
  unfold selection_function.
  intros X e p H.
  split.
    intros [x H']. case_eq (p (e p)); intros.
      specialize (H _ H0 x). congruence.
      reflexivity.
    intro. exists (e p). assumption.
Qed.

Require Import Setoid.

(** Proposition 2.4 *)
Proposition prop_2_4 :
  forall (X Y : Type) (a : X -> Y -> bool),
    searchable Y ->
      (forall x : X, exists y : Y, a x y = false) ->
        exists f : X -> Y, forall x : X, a x (f x) = false.
Proof.
  unfold searchable, selection_function.
  intros X Y a [e He] H.
  exists (fun x : X => e (a x)). intro.
  rewrite <- (lemma_2_3 _ _ _ He). apply H.
Qed.

Fixpoint r (a : nat -> bool) (n : nat) : bool :=
match n with
| 0 => a 0
| S n' => andb (r a n') (a n)
end.

(** Conatural numbers using decreasing boolean sequences. *)

Require Import Nat.
Require Import Arith.

Definition seq_eq (a b : nat -> bool) : Prop :=
  forall i : nat, a i = b i.

Definition seq_neq (a b : nat -> bool) : Prop :=
  exists i : nat, a i <> b i.

Notation "a == b" := (seq_eq a b) (at level 50).
Notation "a # b" := (seq_neq a b) (at level 50).

Definition is_decr (a : nat -> bool) : Prop :=
  forall n : nat, leb_bool (a (S n)) (a n).

Record conat : Type :=
{
  seq :> nat -> bool;
  is_decr_seq : is_decr seq;
}.

Definition finite (n : nat) : conat.
Proof.
  exists (fun k : nat => if k <=? S n then true else false).
  do 2 red. cbn. intro.
  destruct (Nat.leb_spec0 n0 n).
    right. destruct (Nat.leb_spec0 n0 (S n)).
      reflexivity.
      contradict l. intro. apply n1. apply le_S. assumption.
    left. reflexivity.
Defined.

Definition omega : conat.
Proof.
  esplit with (fun n : nat => true).
  do 2 red. right. reflexivity.
Defined.

(** Proposition 3.1 *)

Require Import FunctionalExtensionality.

Lemma r_idempotent :
  forall a : nat -> bool,
    r (r a) = r a.
Proof.
  intro a. extensionality n.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. destruct (r a n'); cbn; reflexivity.
Qed.

Lemma r_is_decr :
  forall a : nat -> bool,
    is_decr (r a).
Proof.
  unfold is_decr, leb_bool.
  induction n as [| n']; cbn.
    destruct (a 0), (a 1); cbn; auto.
    destruct IHn'; cbn in *.
      rewrite H. cbn. auto.
      rewrite H. cbn. destruct (a (S n')); cbn; auto.
Qed.

Definition r_conat (a : nat -> bool) : conat :=
{|
  seq := r a;
  is_decr_seq := r_is_decr a;
|}.

Definition LPO : Prop :=
  forall a : nat -> bool,
    (exists n : nat, a n = false) \/
    (forall n : nat, a n = true).

Definition WLPO : Prop :=
  forall a : nat -> bool,
    (forall n : nat, a n = true) \/
    ~ (forall n : nat, a n = true).

Definition MP : Prop :=
  forall a : nat -> bool,
    ~ (forall n : nat, a n = true) -> exists n : nat, a n = false.

Lemma LPO_is_WLPO_and_MP :
  LPO <-> WLPO /\ MP.
Proof.
  unfold LPO, WLPO, MP. split.
    intro LPO. split.
      intro a. destruct (LPO a) as [[n H] | H].
        right. intro. specialize (H0 n). congruence.
        left. assumption.
      intros a H. destruct (LPO a) as [[n H'] | H'].
        exists n. assumption.
        contradiction.
    intros [WLPO MP] a. destruct (WLPO a).
      right. assumption.
      left. apply MP. assumption.
Qed.

Lemma LPO_equiv :
  LPO <-> forall a : conat, a # seq omega \/ a == omega.
Proof.
  unfold LPO.
  split.
    intros LPO a. destruct (LPO a) as [[n H] | H].
      left. red. cbn. exists n. intro. congruence.
      right. red. cbn. apply H.
    intros H a. destruct (H (r_conat a)).
      left. destruct H0 as [i H0]. cbn in H0.
        induction i as [| i']; cbn in H0.
          exists 0. destruct (a 0); congruence.
          case_eq (r a i'); intro.
            exists (S i'). case_eq (a (S i')); intro.
              rewrite H1 in H0. rewrite H2 in H0. cbn in H0. congruence.
              reflexivity.
            apply IHi'. intro. congruence.
      right. red in H0. cbn in H0.
        induction n as [| n'].
          specialize (H0 0). cbn in H0. assumption.
          specialize (H0 (S n')). cbn in H0. destruct (a (S n')).
            reflexivity.
            rewrite Bool.andb_false_r in H0. congruence.
Qed.

Lemma WLPO_equiv :
  WLPO <-> forall a : conat, a <> omega \/ a == omega.
Proof.
  unfold WLPO.
  split.
    intros WLPO a. destruct (WLPO a).
      right. red. cbn. assumption.
      left. intro. apply H. intro. rewrite H0. cbn. reflexivity.
    intros H a. destruct (H (r_conat a)).
      right. intro. red in H0. apply H0. admit.
      left. intro. red in H0. cbn in H0. admit.
Admitted.

Lemma MP_equiv :
  MP <-> forall a : conat, a <> omega -> a # omega.
Proof.
  unfold MP.
  split.
    intros MP a H. red. cbn. destruct (MP a) as [n Hn].
      intro. apply H. admit.
      exists n. intro. congruence.
    intros H a H'. red in H. cbn in H. destruct (H (r_conat a)).
      intro. apply H'. intro. apply (f_equal seq) in H0. cbn in H0.
Admitted.