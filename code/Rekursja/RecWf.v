Require Import Arith.
Require Import Omega.

Definition div  : nat -> forall k : nat, 0 < k -> nat.
Proof.
  apply (@well_founded_induction_type nat lt lt_wf
    (fun n : nat => forall k : nat, 0 < k -> nat)).
  intros. destruct (le_lt_dec k x).
    Focus 2. exact 0.
    apply S. apply (H (x - k)) with k.
      apply Nat.sub_lt; assumption.
      assumption.
Defined.

Print div.

Compute div 5 2 ltac:(omega).

Lemma div_lt_n_k :
  forall (n k : nat) (H : 0 < k),
    n < k -> div n k H = 0.
Proof.
  intros. cbn. destruct (le_lt_dec k n).
    omega.
    trivial.
Qed.

Lemma div_le_k_n :
  forall (n k : nat) (H : 0 < k),
    k <= n -> div n k H = S (div (n - k) k H).
Proof.
  apply (@well_founded_ind nat lt lt_wf
    (fun n => forall (k : nat) (H : 0 < k),
      k <= n -> div n k H = S (div (n - k) k H))).
  intros. remember (S (div (x - k) k H0)) as w.
    unfold div. cbn. destruct (le_lt_dec k x).
      subst. rewrite <- H.
Admitted.

Theorem div_equation' :
  forall (n k : nat) (H : 0 < k), div n k H =
    match le_lt_dec k n with
        | left _ => S (div (n - k) k H)
        | right _ => 0
    end.
Proof.
  intros. destruct (le_lt_dec k n).
    rewrite div_le_k_n; auto.
    rewrite div_lt_n_k; auto.
Qed.

Inductive divR' : nat -> nat -> nat -> Prop :=
    | div_base :
        forall (n k : nat), 0 < k -> n < k -> divR' n k 0
    | div_rec :
        forall (n k r : nat), 0 < k -> k <= n ->
          divR' (n - k) k r -> divR' n k (S r).

Hint Constructors divR'.

Lemma divR'_correct :
  forall (n k r : nat) (H : 0 < k),
    div n k H = r -> divR' n k r.
Proof.
  apply (@well_founded_induction nat lt lt_wf
    (fun n : nat => forall (k r : nat) (H : 0 < k ),
      div n k H = r -> divR' n k r)).
  intros. rewrite div_equation' in H1. destruct (le_lt_dec k x); subst.
    Focus 2. constructor; auto.
    constructor; auto. apply H with H0; omega.
Qed.

Lemma divR'_complete :
  forall (n k r : nat) (H : 0 < k),
    divR' n k r -> div n k H = r.
Proof.
  induction 1.
    apply div_lt_n_k. assumption.
    rewrite <- IHdivR' with H. rewrite div_le_k_n; auto.
Qed.

Theorem div_ind :
  forall P : nat -> nat -> nat -> Prop,
    (forall n k : nat, 0 < k -> n < k -> P n k 0) ->
    (forall (n k : nat) (H : 0 < k), k <= n ->
      P (n - k) k (div (n - k) k H) -> P n k (S (div (n - k) k H))) ->
        forall (n k : nat) (H : 0 < k), P n k (div n k H).
Proof.
  intros. apply divR'_ind; intros.
    apply H; auto.
    eapply (divR'_complete _ _ _ H2) in H4. subst. apply H0; assumption.
    apply divR'_correct with H1. reflexivity.
Qed.