Require Import Recdef.

Inductive Z : Type :=
| Zero : Z
| MinusOne : Z
| Next : Z -> Z.

Function abs (k : Z) : Z :=
match k with
| Zero => Zero
| MinusOne => Next Zero
| Next k' => Next (abs k')
end.

Function succ (k : Z) : Z :=
match k with
| Zero => Next Zero
| MinusOne => Zero
| Next Zero => Next (Next Zero)
| Next MinusOne => MinusOne
| Next k' => Next (succ k')
end.

Function pred (k : Z) : Z :=
match k with
| Zero => MinusOne
| MinusOne => Next MinusOne
| Next Zero => Zero
| Next MinusOne => Next (Next MinusOne)
| Next k' => Next (pred k')
end.

Function neg' (k : Z) : Z :=
match k with
| Zero => MinusOne
| MinusOne => Zero
| Next k' => Next (neg' k')
end.

Definition neg (k : Z) : Z :=
  succ (neg' k).

Function isNegative (k : Z) : bool :=
match k with
| Zero     => false
| MinusOne => true
| Next k'  => isNegative k'
end.

Definition isZero (k : Z) : bool :=
match k with
| Zero => true
| _    => false
end.

Function add (k1 k2 : Z) : Z :=
match k1 with
| Zero => k2
| MinusOne => pred k2
| Next k1' => if isNegative k1' then pred (add k1' k2) else succ (add k1' k2)
end.

Lemma abs_abs :
  forall k : Z, abs (abs k) = abs k.
Proof.
  intros k; functional induction (abs k)
  ; cbn; rewrite ?IHz; reflexivity.
Qed.

Lemma succ_pred :
  forall k : Z,
    succ (pred k) = k.
Proof.
  intros k; functional induction (pred k); cbn.
  1-4: reflexivity.
  rewrite IHz; clear IHz.
  functional induction (pred k'); cbn in *.
  1-2: contradiction.
  1-3: reflexivity.
Qed.

Lemma pred_succ :
  forall k : Z,
    pred (succ k) = k.
Proof.
  intros k; functional induction (succ k); cbn.
  1-4: reflexivity.
  rewrite IHz; clear IHz.
  functional induction (succ k'); cbn in *.
  1-2: contradiction.
  1-3: reflexivity.
Qed.

Lemma neg'_succ :
  forall k : Z, neg' (succ k) = pred (neg' k).
Proof.
  intros k; functional induction (succ k); cbn.
  1-4: reflexivity.
  rewrite IHz; clear IHz.
  functional induction (neg' k'); cbn.
  1-2: contradiction.
  reflexivity.
Qed.

Lemma pred_neg' :
  forall k : Z, pred (neg' k) = neg' (succ k).
Proof.
  intros k; rewrite neg'_succ; reflexivity.
Qed.

Lemma neg_succ :
  forall k : Z, neg (succ k) = pred (neg k).
Proof.
  intros k; unfold neg.
  rewrite neg'_succ, succ_pred, pred_succ.
  reflexivity.
Qed.

Lemma pred_neg :
  forall k : Z, pred (neg k) = neg (succ k).
Proof.
  intros k; rewrite neg_succ; reflexivity.
Qed.

Lemma neg'_pred :
  forall k : Z, neg' (pred k) = succ (neg' k).
Proof.
  intros k; functional induction (pred k); cbn.
  1-4: reflexivity.
  rewrite IHz; clear IHz.
  functional induction (neg' k'); cbn.
  1-2: contradiction.
  reflexivity.
Qed.

Lemma succ_neg' :
  forall k : Z, succ (neg' k) = neg' (pred k).
Proof.
  intros k; rewrite neg'_pred; reflexivity.
Qed.

Lemma neg_pred :
  forall k : Z, neg (pred k) = succ (neg k).
Proof.
  intros k; unfold neg.
  rewrite neg'_pred.
  reflexivity.
Qed.

Lemma neg'_neg' :
  forall k : Z, neg' (neg' k) = k.
Proof.
  intros k; functional induction (neg' k)
  ; cbn; rewrite ?IHz; reflexivity.
Qed.

Lemma neg_neg :
  forall k : Z, neg (neg k) = k.
Proof.
  intros k; unfold neg.
  rewrite neg'_succ, succ_pred, neg'_neg'.
  reflexivity.
Qed.

(*
neg'
abs
succ
pred
neg
*)

Lemma abs_neg :
  forall k : Z,
    abs (neg k) = abs k.
Proof.
  unfold neg; intros k.
  functional induction (neg' k); cbn.
  1-2: reflexivity.
  destruct (neg' k'); cbn in *; rewrite IHz; reflexivity.
Qed.

Lemma isNegative_abs :
  forall k : Z,
    isNegative (abs k) = false.
Proof.
  intros k; functional induction (abs k)
  ; cbn; rewrite ?IHz; reflexivity.
Qed.

Lemma isNegative_neg' :
  forall k : Z,
    isNegative (neg' k) = negb (isNegative k).
Proof.
  intros k; functional induction (neg' k); cbn; auto.
Qed.

Lemma isNegative_pred :
  forall k : Z,
    isNegative (pred k) = orb (isNegative k) (isZero k).
Proof.
  intros k; functional induction (pred k); cbn.
  1-4: reflexivity.
  destruct k'; cbn in *; try contradiction.
  assumption.
Qed.

Lemma isNegative_succ :
  forall k : Z,
    isNegative (succ k) =
    match k with
    | MinusOne => false
    | _ => isNegative k
    end.
Proof.
  intros k; functional induction (pred k); cbn.
  1-4: reflexivity.
  destruct k'; cbn in *; try contradiction.
  assumption.
Qed.

Lemma abs_spec :
  forall k : Z,
    abs k = if isNegative k then neg k else k.
Proof.
  intros k; functional induction (isNegative k); cbn.
  1-2: reflexivity.
  rewrite IHb.
  destruct (isNegative k') eqn: Heq; [| reflexivity].
  unfold neg; destruct (neg' k') eqn: Hneg.
  all: try reflexivity.
  functional inversion Hneg; subst.
  inversion Heq.
Qed.

(* Function min (k1 k2 : Z) : Z :=
match k1, k2 with
| Next k1', Next k2' => Next (min k1' k2')
| MinusOne, Zero => MinusOne
| Zero    , MinusOne => MinusOne *)

Lemma Next_spec :
  forall k : Z,
    Next k = if isNegative k then pred k else succ k.
Proof.
  intros k; functional induction (isNegative k); cbn.
  1-2: reflexivity.
  rewrite IHb.
  destruct (isNegative k') eqn: Hneg.
  - functional inversion Hneg; cbn in *; reflexivity.
  - functional inversion Hneg; cbn in *; reflexivity.
Qed.

Lemma add_Zero_r :
  forall k : Z,
    add k Zero = k.
Proof.
  induction k as [| | k']; cbn.
  1-2: reflexivity.
  rewrite IHk', Next_spec.
  reflexivity.
Qed.

Lemma add_MinusOne_r :
  forall k : Z,
    add k MinusOne = pred k.
Proof.
  intros k; functional induction (pred k); cbn.
  1-4: reflexivity.
  destruct k'; cbn in *; try contradiction.
  destruct (isNegative k') eqn: Hneg.
  - functional inversion Hneg; subst.
    + cbn. reflexivity.
    + admit.
Admitted.

Lemma add_Next_r :
  forall k1 k2 : Z,
    add k1 (Next k2) = if isNegative k2 then pred (add k1 k2) else succ (add k1 k2).
Proof.
Admitted.

Lemma add_comm :
  forall k1 k2 : Z,
    add k1 k2 = add k2 k1.
Proof.
  intros k1 k2; functional induction (add k1 k2); cbn.
  - rewrite add_Zero_r; reflexivity.
  - rewrite add_MinusOne_r; reflexivity.
  - rewrite add_Next_r, e0, IHz; reflexivity.
  - rewrite add_Next_r, e0, IHz; reflexivity.
Qed.

Lemma add_pred_l :
  forall k1 k2 : Z,
    add (pred k1) k2 = pred (add k1 k2).
Proof.
  intros k1 k2; functional induction (pred k1); cbn.
  1-2, 4: reflexivity.
  - rewrite pred_succ; reflexivity.
  - rewrite isNegative_pred.
    destruct k'; try contradiction; cbn [isZero]; rewrite Bool.orb_false_r.
    rewrite IHz, succ_pred.
    destruct (isNegative (Next k')).
    + reflexivity.
    + rewrite pred_succ. reflexivity.
Qed.

Lemma add_pred_r :
  forall k1 k2 : Z,
    add k1 (pred k2) = pred (add k1 k2).
Proof.
  intros k1 k2.
  rewrite add_comm, add_pred_l, add_comm.
  reflexivity.
Qed.

Lemma add_succ_l :
  forall k1 k2 : Z,
    add (succ k1) k2 = succ (add k1 k2).
Proof.
  intros k1 k2.
  assert (H : add (pred (succ k1)) k2 = pred (succ (add k1 k2)))
      by (rewrite !pred_succ; reflexivity).
  apply (f_equal succ) in H.
  rewrite add_pred_l, !succ_pred in H.
  assumption.
Qed.

Lemma add_succ_r :
  forall k1 k2 : Z,
    add k1 (succ k2) = succ (add k1 k2).
Proof.
  intros k1 k2.
  rewrite add_comm, add_succ_l, add_comm.
  reflexivity.
Qed.

Lemma add_assoc :
  forall k1 k2 k3 : Z,
    add (add k1 k2) k3 = add k1 (add k2 k3).
Proof.
  intros k1 k2 k3.
  functional induction (add k1 k2); cbn.
  - reflexivity.
  - rewrite add_pred_l; reflexivity.
  - rewrite add_pred_l, e0, IHz; reflexivity.
  - rewrite add_succ_l, e0, IHz; reflexivity.
Qed.

Lemma neg'_add :
  forall k1 k2 : Z,
    neg' (add k1 k2) = succ (add (neg' k1) (neg' k2)).
Proof.
  intros k1 k2.
  functional induction (add k1 k2); cbn.
  - rewrite succ_pred. reflexivity.
  - rewrite neg'_pred. reflexivity.
  - rewrite neg'_pred, IHz, isNegative_neg', e0; cbn. reflexivity.
  - rewrite neg'_succ, IHz, isNegative_neg', e0; cbn.
    rewrite pred_succ, succ_pred. reflexivity.
Qed.

Lemma neg_add :
  forall k1 k2 : Z,
    neg (add k1 k2) = add (neg k1) (neg k2).
Proof.
  intros k1 k2. unfold neg.
  rewrite add_succ_l, add_succ_r, neg'_add.
  reflexivity.
Qed.