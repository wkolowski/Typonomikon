Require Import B W3.

(** Xor w logice intuicjonistycznej - ubaw po pachy. *)

Definition xor (A B : Prop) : Prop :=
  (A /\ ~ B) \/ (~ A /\ B).

Ltac xor := unfold xor.

Lemma xor_irrefl :
  forall P : Prop, ~ xor P P.
Proof.
  xor. intros A H.
  destruct H as [[p np] | [np p]].
    apply np. assumption.
    apply np. assumption.
Qed.

Lemma xor_sym :
  forall P Q : Prop, xor P Q -> xor Q P.
Proof.
  xor. intros P Q H.
  destruct H as [[p nq] | [q np]].
    right. split; assumption.
    left. split; assumption.
Qed.

Lemma xor_sym' :
  forall P Q : Prop, xor P Q <-> xor Q P.
Proof.
  split; apply xor_sym.
Qed.

Lemma xor_cotrans :
  LEM ->
    (forall P Q R : Prop, xor P Q -> xor P R \/ xor Q R).
Proof.
  unfold LEM, xor. intros LEM P Q R H.
  destruct H as [[p nq] | [q np]].
    destruct (LEM R) as [r | nr].
      right. right. split; assumption.
      left. left. split; assumption.
    destruct (LEM R) as [r | nr].
      left. right. split; assumption.
      right. left. split; assumption.
Qed.

Lemma xor_assoc :
  forall P Q R : Prop,
    xor P (xor Q R) <-> xor (xor P Q) R.
Proof.
  unfold xor. split.
    firstorder.
Abort.

Lemma xor_not_iff :
  forall P Q : Prop, xor P Q -> ~ (P <-> Q).
Proof.
  unfold xor, iff.
  intros P Q H1 H2.
  destruct H2 as [pq qp], H1 as [[p nq] | [np q]].
    apply nq, pq. assumption.
    apply np, qp. assumption.
Qed.

Lemma not_iff_xor :
  LEM ->
    forall P Q : Prop, ~ (P <-> Q) -> xor P Q.
Proof.
  unfold LEM, xor.
  intros LEM P Q H.
  destruct (LEM P) as [p | np], (LEM Q) as [q | nq].
    contradiction H. split; trivial.
    left. split; assumption.
    right. split; assumption.
    contradiction H. split; intro; contradiction.
Qed.

Lemma xor_spec :
  forall P Q : Prop, xor P Q <-> (P \/ Q) /\ (~ P \/ ~ Q).
Proof.
  unfold xor, iff. split.
    intros [[p nq] | [np q]].
      split.
        left. assumption.
        right. assumption.
      split.
        right. assumption.
        left. assumption.
    intros [[p | q] [np | nq]].
      contradiction.
      left. split; assumption.
      right. split; assumption.
      contradiction.
Qed.

Lemma xor_False_r :
  forall P : Prop, xor P False <-> P.
Proof.
  unfold xor, iff. split.
    intro H. destruct H as [[p _] | [_ f]].
      assumption.
      contradiction.
    intro p. left. split.
      assumption.
      intro f. contradiction.
Qed.

Lemma xor_False_l :
  forall P : Prop, xor False P <-> P.
Proof.
  split.
    intro x. apply xor_sym in x. apply xor_False_r. assumption.
    intro p. unfold xor. right. split.
      intro f. contradiction.
      assumption.
Qed.

Lemma xor_True_l :
  forall P : Prop, xor True P <-> ~ P.
Proof.
  unfold xor, iff. split.
    intros [[_ np] | [f _]].
      assumption.
      contradiction.
    intro np. left. split.
      trivial.
      assumption.
Qed.

Lemma xor_True_r :
  forall P : Prop, xor P True <-> ~ P.
Proof.
  intros. rewrite xor_sym', xor_True_l. reflexivity.
Qed.