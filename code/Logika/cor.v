Require Import B W3.

(** Klasyczna dysjunkcja. Panie, na co to komu? *)
Definition cor (P Q : Prop) : Prop :=
  ~ ~ (P \/ Q).

Lemma cor_in_l :
  forall P Q : Prop, P -> cor P Q.
Proof.
  firstorder.
Qed.

Lemma cor_in_r :
  forall P Q : Prop, Q -> cor P Q.
Proof.
  firstorder.
Qed.

Lemma cor_assoc :
  forall P Q R : Prop, cor (cor P Q) R <-> cor P (cor Q R).
Proof.
  firstorder.
Qed.

Lemma cor_comm :
  forall P Q : Prop, cor P Q -> cor Q P.
Proof.
  firstorder.
Qed.

Lemma cor_True_l :
  forall P : Prop, cor True P <-> True.
Proof.
  firstorder.
Qed.

Lemma cor_True_r :
  forall P : Prop, cor P True <-> True.
Proof.
  firstorder.
Qed.

Lemma cor_False_l :
  forall P : Prop, cor False P <-> ~ ~ P.
Proof.
  firstorder.
Qed.

Lemma cor_False_r :
  forall P : Prop, cor P False <-> ~ ~ P.
Proof.
  firstorder.
Qed.

Lemma or_cor :
  forall P Q : Prop, P \/ Q -> cor P Q.
Proof.
  firstorder.
Qed.

Lemma cor_LEM :
  forall P : Prop, cor P (~ P).
Proof.
  unfold cor.
  intros P H.
  apply H. right. intro p.
  apply H. left. assumption.
Qed.

Lemma cor_or_LEM :
  (forall P Q : Prop, cor P Q -> P \/ Q)
    <->
  LEM.
Proof.
  unfold cor, LEM; split.
    intros H P. apply H, cor_LEM.
    intros LEM P Q H. destruct (LEM (P \/ Q)).
      assumption.
      contradiction.
Qed.

Lemma cand_and_LEM :
  (forall P Q : Prop, ~ ~ (P /\ Q) -> P /\ Q) ->
    LEM.
Proof.
  unfold LEM. intros H P.
  destruct (H (P \/ ~ P) True).
    firstorder.
    assumption.
Qed.

Lemma cor_spec :
  forall P Q : Prop,
    cor P Q <-> ~ (~ P /\ ~ Q).
Proof.
  split.
    intros H [np nq]. apply H. intros [p | q].
      apply np, p.
      apply nq, q.
    intros pq npq. apply pq. split.
      intro p. apply npq. left. assumption.
      intro q. apply npq. right. assumption.
Qed.