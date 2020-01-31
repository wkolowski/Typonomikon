Require Import B.

Definition WLEM : Prop :=
  forall P : Prop, ~ P \/ ~ ~ P.

Lemma WLEM_hard :
  forall P : Prop, ~ P \/ ~ ~ P.
Proof.
  intro P. left. intro p.
Restart.
  intro P. right. intro np. apply np.
Abort.

Lemma WLEM_irrefutable :
  forall P : Prop, ~ ~ (~ P \/ ~ ~ P).
Proof.
  intros P H.
  apply H. left. intro p.
  apply H. right. intro np.
  contradiction.
Qed.

Lemma LEM_WLEM :
  LEM -> WLEM.
Proof.
  unfold LEM, WLEM.
  intros LEM P.
  destruct (LEM P) as [p | np].
    right. intro np. contradiction.
    left. assumption.
Qed.

Lemma MI_WLEM :
  MI -> WLEM.
Proof.
  unfold MI, WLEM.
  intros MI P.
  destruct (MI P P) as [np | p].
    trivial.
    left. assumption.
    right. intro np. contradiction.
Qed.

Lemma ME_WLEM :
  ME -> WLEM.
Proof.
  unfold ME, WLEM.
  intros ME P.
  destruct (ME P P) as [[p _] | [np _]].
    split; trivial.
    right. intro np. contradiction.
    left. assumption.
Qed.

Lemma DNE_WLEM :
  DNE -> WLEM.
Proof.
  unfold DNE, WLEM.
  intros DNE P.
  apply DNE.
  intro H. apply H.
  right. intro np.
  apply H.
  left. assumption.
Qed.

Lemma CM_WLEM :
  CM -> WLEM.
Proof.
  unfold CM, WLEM.
  intros CM P.
  apply CM. intro H.
  right. intro np.
  apply H.
  left. assumption.
Qed.

Lemma Peirce_WLEM :
  Peirce -> WLEM.
Proof.
  unfold Peirce, WLEM.
  intros Peirce P.
  apply (Peirce _ False).
  intro H.
  right. intro np.
  apply H.
  left. assumption.
Qed.

Lemma Contra_WLEM :
  Contra -> WLEM.
Proof.
  unfold Contra, WLEM.
  intros Contra P.
  apply (Contra True).
    intros H _. apply H. right. intro np. apply H. left. assumption.
    trivial.
Qed.