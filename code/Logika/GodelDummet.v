Require Import B.

(** * Godel-Dummet *)

Definition GD : Prop :=
  forall P Q : Prop, (P -> Q) \/ (Q -> P).

Lemma GD_irrefutable :
  forall P Q : Prop, ~ ~ ((P -> Q) \/ (Q -> P)).
Proof.
  intros P Q H.
  apply H. left. intro p.
  exfalso.
  apply H. right. intro q.
  assumption.
Qed.

Lemma LEM_GD :
  LEM -> GD.
Proof.
  unfold LEM, GD. intros LEM P Q.
  destruct (LEM P) as [p | np].
    right. intros _. assumption.
    left. intro p. contradiction.
Qed.

Lemma MI_GD :
  MI -> GD.
Proof.
  unfold MI, GD.
  intros MI P Q.
  destruct (MI P P) as [np | p].
    trivial.
    left. intro p. contradiction.
    right. intros _. assumption.
Qed.

Lemma ME_GD :
  ME -> GD.
Proof.
  unfold ME, GD.
  intros ME P Q.
  destruct (ME P P) as [[p _] | [np _]].
    split; trivial.
    right. intros _. assumption.
    left. intro p. contradiction.
Qed.

Lemma DNE_GD :
  DNE -> GD.
Proof.
  unfold DNE, GD.
  intros DNE P Q.
  apply DNE.
  apply GD_irrefutable.
Qed.

Lemma CM_GD :
  CM -> GD.
Proof.
  unfold CM, GD.
  intros CM P Q.
  apply CM. intro H.
  left. intro p.
  exfalso. apply H.
  right. intros _.
  assumption.
Qed.

Lemma Peirce_GD :
  Peirce -> GD.
Proof.
  unfold Peirce, GD.
  intros Peirce P Q.
  apply (Peirce _ False). intro H.
  left. intro p.
  exfalso. apply H.
  right. intros _.
  assumption.
Qed.

Lemma Contra_GD :
  Contra -> GD.
Proof.
  unfold Contra, GD.
  intros Contra P Q.
  apply (Contra True).
    intros H _. apply H. left. intro p. exfalso.
      apply H. right. intros. assumption.
    trivial.
Qed.