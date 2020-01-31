Require Import B.

Definition LEM3 : Prop :=
  forall P : Prop, P \/ ~ P \/ ~ ~ P.

Lemma LEM_LEM3 :
  LEM -> LEM3.
Proof.
  unfold LEM, LEM3.
  intros LEM P.
  destruct (LEM P) as [p | np].
    left. assumption.
    right. left. assumption.
Qed.

Require Import WLEM.

Lemma LEM3_WLEM :
  LEM3 -> WLEM.
Proof.
  unfold LEM3, WLEM.
  intros LEM3 P.
  destruct (LEM3 P) as [p | [np | nnp]].
    right. intro np. contradiction.
    left. assumption.
    right. assumption.
Qed.

Lemma WLEM_LEM3 :
  WLEM -> LEM3.
Proof.
  unfold WLEM, LEM3.
  intros WLEM P.
  destruct (WLEM P) as [np | nnp].
    right. left. assumption.
    right. right. assumption.
Qed.