Require Import B.

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