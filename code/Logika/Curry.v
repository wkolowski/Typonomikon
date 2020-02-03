(** * Paradoks Curry'ego *)

Definition NI : Prop :=
  forall P Q : Prop, ~ (P -> Q) -> P /\ ~ Q.

Require Import W3 WLEM.

Lemma NI_LEM :
  NI -> LEM.
Proof.
  unfold NI, LEM.
  intros NI P.
  destruct (NI (P \/ ~ P) False).
    firstorder.
    assumption.
Qed.

Definition IOR : Prop :=
  forall P Q R : Prop, (P -> Q \/ R) -> (P -> Q) \/ (P -> R).

Lemma IOR_LEM :
  IOR -> LEM.
Proof.
  unfold IOR, LEM.
  intros IOR P.
Abort.


Lemma IOR_WLEM :
  IOR -> WLEM.
Proof.
  unfold IOR, WLEM.
  intros IOR P.
Abort.

Lemma WLEM_IOR :
  WLEM -> IOR.
Proof.
  unfold WLEM, IOR.
  intros WLEM P Q R H.
  destruct (WLEM (P -> Q)).
    right. intro p. destruct (H p).
      contradiction H0. intros _. assumption.
      assumption.
    left. intro p.
Abort.