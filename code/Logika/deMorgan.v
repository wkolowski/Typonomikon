Require Import B.

(** * Logika klasyczna jako (coś więcej niż) logika de Morgana *)

Lemma deMorgan :
  forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros P Q H. left. intro p. apply H. split.
    assumption.
Restart.
  intros P Q H. right. intro q. apply H. split.
Abort.

Lemma deMorgan_irrefutable :
  forall P Q : Prop, ~ ~ (~ (P /\ Q) -> ~ P \/ ~ Q).
Proof.
  intros P Q H.
  apply H. intro npq.
  left. intro p.
  apply H. intros _.
  right. intro q.
  apply npq. split.
    assumption.
    assumption.
Qed.

Lemma deMorgan_WLEM :
  (forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q)
    <->
  (forall P : Prop, ~ P \/ ~ ~ P).
Proof.
  split.
    intros deMorgan P. apply deMorgan. apply noncontradiction.
    intros WLEM P Q H. destruct (WLEM P) as [np | nnp].
      left. assumption.
      destruct (WLEM Q) as [nq | nnq].
        right. assumption.
        left. intro p. apply nnq. intro. apply H. split; assumption.
Qed.

Lemma deMorgan_big :
  forall (A : Type) (P : A -> Prop),
    A -> (~ forall x : A, P x) -> exists x : A, ~ P x.
Proof.
  intros A P a H.
  exists a. intro pa.
  apply H. intro x.
Abort.

Lemma deMorgan_big_irrefutable :
  forall (A : Type) (P : A -> Prop),
    ~ ~ (A -> (~ forall x : A, P x) -> exists x : A, ~ P x).
Proof.
  intros A P H1.
  apply H1. intros a H2.
  exists a. intro pa.
Abort.

Lemma LEM_deMorgan_big :
  (forall P : Prop, P \/ ~ P) ->
    (forall (A : Type) (P : A -> Prop),
       (~ forall x : A, P x) -> exists x : A, ~ P x).
Proof.
  intros LEM A P H. destruct (LEM (exists x : A, ~ P x)).
    assumption.
    contradiction H. intro x. destruct (LEM (P x)).
      assumption.
      contradiction H0. exists x. assumption.
Qed.

Lemma deMorgan_big_WLEM :
  (forall (A : Type) (P : A -> Prop),
     (~ forall x : A, P x) -> exists x : A, ~ P x) ->
  (forall P : Prop, ~ P \/ ~ ~ P).
Proof.
  intros DM P.
    specialize (DM bool (fun b => if b then P else ~ P)).
    cbn in DM. destruct DM as [b H].
      intro H. apply (H false). apply (H true).
      destruct b.
        left. assumption.
        right. assumption.
Qed.