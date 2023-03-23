From stdpp Require Import prelude well_founded.

Lemma wf_tc :
  forall {A : Type} (R : A -> A -> Prop),
    wf R -> wf (tc R).
Proof.
  unfold wf.
  intros A R Hwf a.
  specialize (Hwf a).
  induction Hwf as [a H IH].
  constructor.
  intros y Hy.
  induction Hy.
  - by apply IH.
  - by apply IHHy; [| | constructor].
Qed.

Module Fail.

Require Import Equality.

Inductive step : nat -> nat -> Prop :=
| step' : forall n : nat, step n (S n).

Lemma wf_step :
  wf step.
Proof.
  intro n.
  induction n as [| n' IH].
  - constructor. inversion 1.
  - constructor. inversion 1; subst. apply IH.
Defined.

Lemma wf_tc_step :
  wf (tc step).
Proof.
  intro n.
  induction n as [| n' IH].
  - constructor.
    intros m H.
    exfalso.
    dependent induction H.
    + inversion H.
    + by apply IHtc.
  - constructor.
    intros m H.
    revert IH.
    dependent induction H; intros.
    + by inversion H; subst.
    + inversion H; subst.
      specialize (IHtc _ eq_refl IH).
      inversion IHtc.
      apply H1.
      do 2 constructor.
Defined.

End Fail.

Module Success.

Inductive step : nat -> nat -> Prop :=
| step' : forall n : nat, step (S n) n.

Lemma wf_step :
  wf step.
Proof.
  intro n.
  induction n as [| n' IH].
  - constructor. inversion 1; subst. constructor. inversion 1; subst.
Abort.

End Success.