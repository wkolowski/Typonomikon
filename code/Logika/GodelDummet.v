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

(* TODO
  unfold GD, LEM. split.
    intros GD P. destruct (GD P (~ P)) as [pnp | npp].
      right. intro p. apply pnp; assumption.
      right. intro p.
*)