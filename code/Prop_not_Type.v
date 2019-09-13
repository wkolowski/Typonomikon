Inductive buul : Prop :=
    | truu : buul
    | faals : buul.

Require Import ProofIrrelevance.

Goal forall P : Prop, @eq Type P bool -> False.
Proof.
  intros.
  assert (forall b1 b2 : bool, b1 = b2).
    rewrite <- H. apply proof_irrelevance.
  specialize (H0 true false). inversion H0.
Qed.

Definition transport
  {A : Type} (P : A -> Type) {x y : A} (p : x = y) : P x -> P y.
Proof.
  destruct p. exact (@id _).
Defined.

Goal Prop <> Type.
Proof.
  intro.
  pose Unnamed_thm.
  assert (~ forall A : Type, A = bool -> False).
    intro. apply (H0 bool). reflexivity.
  assert (forall P : Type -> Type, P Type -> P Prop).
    intros. rewrite H. assumption.
  apply H0. intros. apply eq_sym in H.
  assert (~ exists (P : Prop) (x y : P), x <> y).
    admit.
  apply H2. exists (transport (@id _) H bool).
Abort.