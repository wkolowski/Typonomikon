Require Import Bool.

Print reflect.

Print BoolSpec.

Print CompareSpec.

Inductive Spec {A : Type} (P : A -> Prop) : A -> Prop :=
    | spec : forall x : A, P x -> Spec P x.

Ltac spec_aux H :=
match type of H with
    | Spec ?P ?x => destruct H as [x H], x
end.

Tactic Notation "spec" hyp(H) := spec_aux H.

Tactic Notation "spec" integer(n) :=
  intros until n;
match goal with
    | H : Spec _ _ |- _ => spec_aux H
end.

Goal
  forall (P Q : Prop) (b : bool),
    Spec (fun b : bool => if b then P else Q) b
      <->
    BoolSpec P Q b.
Proof.
  split.
    spec 1; constructor; assumption.
    destruct 1; constructor; assumption.
Qed.

Goal
  forall (P Q : Prop) (b : bool),
    Spec (fun b : bool => if b then P else Q) b
      <->
    BoolSpec P Q b.
Proof.
  split.
    spec 1; constructor; assumption.
    destruct 1; constructor; assumption.
Qed.

Lemma Spec_char :
  forall (A : Type) (P : A -> Prop) (x : A),
    P x <-> Spec P x.
Proof.
  split.
    intro. constructor. assumption.
    destruct 1. assumption.
Qed.

Inductive Box (A : Type) : Prop :=
    | box : A -> Box A.

Print Box_sind.

Require Import SetIsType.

Lemma SetIsType : Set = Type.
Proof.
  reflexivity.
Qed.