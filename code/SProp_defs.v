(** * Sort [SProp], czyli zdania, ale takie jakby inne (TODO) *)

(* begin hide *)
Set Warnings "-cannot-define-projection".

Set Allow StrictProp.

Inductive sEmpty : SProp := .

Inductive sUnit : SProp :=
    | stt : sUnit.

Inductive seq {A : Type} (x : A) : A -> SProp :=
    | srefl : seq x x.

Goal forall A : Type, sEmpty -> A.
Proof.
  destruct 1.
Qed.

Goal
  forall {A : Type} (P : A -> Type) (x y : A),
    seq x y -> P x -> P y.
Proof.
  intros A P x y Hs Hp.
Abort.

Inductive Box (A : Type) : Prop :=
    | box : A -> Box A.

Print Box_sind.

Require Import SetIsType.

Lemma SetIsType : Set = Type.
Proof.
  reflexivity.
Qed.
(* end hide *)