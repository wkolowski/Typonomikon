Require Import List.
Import ListNotations.

Record Finite (A : Type) : Type :=
{
  enum : list A;
  NoDup_enum : NoDup enum;
  In_enum : forall x : A, In x enum;
}.

Lemma dec :
  forall {A : Type} (l : list A),
    NoDup l -> forall x y : A, In x l -> In y l -> x = y \/ x <> y.
Proof.
  induction 1 as [| h Hnot HND IH].
  - inversion 1.
  - intros x y [-> | Hx] [-> | Hy].
    + left. reflexivity.
    + right. intros ->. contradiction.
    + right. intros ->. contradiction.
    + apply IHIH; assumption.
Qed.

Lemma dec_from_Finite :
  forall {A : Type} (F : Finite A),
    forall x y : A, x = y \/ x <> y.
Proof.
  intros A [enum ND HIn] x y.
  apply (dec enum ND).
  apply HIn.
  apply HIn.
Qed.

Lemma dec' :
  forall {A : Type} (l : list A),
    NoDup l -> forall x y : A, In x l -> In y l -> {x = y} + {x <> y}.
Proof.
  induction l as [| h t].
  - inversion 2.
  - Fail intros ND x y [-> | Hx] [-> | Hy].
    (* ===> The command has indeed failed with message:
            Case analysis on sort Set is not allowed for inductive definition or. *)
Abort.