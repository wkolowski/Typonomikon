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
  - intros ND x y [-> | Hx] [-> | Hy].
    + left. reflexivity.
    + right. intros ->. contradiction.
    + right. intros ->. contradiction.
    + apply IHIH; assumption.
Qed.

Lemma dec :
  forall {A : Type} (F : Finite A),
    forall x y : A, In x (enum _ F) -> In y (enum _ F) -> x = y \/ x <> y.
Proof.
  intros A [enum HND HIn] x y; cbn; intros HInx HIny.
  revert x y HInx HIny.
  induction HND as [| h t HIn' HNDt IH]; intros.
  - inversion HInx.
  - specialize (HIn x) as ix.
    specialize (HIn y) as iy.
    cbn in ix, iy.
    destruct ix as [-> | ix], iy as [-> | iy].
    + left. reflexivity.
    + right. intros ->. contradiction.
    + right. intros ->. contradiction.
    + assert (Hneqx : x <> h) by congruence.
      assert (Hneqy : y <> h) by congruence.
      apply IH; [| assumption | assumption].
      intros z. specialize (H z) as [<- | ?].
      * admit.
      * assumption.
Qed.