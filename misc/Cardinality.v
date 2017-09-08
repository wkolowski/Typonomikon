Require Import List.
Import ListNotations.

Inductive FinType (A : Type) : list A -> Prop :=
    | empty_fin : (A -> False) -> FinType A []
    | singl_fin : forall x : A, FinType A [x]
    | nonempty_fin : forall (h : A) (t : list A),
        FinType A t -> ~ In h t -> FinType A (h :: t).

Theorem unit_finite : FinType unit [tt].
Proof.
  constructor.
Qed.

Theorem unit_no_2 : forall l : list unit, 2 <= length l -> ~ FinType unit l.
Proof.
  induction l as [| h t].
    inversion 1.
    destruct t as [| h' t'].
      inversion 1. inversion H1.
      simpl. do 2 intro. do 2 apply le_S_n in H. inversion H0; subst.
        destruct h, h'. apply H4. constructor. trivial.
Qed.

Theorem bool_finite : FinType bool [true; false].
Proof.
  repeat constructor. inversion 1; inversion H0.
Qed.

Theorem unit_not_bool : ~ unit = bool.
Proof.
  intro. pose proof unit_no_2. unfold not in H0.
  rewrite H in H0. apply (H0 [true; false]).
    trivial.
    apply bool_finite.
Qed.

Theorem wut : ~ prod Empty_set unit = prod Empty_set bool.
Proof.
  intro.
  remember (prod Empty_set unit) as A.
  remember (prod Empty_set bool) as B.
  generalize dependent HeqA.
  generalize dependent HeqB.
  destruct H. intros.
Abort.

Goal ~ forall A B C : Type, prod A B = prod A C -> B = C.
Proof.
  intro. cut (unit = bool).
    apply unit_not_bool.
    specialize (H Empty_set unit bool).
Abort. (* TODO *)