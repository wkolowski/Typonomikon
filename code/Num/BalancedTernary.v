Require Import Lia ZArith Recdef.

Import Pos.

Inductive Z3' : Type :=
| Plus       : Z3'
| Minus      : Z3'
| ShiftPlus  : Z3' -> Z3'
| ShiftMinus : Z3' -> Z3'
| ShiftZero  : Z3' -> Z3'.

Inductive Z3 : Type :=
| Zero    : Z3
| Nonzero : Z3' -> Z3.

Coercion Nonzero : Z3' >-> Z3.

Fixpoint toZ' (n : Z3') : Z :=
match n with
| Plus => 1
| Minus => -1
| ShiftPlus n' => 1 + 3 * toZ' n'
| ShiftMinus n' => -1 + 3 * toZ' n'
| ShiftZero n' => 3 * toZ' n'
end.

Definition toZ (n : Z3) : Z :=
match n with
| Zero => 0
| Nonzero n' => toZ' n'
end.

Fixpoint neg' (n : Z3') : Z3' :=
match n with
| Plus => Minus
| Minus => Plus
| ShiftPlus n' => ShiftMinus (neg' n')
| ShiftMinus n' => ShiftPlus (neg' n')
| ShiftZero n' => ShiftZero (neg' n')
end.

Lemma neg'_neg' :
  forall n : Z3', neg' (neg' n) = n.
Proof.
  induction n as [| | n' | n' | n']; cbn; congruence.
Qed.

Definition neg (n : Z3) : Z3 :=
match n with
| Zero => Zero
| Nonzero n' => neg' n'
end.

Lemma neg_neg :
  forall n : Z3, neg (neg n) = n.
Proof.
  destruct n; cbn.
    reflexivity.
    f_equal. apply neg'_neg'.
Qed.

Fixpoint increment' (n : Z3') : Z3 :=
match n with
| Plus => ShiftMinus Plus
| Minus => Zero
| ShiftPlus n' =>
  match increment' n' with
  | Zero => Minus
  | Nonzero n'' => ShiftMinus n''
  end
| ShiftMinus n' => ShiftZero n'
| ShiftZero n' => ShiftPlus n'
end.

Definition increment (n : Z3) : Z3 :=
match n with
| Zero => Plus
| Nonzero n' => increment' n'
end.

Lemma toZ_increment' :
  forall n : Z3', toZ (increment' n) = (1 + toZ' n)%Z.
Proof.
  induction n as [| | n' | n' | n']; cbn [increment' toZ toZ']; try lia.
  destruct (increment' n'); cbn [toZ toZ'] in *; lia.
Qed.

Lemma toZ_increment :
  forall n : Z3, toZ (increment n) = (1 + toZ n)%Z.
Proof.
  destruct n as [| n'].
  - reflexivity.
  - apply toZ_increment'.
Qed.

Definition decrement' (n : Z3') : Z3 :=
  neg (increment' (neg' n)).

Definition decrement (n : Z3) : Z3 :=
  neg (increment (neg n)).

Definition shiftMinus (n : Z3) : Z3 :=
match n with
| Zero => Minus
| Nonzero n' => ShiftMinus n'
end.

Definition shiftPlus (n : Z3) : Z3 :=
match n with
| Zero => Plus
| Nonzero n' => ShiftPlus n'
end.

Definition shiftZero (n : Z3) : Z3 :=
match n with
| Zero => Zero
| Nonzero n' => ShiftZero n'
end.

Function add (n m : Z3') : Z3 :=
match n with
| Plus => increment m
| Minus => decrement m
| ShiftPlus n' =>
  match m with
  | Plus => increment n
  | Minus => decrement n
  | ShiftPlus m' => shiftMinus (increment (add n' m'))
  | ShiftMinus m' => shiftZero (add n' m')
  | ShiftZero m' => shiftPlus (add n' m')
  end
| ShiftMinus n' =>
  match m with
  | Plus => increment n
  | Minus => decrement n
  | ShiftPlus m' => shiftZero (add n' m')
  | ShiftMinus m' => shiftPlus (decrement (add n' m'))
  | ShiftZero m' => shiftMinus (add n' m')
  end
| ShiftZero n' =>
  match m with
  | Plus => shiftPlus n'
  | Minus => shiftMinus n'
  | ShiftPlus m' => shiftPlus (add n' m')
  | ShiftMinus m' => shiftMinus (add n' m')
  | ShiftZero m' => shiftZero (add n' m')
  end
end.

Lemma toZ_neg :
  forall n : Z3, toZ (neg n) = (- toZ n)%Z.
Proof.
  destruct n as [| n]; cbn.
  - reflexivity.
  - induction n as [| | n' | n' | n']; cbn [neg' toZ']; lia.
Qed.

Lemma decrement_correct :
  forall n : Z3, toZ (decrement n) = (-1 + toZ n)%Z.
Proof.
  unfold decrement.
  intro n.
  rewrite toZ_neg, toZ_increment, toZ_neg. lia.
Qed.

Lemma toZ_shiftMinus :
  forall n : Z3, toZ (shiftMinus n) = (-1 + 3 * toZ n)%Z.
Proof.
  destruct n as [| n']; reflexivity.
Qed.

Lemma toZ_shiftPlus :
  forall n : Z3, toZ (shiftPlus n) = (1 + 3 * toZ n)%Z.
Proof.
  destruct n as [| n']; reflexivity.
Qed.

Lemma toZ_shiftZero :
  forall n : Z3, toZ (shiftZero n) = (3 * toZ n)%Z.
Proof.
  destruct n as [| n']; reflexivity.
Qed.

Lemma add_correct :
  forall n m : Z3', toZ (add n m) = (toZ' n + toZ' m)%Z.
Proof.
  intros.
  functional induction add n m;
  rewrite ?toZ_shiftMinus, ?toZ_shiftPlus, ?toZ_shiftZero,
            ?toZ_increment, ?decrement_correct;
  cbn [toZ' toZ]; lia.
Qed.

Definition add' (n m : Z3) : Z3 :=
match n, m with
| Zero, _ => m
| _, Zero => n
| Nonzero n', Nonzero m' => add n' m'
end.

Definition mul2 (n : Z3) : Z3 :=
  add' n n.

Fixpoint fromPositive (p : positive) : Z3 :=
match p with
| xH => Plus
| xI p' => increment (mul2 (fromPositive p'))
| xO p' => mul2 (fromPositive p')
end.

Definition fromZ (n : Z) : Z3 :=
match n with
| Z0 => Zero
| Zpos p => fromPositive p
| Zneg p => neg (fromPositive p)
end.

Lemma toZ_add' :
  forall n m : Z3, toZ (add' n m) = (toZ n + toZ m)%Z.
Proof.
  destruct n as [| n'], m as [| m']; cbn [toZ add'].
  - reflexivity.
  - reflexivity.
  - lia.
  - rewrite add_correct. reflexivity.
Qed.

Lemma toZ_mul2 :
  forall n : Z3, toZ (mul2 n) = (2 * toZ n)%Z.
Proof.
  unfold mul2.
  intros.
  rewrite toZ_add'. lia.
Qed.

Lemma toZ_fromPositive :
  forall p : positive, toZ (fromPositive p) = Zpos p.
Proof.
  induction p as [p' | p' |]; cbn.
  - rewrite toZ_increment, toZ_mul2, IHp'. reflexivity.
  - rewrite toZ_mul2, IHp'. reflexivity.
  - reflexivity.
Qed.

Lemma toZ_fromZ :
  forall n : Z, toZ (fromZ n) = n.
Proof.
  induction n as [| n' | n']; cbn.
  - reflexivity.
  - apply toZ_fromPositive.
  - rewrite toZ_neg, toZ_fromPositive. lia.
Qed.

Lemma toZ'_inv_Zero :
  forall n : Z3', (toZ' n = 0)%Z -> False.
Proof.
  induction n as [| | n' | n' | n']; cbn [toZ']; intros; try lia.
Qed.

Lemma toZ'_inv_Plus :
  forall n : Z3', (toZ' n = 1)%Z -> n = Plus.
Proof.
  induction n as [| | n' | n' | n']; cbn [toZ']; intros H; try lia.
  - reflexivity.
  - assert (toZ' n' = 0%Z) by lia. apply toZ'_inv_Zero in H0. contradiction.
Qed.

Lemma toZ'_inv_Minus:
  forall n : Z3', (toZ' n = -1)%Z -> n = Minus.
Proof.
  induction n as [| | n' | n' | n']; cbn [toZ']; intros; try lia.
  - reflexivity.
  - assert (toZ' n' = 0%Z) by lia. apply toZ'_inv_Zero in H0. contradiction.
Qed.

Lemma toZ_Zero :
  forall n : Z3, (toZ n = 0)%Z -> n = Zero.
Proof.
  destruct n as [| n]; cbn.
  - reflexivity.
  - intro H. apply toZ'_inv_Zero in H. contradiction.
Qed.

Lemma toZ'_inj :
  forall n m : Z3', toZ' n = toZ' m -> n = m.
Proof.
  induction n as [| | n' | n' | n']; cbn [toZ']; intros; try lia.
  - symmetry in H. apply toZ'_inv_Plus in H. congruence.
  - symmetry in H. apply toZ'_inv_Minus in H. congruence.
  - destruct m; cbn [toZ'] in *; try lia.
    + assert (toZ' n' = 0%Z) by lia. apply toZ'_inv_Zero in H0. contradiction.
    + f_equal. apply IHn'. lia.
  - destruct m; cbn [toZ'] in *; try lia.
    + assert (toZ' n' = 0%Z) by lia. apply toZ'_inv_Zero in H0. contradiction.
    + f_equal. apply IHn'. lia.
  - destruct m; cbn [toZ'] in *; try lia.
    f_equal. apply IHn'. lia.
Qed.

Lemma toZ_inj :
  forall n m : Z3, toZ n = toZ m -> n = m.
Proof.
  destruct n as [| n], m as [| m]; cbn; intros.
  - reflexivity.
  - symmetry in H. apply toZ'_inv_Zero in H. contradiction.
  - apply toZ'_inv_Zero in H. contradiction.
  - apply toZ'_inj in H. inversion H. reflexivity.
Qed.

Lemma fromZ_toZ :
  forall n : Z3, fromZ (toZ n) = n.
Proof.
  intros.
  apply toZ_inj, toZ_fromZ.
Qed.