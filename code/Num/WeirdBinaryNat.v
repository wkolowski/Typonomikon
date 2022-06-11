Require Import Recdef PeanoNat Lia.

(* [Z] to 0, [L n] to 2n + 1, a [R n] to 2n + 2. *)
Inductive Nat : Type :=
| Z : Nat
| L : Nat -> Nat
| R : Nat -> Nat.

Function succ (n : Nat) : Nat :=
match n with
| Z => L Z
| L n' => R n'
| R n' => L (succ n')
end.

Function pred (n : Nat) : Nat :=
match n with
| Z => Z
| L Z => Z
| L n' => R (pred n')
| R n' => L n'
end.

Function add (n m : Nat) : Nat :=
match n, m with
| Z   , _    => m
| _   , Z    => n
| L n', L m' => R (add n' m')
| L n', R m' => succ (R (add n' m'))
| R n', L m' => succ (R (add n' m'))
| R n', R m' => R (succ (add n' m'))
end.

Function div2 (n : Nat) : Nat :=
match n with
| Z => Z
| L n' => n'
| R n' => succ n'
end.

Function mul2 (n : Nat) : Nat :=
  pred (L n).

Function mul (n m : Nat) : Nat :=
match n with
| Z    => Z
| L n' => add (mul2 (mul n' m)) m
| R n' => mul2 (add (mul n' m) m)
end.

Function sub (n m : Nat) : Nat :=
match n, m with
| Z   , _    => Z
| _   , Z    => n
| L n', L m' => mul2 (sub n' m')
| L n', R m' => pred (mul2 (sub n' m'))
| R n', L m' => succ (mul2 (sub n' m'))
| R n', R m' => mul2 (sub n' m')
end.

Function le (n m : Nat) : bool :=
match n, m with
| Z   , _    => true
| _   , Z    => false
| L n', L m' => le n' m'
| L n', R m' => le n' m'
| R n', L m' => false (* 2n <= 2m -1 *)
| R n', R m' => le n' m'
end.

Definition L' (n : nat) : nat :=
  1 + 2 * n.

Definition R' (n : nat) : nat :=
  2 + 2 * n.

Function fromNat (n : Nat) : nat :=
match n with
| Z => 0
| L n' => L' (fromNat n')
| R n' => R' (fromNat n')
end.

Function toNat (n : nat) : Nat :=
match n with
| 0 => Z
| S n' => succ (toNat n')
end.

Compute fromNat (L (L (L (L Z)))).
Compute fromNat (R (R (R (R Z)))).
Compute fromNat (R (R (L (R Z)))).

Compute fromNat (succ (L (L (L (L Z))))).
Compute fromNat (succ (R (R (R (R Z))))).
Compute fromNat (succ (R (R (L (R Z))))).

Compute fromNat (pred (L (L (L (L Z))))).
Compute fromNat (pred (R (R (R (R Z))))).
Compute fromNat (pred (R (R (L (R Z))))).

Compute fromNat (div2 (L (L (L (L Z))))).
Compute fromNat (div2 (R (R (R (R Z))))).
Compute fromNat (div2 (R (R (L (R Z))))).

Compute fromNat (mul2 (L (L (L (L Z))))).
Compute fromNat (mul2 (R (R (R (R Z))))).
Compute fromNat (mul2 (R (R (L (R Z))))).

Lemma pred_succ :
  forall n : Nat,
    pred (succ n) = n.
Proof.
  intros n; functional induction (succ n); cbn.
  1-2: reflexivity.
  rewrite IHn0; clear IHn0.
  destruct n'; cbn; reflexivity.
Qed.

Lemma div2_mul2 :
  forall n : Nat,
    div2 (mul2 n) = n.
Proof.
  intros n; functional induction (mul2 n); cbn.
  induction n as [| n' | n']; cbn.
  1, 3: reflexivity.
  rewrite <- IHn' at 2.
  destruct n'; cbn in *; reflexivity.
Qed.

Lemma fromNat_succ :
  forall n : Nat,
    fromNat (succ n) = S (fromNat n).
Proof.
  intros n; functional induction (fromNat n); cbn; lia.
Qed.

Lemma fromNat_toNat :
  forall n : nat,
    fromNat (toNat n) = n.
Proof.
  intros n; functional induction (toNat n); cbn.
  - reflexivity.
  - rewrite fromNat_succ, IHn0. reflexivity.
Qed.

Lemma L'_S :
  forall n : nat,
    L' (S n) = 2 + L' n.
Proof.
  intros; cbn; lia.
Qed.

Lemma R'_S :
  forall n : nat,
    R' (S n) = 3 + L' n.
Proof.
  intros; cbn; lia.
Qed.

Lemma toNat_L' :
  forall n : nat,
    toNat (L' n) = L (toNat n).
Proof.
  induction n as [| n'].
  - reflexivity.
  - rewrite L'_S.
    change (toNat (2 + _)) with (succ (succ (toNat (L' n')))).
    rewrite IHn'; cbn. reflexivity.
Qed.

Lemma toNat_R' :
  forall n : nat,
    toNat (R' n) = R (toNat n).
Proof.
  induction n as [| n'].
  - reflexivity.
  - rewrite R'_S.
    change (toNat (3 + _)) with (succ (succ (toNat (R' n')))).
    rewrite IHn'; cbn. reflexivity.
Qed.

Lemma toNat_fromNat :
  forall n : Nat,
    toNat (fromNat n) = n.
Proof.
  intros n; functional induction (fromNat n).
  - reflexivity.
  - rewrite toNat_L', IHn0. reflexivity.
  - rewrite toNat_R', IHn0. reflexivity.
Qed.

Lemma add_Z_l :
  forall n : Nat,
    add Z n = n.
Proof. reflexivity. Qed.

Lemma add_Z_r :
  forall n : Nat,
    add n Z = n.
Proof.
  intros []; reflexivity.
Qed.

Lemma add_succ_l :
  forall n m : Nat,
    add (succ n) m = succ (add n m).
Proof.
  intros n m; functional induction (add n m)
  ; cbn; rewrite ?IHn0.
  3-6: reflexivity.
  - destruct m; reflexivity.
  - destruct n; reflexivity.
Qed.

Lemma add_succ_r :
  forall n m : Nat,
    add n (succ m) = succ (add n m).
Proof.
  intros n m; functional induction (add n m)
  ; cbn; rewrite ?IHn0.
  3-6: reflexivity.
  - destruct m; reflexivity.
  - destruct n; cbn; rewrite ?add_Z_r; reflexivity.
Qed.

Lemma add_comm :
  forall n m : Nat,
    add n m = add m n.
Proof.
  intros n m; functional induction (add n m)
  ; cbn; rewrite ?add_Z_r, ?IHn0; reflexivity.
Qed.

Lemma add_assoc :
  forall a b c : Nat,
    add (add a b) c = add a (add b c).
Proof.
  intros a b.
  functional induction (add a b); cbn; intros.
  1-2: reflexivity.
  all: destruct c; cbn; rewrite ?add_succ_l, ?add_succ_r, ?IHn; reflexivity.
Qed.

Lemma mul_Z_l :
  forall n : Nat,
    mul Z n = Z.
Proof. reflexivity. Qed.

Lemma mul_Z_r :
  forall n : Nat,
    mul n Z = Z.
Proof.
  induction n as [| n' IH | n' IH]; cbn.
  - reflexivity.
  - rewrite IH; cbn. reflexivity.
  - rewrite IH; cbn. reflexivity.
Qed.

Lemma fromNat_add :
  forall n m : Nat,
    fromNat (add n m) = fromNat n + fromNat m.
Proof.
  intros n m; functional induction (add n m)
  ; cbn; rewrite ?fromNat_succ; lia.
Qed.

Lemma fromNat_pred :
  forall n : Nat,
    fromNat (pred n) = fromNat n - 1.
Proof.
  intros n; functional induction (pred n); simpl.
  1-2: reflexivity.
  - rewrite IHn0. destruct n'; cbn; lia.
  - unfold L'. lia.
Qed.

Lemma fromNat_mul2 :
  forall n : Nat,
    fromNat (mul2 n) = 2 * fromNat n.
Proof.
  intros n; unfold mul2.
  rewrite fromNat_pred.
  cbn; lia.
Qed.

Lemma fromNat_mul :
  forall n m : Nat,
    fromNat (mul n m) = fromNat n * fromNat m.
Proof.
  intros n m; functional induction (mul n m); simpl.
  - reflexivity.
  - rewrite fromNat_add, fromNat_mul2, IHn0. lia.
  - rewrite fromNat_mul2, fromNat_add, IHn0. lia.
Qed.

Lemma mul_L_r :
  forall n m : Nat,
    mul n (L m) = add (mul2 (mul m n)) n.
Proof.
  induction n as [| n' IH | n' IH]; simpl; intros m.
  - rewrite mul_Z_r; cbn; reflexivity.
Admitted.

Lemma mul_R_r :
  forall n m : Nat,
    mul n (R m) = mul2 (add (mul m n) n).
Proof.
  induction n as [| n' IH | n' IH]; simpl; intros m.
  - rewrite mul_Z_r; cbn; reflexivity.
Admitted.

Lemma mul_comm :
  forall n m : Nat,
    mul n m = mul m n.
Proof.
  intros n m.
  rewrite <- toNat_fromNat, fromNat_mul, Nat.mul_comm, <- fromNat_mul, toNat_fromNat.
  reflexivity.
Qed.

Lemma fromNat_L :
  forall n : Nat,
    fromNat (L n) = L' (fromNat n).
Proof. reflexivity. Qed.

Lemma fromNat_R :
  forall n : Nat,
    fromNat (R n) = R' (fromNat n).
Proof. reflexivity. Qed.

Lemma fromNat_sub :
  forall n m : Nat,
    fromNat (sub n m) = fromNat n - fromNat m.
Proof.
  intros n m; functional induction (sub n m)
  ; rewrite ?fromNat_L, ?fromNat_R, ?fromNat_succ, ?fromNat_pred, ?fromNat_mul2, ?IHn0
  ; unfold L', R'.
  1-4, 6: cbn; lia.
Admitted.