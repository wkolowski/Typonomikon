Module range.

Require Import List.
Import ListNotations.

Fixpoint range (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: range n'
end.

End range.

Module Factorial.

Require Import Arith.

Fixpoint fac (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => mult n (fac n')
end.

Theorem le_1_fac : forall n : nat, 1 <= fac n.
Proof.
  induction n as [| n']; simpl.
    auto.
    apply le_plus_trans. assumption.
Qed.

Theorem le_lin_fac : forall n : nat, n <= fac n.
Proof.
  induction n as [| n']; simpl.
    auto.
    replace (S n') with (1 + n'); auto.
    apply plus_le_compat.
      apply le_1_fac.
      replace n' with (n' * 1) at 1.
        apply mult_le_compat_l. apply le_1_fac.
        rewrite mult_comm. simpl. rewrite plus_comm. simpl. trivial.
Qed.

Fixpoint pow2 (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => 2 * pow2 n'
end.

Theorem le_exp_Fac : forall n : nat,
    4 <= n -> pow2 n <= fac n.
Proof.
  induction 1; simpl.
    repeat constructor.
    rewrite plus_0_r. apply plus_le_compat.
      assumption.
      replace (pow2 m) with (1 * pow2 m).
        apply mult_le_compat.
          apply le_trans with 4; auto.
          assumption.
        rewrite mult_1_l. trivial.
Qed.

End Factorial.

Module Binom.

Require Import Recdef.

Function binom (n k : nat) : nat :=
match n, k with
    | 0, 0 => 1
    | 0, _ => 0
    | _, 0 => 1 
    | S n', S k' => plus (binom n' k') (binom n' k)
end.

Fixpoint double (n : nat) : nat :=
match n with
    | 0 => 0
    | S n' => S (S (double n'))
end.

Lemma binom_0_r :
  forall n : nat, binom n 0 = 1.
Proof.
  destruct n; simpl; trivial.
Qed.

Lemma binom_0_l :
  forall n : nat, binom 0 (S n) = 0.
Proof.
  simpl. trivial.
Qed.

Lemma binom_1_r :
  forall n : nat, binom n 1 = n.
Proof.
  induction n as [| n']; simpl.
    trivial.
    rewrite IHn', binom_0_r. simpl. trivial.
Qed.

Require Import Omega.

Lemma binom_gt :
  forall n k : nat, n < k -> binom n k = 0.
Proof.
  induction n as [| n']; destruct k as [| k']; simpl;
  try (inversion 1; trivial; fail); intro.
    rewrite !IHn'; omega.
Qed.

Lemma binom_n : forall n : nat, binom n n = 1.
Proof.
  induction n as [| n']; simpl.
    trivial.
    rewrite IHn', binom_gt; omega.
Qed.

Theorem binom_sym :
  forall n k : nat, k < n -> binom n k = binom n (minus n k).
Proof.
  induction n as [| n']; destruct k as [| k']; simpl; intros.
    trivial.
    omega.
    rewrite binom_n, binom_gt; omega.
    case_eq (n' - k'); intros; subst.
      omega.
      assert (S k' = n' - n). omega. rewrite <- H0, H1, <- !IHn'; omega.
Qed.

Goal forall n k : nat,
  k * binom (S n) (S k) = n * binom n k.
Proof.
  simpl.
  induction n as [| n']; destruct k as [| k']; simpl; try omega.
Abort.

Theorem binom_spec :
  forall n k : nat,
    k <= n -> fact k * fact (n - k) * binom n k = fact n.
Proof.
  induction n as [| n']; destruct k as [| k'].
    trivial.
    inversion 1.
    intros. simpl. omega.
    intros. simpl.
      rewrite !mult_plus_distr_r, !mult_plus_distr_l.
      rewrite IHn'; try omega.
      rewrite <- !plus_assoc. f_equal.
      rewrite <- 2!(mult_assoc k'). rewrite IHn'; try omega.
Restart.
  intros n k.
  functional induction binom n k; intros; simpl; try omega.
    destruct k. inversion y. omega.
    destruct n; simpl; omega.
    destruct n', k'; simpl in *; try omega.
      rewrite binom_0_r, <- plus_n_O, <- minus_n_O in *.
        assert (0 <= S n') by omega.
        specialize (IHn0 H0). rewrite mult_comm. simpl.
        rewrite binom_1_r. trivial.
      assert (S k' <= S n') by omega.
        specialize (IHn0 H0).
        rewrite <- !IHn0.
        rewrite !mult_plus_distr_r, !mult_plus_distr_l.
        repeat (rewrite ?mult_assoc, ?plus_assoc, ?IHn0). f_equal.
Abort.

End Binom.

Module Div2.

Require Import Div2.

Fixpoint evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

Require Import ZArith.

Fixpoint quickMul (fuel n m : nat) : nat :=
match fuel with
    | 0 => 42
    | S fuel' => match n with
        | 0 => 0
        | _ => let res := quickMul fuel' (div2 n) m in
            if evenb n then res + res else (m + res) + res
        end
end.

Time Eval compute in 430 * 110.
Time Eval compute in quickMul 1000 430 110.

Require Import Recdef.

Function qm (n m : nat) {measure id n} : nat :=
match n with
    | 0 => 0
    | _ => let r := qm (div2 n) m in
        if evenb n then 2 * r else m + 2 * r
end.
Proof.
Abort.

End Div2.

(* end hide *)