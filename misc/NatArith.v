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

(*Lemma double_plus : forall n, double n = n + n .
induction n as [| n'].
Case "n = 0". reflexivity.
Case "n = S n'". simpl. rewrite IHn'. rewrite plus_n_Sm. trivial.
Qed.

Theorem plus_ble_compat_l : forall a b c : nat,
ble_nat a b = true -> ble_nat (c + a) (c + b) = true.
induction a as [| a']; intros.
Case "a = 0". rewrite plus_0_r. induction c as [| c'].
    SCase "c = 0". apply H.
    SCase "c = S c'". simpl. apply IHc'.
Case "a = S a'". induction c as [| c'].
    SCase "c = 0". simpl plus. apply H.
    SCase "c = S c'". simpl. apply IHc'.
Qed.
*)

(*
Theorem plus_ble_compat_r : forall a b c : nat,
ble_nat a b = true -> ble_nat (a + c) (b + c) = true.
induction a as [| a']; intros.
Case "a = 0". induction c as [| c'].
    SCase "c = 0". apply H.
    SCase "c = S c'". rewrite <- plus_n_Sm, <- plus_n_Sm. apply IHc'.
Case "a = S a'". induction c as [| c'].
    SCase "c = 0". rewrite plus_0_r, plus_0_r. apply H.
    SCase "c = S c'". rewrite <- plus_n_Sm, <- plus_n_Sm. apply IHc'.
Qed.




Theorem ble_nat_refl : forall n : nat, true = ble_nat n n.
induction n as [| n'].
Case "n = 0". reflexivity.
Case "n = S n'". simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat, beq_nat 0 (S n) = false.
intro. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n : nat, beq_nat (S n) 0 = false.
intro. reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.
intros. rewrite H. trivial. Abort.

Theorem plus_id_exercise : forall a b c : nat, a = b -> b = c -> a + b = b + c.
intros. rewrite H, H0. trivial. Abort.

Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
intros. simpl. trivial. Abort.

Theorem mult_S_1 : forall n m : nat,  m = S n ->  m * (1 + n) = m * m.
intros. simpl. rewrite <- H. trivial. Abort.

Theorem plus_1_neq_0_firsttry : forall n : nat, beq_nat (n + 1) 0 = false.
intro.
destruct n as [| n']; reflexivity. Abort.

Theorem zero_nbeq_plus_1 : forall n : nat, beq_nat 0 (n + 1) = false.
intro.
destruct n; reflexivity.
Qed.

Theorem double_induction: forall (P : nat -> nat -> Prop), P 0 0 ->
(forall m : nat, P m 0 -> P (S m) 0) -> (forall n : nat, P 0 n -> P 0 (S n)) ->
(forall m n : nat, P m n -> P (S m) (S n)) -> forall m n : nat, P m n.
intros P P00 Im In IS. induction m as [| m']; intros.
Case "m = 0". induction n as [| n'].
    SCase "n = 0". apply P00.
    SCase "n = S n'". apply In. apply IHn'.
Case "m = S m'". induction n as [| n'].
    SCase "n = 0". apply Im. apply IHm'.
    SCase "n = S n'". apply IS. apply IHm'.
Qed.

Lemma S_not_eq : forall n m : nat, S n <> S m -> n <> m.
intros n m. unfold not. intros. apply H. apply f_equal. apply H0.
Qed.

Theorem beq_nat_0_l : forall n, beq_nat 0 n = true -> n = 0.
intros. induction n as [| n'].
Case "n = 0". trivial.
Case "n = S n'". inversion H.
Qed.

Theorem beq_nat_0_r : forall n, beq_nat n 0 = true -> n = 0.
intros. induction n as [| n'].
Case "n = 0". trivial.
Case "n = S n'". inversion H.
Qed.

Theorem beq_nat_refl : forall n : nat, true = beq_nat n n.
induction n as [| n'].
Case "n = 0". trivial.
Case "n = S n'". simpl. apply IHn'.
Qed.

Theorem beq_nat_true : forall n m : nat, beq_nat n m = true -> n = m.
induction n as [| n']; intros.
Case "n = 0". destruct m as [|m'].
    SCase "m = 0". trivial.
    SCase "m = S m'". inversion H.
Case "n = Sn'". destruct m as [| m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'". apply f_equal. apply IHn'. simpl in H. apply H.
Qed.

Lemma beq_nat_false : forall (n m : nat), beq_nat n m = false -> n <> m.
induction n as [| n']; intros.
Case "n = 0". destruct m as [| m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'". discriminate.
Case "n = S n'". destruct m as [| m'].
    SCase "m = 0". discriminate.
    SCase "m = S m'". simpl in H. apply IHn' in H. apply not_eq_S. apply H.
Qed.

Lemma beq_nat_false2 : forall (n m : nat), n <> m -> beq_nat n m = false.
induction n as [| n']; intros.
Case "n = 0". destruct m as [| m'].
    SCase "m = 0". contradiction H. trivial.
    SCase "m = S n'". reflexivity.
Case "n = S n'". destruct m as [| m'].
    SCase "m = 0". trivial.
    SCase "m = S m'". simpl. apply IHn'. apply S_not_eq in H. apply H.
Qed.

Theorem beq_nat_sym : forall (n m : nat), beq_nat n m = beq_nat m n.
intros. destruct (beq_nat n m) eqn: eq_n_m.
Case "n = m". apply beq_nat_true in eq_n_m. rewrite eq_n_m. apply beq_nat_refl.
Case "n =/= m". apply beq_nat_false in eq_n_m. symmetry. apply beq_nat_false2.
    unfold not. unfold not in eq_n_m. intro. apply eq_n_m. symmetry. apply H.
Qed.

Theorem beq_nat_trans : forall n m p : nat,
beq_nat n m = true -> beq_nat m p = true -> beq_nat n p = true.
intros. apply beq_nat_true in H. apply beq_nat_true in H0.
rewrite H, H0. symmetry; apply beq_nat_refl.
Qed.
*)

(* end hide *)
