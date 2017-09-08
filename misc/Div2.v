Fixpoint nat_ind2 (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
    (HSS : forall n : nat, P n -> P (S (S n))) (n : nat) : P n.
Proof.
  destruct n as [| n'].
    assumption.
    destruct n' as [| n''].
      assumption.
      apply HSS. apply nat_ind2; auto.
Defined.

Function div2 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => S (div2 n')
end.

Theorem div2_2n : forall n : nat, div2 (2 * n) = n.
Proof.
  destruct n as [| n']; simpl.
    trivial.
    induction n' as [| n'']; simpl.
      trivial.
      rewrite <- plus_n_O in *. do 2 rewrite <- plus_n_Sm in *. simpl.
        f_equal. assumption.
Restart.
  intros. remember (2 * n) as m. generalize dependent n.
  functional induction div2 m; intros.
    destruct n; simpl in *; inversion Heqm. trivial.
    destruct n; simpl in *; inversion Heqm.
      destruct n; simpl in H0; inversion H0.
    destruct n as [| [| n]]; simpl in *.
      inversion Heqm.
      inversion Heqm. simpl. trivial.
      rewrite (IHn (S n)).
        trivial.
        inversion Heqm; subst; clear Heqm.
          rewrite <- !plus_n_O, <- !plus_n_Sm. simpl. trivial.
Qed.

Fixpoint mod2 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n') => mod2 n'
end.

Theorem mod2_even : forall n : nat, mod2 (2 * n) = 0.
Proof.
  destruct n as [| n']; simpl.
    trivial.
    induction n' as [| n'']; simpl.
      trivial.
      rewrite <- plus_n_O in *. do 2 rewrite <- plus_n_Sm in *. simpl.
        assumption.
Restart.
  induction n using nat_ind2; simpl in *; trivial.
    rewrite <- plus_n_O in *. do 2 rewrite <- plus_n_Sm.
      simpl. assumption.
Qed.

Theorem mod2_odd : forall n : nat, mod2 (S (2 * n)) = 1.
Proof.
  destruct n as [| n']; simpl.
    trivial.
    induction n' as [| n'']; simpl.
      trivial.
      rewrite <- plus_n_O in *. do 2 rewrite <- plus_n_Sm in *. simpl.
        assumption.
Qed.

Eval compute in (div2 15, mod2 15).

Theorem div2_wut : forall n : nat, 2 * div2 n + mod2 n = n.
Proof.
  induction n as [| n']; simpl.
    trivial.
    induction n' as [| n'']; simpl.
      trivial.
      rewrite <- plus_n_O in *. Require Import Arith.
        rewrite <- plus_Sn_m. rewrite <- plus_n_Sm. simpl.
          f_equal. rewrite <- IHn''. unfold div2.
            repeat rewrite <- plus_assoc. destruct n''; simpl.
              trivial.
Restart.
  apply nat_ind2; simpl; trivial.
    intros. rewrite <- plus_n_O in *.
    rewrite <- plus_Sn_m, <- plus_n_Sm. simpl. rewrite H. trivial.
Qed.

Fixpoint evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

Fixpoint quickMul (fuel n m : nat) : nat :=
match fuel with
    | 0 => 42
    | S fuel' => match n with
        | 0 => 0
        | _ => let res := quickMul fuel' (div2 n) m in
            if evenb n then res + res else res + res + m
        end
end.



Time Eval compute in 220 * 430.
Time Eval compute in quickMul 1000 220 430.