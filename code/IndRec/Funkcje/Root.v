Require Import Arith.
Require Import Lia Arith.

Lemma root : forall n : nat, {r : nat | r * r <= n < (S r) * (S r)}.
Proof.
  induction n as [| n'].
    exists 0. cbn; split.
      trivial.
      apply le_n.
    destruct IHn' as [r [H1 H2]].
    destruct (le_lt_dec ((S r) * (S r)) (S n')).
      exists (S r). cbn; split.
        cbn in l. assumption.
        cbn in *. apply lt_n_S.
        repeat match goal with
            | H : context [?x + S ?y] |- _ =>
                rewrite (plus_comm x (S y)) in H; cbn in H
            | H : context [?x * S ?y] |- _ =>
                rewrite (mult_comm x (S y)) in H; cbn in H
            | |- context [?x + S ?y] => rewrite (plus_comm x (S y)); cbn
            | |- context [?x * S ?y] => rewrite (mult_comm x (S y)); cbn
        end. lia.
      exists r. cbn; split.
        apply le_trans with n'.
          assumption.
          apply le_S. apply le_n.
        cbn in l. assumption.
Defined.

Definition root' (n : nat) : nat.
Proof.
  destruct (root n). exact x.
Defined.

Eval compute in root' 24.

Fixpoint div4 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | S (S (S (S n'))) => S (div4 n')
end.

Fixpoint nat_ind_4 (P : nat -> Prop) (H0 : P 0) (H1 : P 1) (H2 : P 2) (H3 : P 3)
    (H4 : forall n : nat, P n -> P (S (S (S (S n))))) (n : nat) : P n.
Proof.
  destruct n.
    exact H0.
    destruct n.
    exact H1.
      destruct n.
        exact H2.
        destruct n.
          exact H3.
          apply H4. apply nat_ind_4; assumption.
Defined.

Fixpoint nat_ind_3 (P : nat -> Prop) (H0 : P 0) (H1 : P 1) (H2 : P 2)
    (H3 : forall n : nat, P n -> P (S (S (S n)))) (n : nat) : P n.
Proof.
  destruct n.
    exact H0.
    destruct n.
    exact H1.
      destruct n.
        exact H2.
        apply H3. apply nat_ind_3; assumption.
Defined.

Require Import Wf.

Print well_founded_induction.

Lemma div4_lemma : forall n : nat,
    S (div4 n) < S (S (S (S n))).
Proof.
  induction n using nat_ind_4; cbn; lia.
Qed.

Lemma nat_ind_div4 (P : nat -> Type) (H0 : P 0)
    (Hdiv : forall n : nat, P (div4 n) -> P n) (n : nat) : P n.
Proof.
  apply (Fix lt_wf P). intros.
  destruct x.
    apply H0.
    destruct x.
      apply Hdiv. cbn. apply H0.
      destruct x.
        apply Hdiv. cbn. apply H0.
        destruct x.
          apply Hdiv. cbn. apply H0.
          apply Hdiv. cbn. apply X. apply div4_lemma.
Defined.

Ltac nat_cbn := repeat
match goal with
    | H : context [?x + S ?y] |- _ =>
        rewrite (plus_comm x (S y)) in H; cbn in H
    | H : context [?x * S ?y] |- _ =>
        rewrite (mult_comm x (S y)) in H; cbn in H
    | |- context [?x + S ?y] => rewrite (plus_comm x (S y)); cbn
    | |- context [?x * S ?y] => rewrite (mult_comm x (S y)); cbn
end;
repeat rewrite plus_0_r.