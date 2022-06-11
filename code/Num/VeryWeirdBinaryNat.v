Require Import List.
Import ListNotations.

Require Import Classes.SetoidClass.

Require Import Recdef.
Require Import Coq.Program.Wf.

Inductive D : Set :=
    | O : D
    | I : D.

Definition bin : Set := list D.

Inductive bin_equiv : bin -> bin -> Prop :=
    | equiv_refl : forall b : bin, bin_equiv b b
    | equiv_sym : forall b b' : bin, bin_equiv b b' -> bin_equiv b' b
    | equiv_trans : forall b1 b2 b3 : bin,
        bin_equiv b1 b2 -> bin_equiv b2 b3 -> bin_equiv b1 b3
    | equiv_nil : bin_equiv [O] []
    | equiv_leading_zeros : forall b b' : bin,
        bin_equiv b b' -> bin_equiv (O :: b) b'.

#[global] Hint Constructors bin_equiv : core.

#[refine]
#[export]
Instance bin_setoid : Setoid bin :=
{
    equiv := bin_equiv
}.
Proof.
  split; red; eauto.
Qed.

Fixpoint normalize (b : bin) : bin :=
match b with
    | [] => []
    | O :: b' => normalize b'
    | _ => b
end.

Theorem normalize_spec :
  forall b : bin, bin_equiv b (normalize b).
Proof.
  induction b as [| d ds].
    cbn. eauto.
    destruct d; cbn.
      apply equiv_leading_zeros. assumption.
      constructor.
Qed.

Fixpoint bin_to_nat' (b : bin) : nat :=
match b with
    | [] => 0
    | O :: b' => 2 * bin_to_nat' b'
    | I :: b' => 1 + 2 * bin_to_nat' b'
end.

Definition bin_to_nat (b : bin) : nat :=
    bin_to_nat' (rev (normalize b)).

Eval compute in bin_to_nat [I; O; I; O; I; O].

Function divmod2 (n : nat) : nat * D :=
match n with
    | 0 => (0, O)
    | 1 => (0, I)
    | S (S n') => let (a, b) := divmod2 n' in (S a, b)
end.

Fixpoint nat_ind_2 (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
    (H : forall n : nat, P n -> P (S (S n))) (n : nat) : P n :=
match n with
    | 0 => H0
    | 1 => H1
    | S (S n') => H n' (nat_ind_2 P H0 H1 H n')
end.

Ltac inv H := inversion H; subst; clear H.

Lemma divmod2_spec :
  forall (n m : nat) (d : D),
    divmod2 n = (m, d) -> m = 0 \/ m < n.
Proof.
  induction n using nat_ind_2; cbn; intros; inv H.
  - left. reflexivity.
  - left. reflexivity.
  - destruct (divmod2 n). inv H1. destruct (IHn _ _ eq_refl).
    + right. rewrite H. do 2 apply le_n_S. apply le_0_n.
    + right. apply le_n_S. apply le_S. assumption.
Qed.

Function nat_to_bin' (n : nat) {measure id n} : bin :=
    let '(a, b) := divmod2 n in
    match a with
        | 0 => [b]
        | _ => b :: nat_to_bin' a
    end.
Proof.
  intros.
  destruct (divmod2_spec _ _ _ teq); subst.
  - inv H.
  - unfold id. assumption.
Defined.

Definition nat_to_bin (n : nat) : bin := rev (nat_to_bin' n).

Goal
  forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  unfold nat_to_bin. intro.
  functional induction (nat_to_bin' n). cbn.
    destruct b; cbn.
      functional inversion e. reflexivity.
      functional inversion e. reflexivity.
    cbn. unfold bin_to_nat in IHb. destruct a.
      contradiction.
      functional inversion e. subst.
Abort.

Compute bin_to_nat [I; O; I; O].
Compute bin_to_nat [I; O; O; O; I; I; I; I; O; I; I; O; I; I; I].