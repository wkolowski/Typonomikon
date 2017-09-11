Require Import List.
Import ListNotations.
Require Import Classes.SetoidClass.
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

Hint Constructors bin_equiv.

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

Theorem normalize_spec : forall b : bin, bin_equiv b (normalize b).
Proof.
  induction b as [| d ds].
    simpl. eauto.
    destruct d; simpl.
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

Fixpoint divmod2 (n : nat) : nat * D :=
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

Program Fixpoint nat_to_bin (n : nat) {measure n} : bin :=
    let (a, b) := (div2 n, mod2 n) in
    match a, b with
        | 0, O => []
        | 0, I => [I]
        | _, _ => b :: nat_to_bin a
    end.
Next Obligation.
  destruct a as [| a'].
    cut False.
        