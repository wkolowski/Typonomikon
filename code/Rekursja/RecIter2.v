Require Import Omega.
Require Export Nat.

Definition divF (f : nat -> forall k : nat, 0 < k -> nat)
  (n k : nat) (H : 0 < k) : nat :=
match le_lt_dec k n with
    | left _ => S (f (n - k) k H)
    | right _ => 0
end.

(*Arguments iter {A} _ _.*)

Theorem divF_terminates :
  forall (n k : nat) (H : 0 < k),
    {v : nat | exists p : nat, forall n_iter : nat, p < n_iter ->
      forall f : forall n k : nat, 0 < k -> nat,
         iter n_iter divF f n k H = v}.
Proof.
  intros. generalize dependent n.
  apply well_founded_induction_type with lt.
    apply lt_wf.
    intros. case_eq (le_lt_dec k x); intro.
      Focus 2. exists 0. exists 0. intros. destruct n_iter; cbn.
        omega.
        unfold divF. rewrite H1. trivial.
      destruct (H0 (x - k)) as [v Hv].
        omega.
        exists (S v). destruct Hv as [p Hp]. exists (S p). intros.
          destruct (n_iter); cbn.
            omega.
            unfold divF. rewrite H1. f_equal. apply Hp. omega.
Defined.

Definition div (n k : nat) (H : 0 < k) : nat :=
  proj1_sig (divF_terminates n k H).

Theorem div_fix : div = divF div.
Proof.
Admitted.

Lemma div_equation :
  forall (n k : nat) (H : 0 < k),
    div n k H =
    if le_lt_dec k n then S (div (n - k) k H) else 0.
Proof.
Admitted.