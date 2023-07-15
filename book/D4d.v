(** * D4d: Rekursja ogonowa [TODO] *)

Require Import PeanoNat Nat.

From Typonomikon Require Import D5a.

(** * Rekursja ogonowa (TODO) *)

(** * Liczby Fibonacciego (TODO) *)

Module Fib.

Fixpoint fib (n : nat) : nat :=
match n with
| 0 => 0
| 1 => 1
| S (S n' as n'') => fib n'' + fib n'
end.

Fixpoint fib_tailrec_aux (n : nat) (a b : nat) : nat :=
match n with
| 0 => a
| S n' => fib_tailrec_aux n' b (a + b)
end.

Lemma fib_tailrec_aux_S :
  forall n a b : nat,
    fib_tailrec_aux (S n) a b = fib_tailrec_aux n b (a + b).
(* begin hide *)
Proof.
  easy.
Qed.
(* end hide *)

Compute fib_tailrec_aux 7 1 2.

Lemma fib_SS :
  forall n : nat,
    fib (S (S n)) = fib (S n) + fib n.
(* begin hide *)
Proof.
  easy.
Qed.
(* end hide *)

Definition fib_tailrec (n : nat) := fib_tailrec_aux n 0 1.

Lemma fib_tailrec_aux_spec :
  forall n k : nat,
    fib_tailrec_aux k (fib n) (fib (1 + n)) = fib (k + n).
(* begin hide *)
Proof.
  intros n k; revert n.
  induction k as [| k']; intros; [easy |].
  rewrite fib_tailrec_aux_S.
  rewrite (PeanoNat.Nat.add_comm (fib n)).
  rewrite <- fib_SS.
  rewrite IHk'.
  f_equal.
  rewrite <- !plus_n_Sm; cbn.
  easy.
Qed.
(* end hide *)

Lemma fib_tailrec_spec :
  forall n : nat, fib_tailrec n = fib n.
(* begin hide *)
Proof.
  destruct n as [| n']; [easy |].
  unfold fib_tailrec.
  change 1 with (fib 1).
  change 0 with (fib 0) at 1.
  rewrite fib_tailrec_aux_spec.
  f_equal.
  rewrite PeanoNat.Nat.add_0_r; cbn.
  easy.
Qed.
(* end hide *)

End Fib.

(** * Sklejanie list (TODO) *)

Fixpoint app_tailrec_aux {A : Type} (l acc : list A) : list A :=
match l with
| [] => acc
| h :: t => app_tailrec_aux t (h :: acc)
end.

Definition app' {A : Type} (l1 l2 : list A) : list A :=
  app_tailrec_aux (app_tailrec_aux l1 []) l2.

Lemma app_tailrec_aux_spec :
  forall (A : Type) (l1 l2 : list A),
    app_tailrec_aux l1 l2 = rev l1 ++ l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros; trivial.
    rewrite IHt, app_snoc_l. reflexivity.
Qed.
(* end hide *)

Lemma app'_spec :
  forall (A : Type) (l1 l2 : list A),
    app' l1 l2 = l1 ++ l2.
(* begin hide *)
Proof.
  unfold app'. intros. rewrite !app_tailrec_aux_spec, app_nil_r, rev_rev. trivial.
Qed.
(* end hide *)

Definition rev' {A : Type} (l : list A) : list A :=
  app_tailrec_aux l [].

Lemma rev'_spec :
  forall {A : Type} (l : list A),
    rev' l = rev l.
(* begin hide *)
Proof.
  intros. unfold rev'.
  rewrite app_tailrec_aux_spec.
  apply app_nil_r.
Qed.
(* end hide *)

