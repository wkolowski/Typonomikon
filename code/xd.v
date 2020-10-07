Require Import Recdef Wellfounded Arith Lia.

(** Zainspirowane przez pracę
    https://www-sop.inria.fr/lemme/Venanzio.Capretta/publications/imp.pdf

    Niestety chyba jednak w pizdu nie działa, a szkoda. *)

Fixpoint iter {A : Type} (f : A -> A) (n : nat) (a : A) : A :=
match n with
    | 0 => a
    | S n' => iter f n' (f a)
end.

Inductive fG : nat -> nat -> Prop :=
    | fG_gt100 :
        forall n : nat, 100 < n -> fG n (n - 10)
    | fG_le100 :
        forall n r1 r2 : nat,
          n <= 100 -> fG (n + 11) r1 -> fG r1 r2 -> fG n r2.

Definition F (f : nat -> nat) (n : nat) : nat :=
  if 100 <? n then n - 10 else f (f (11 + n)).

Definition Steps := nat.

Inductive fAcc : nat -> Steps -> (nat -> nat) -> Type :=
    | fAcc_gt100 :
        forall (n : nat) (k : Steps) (f : nat -> nat),
          100 < n ->
            fAcc n (S k) f
    | fAcc_le100 :
        forall (n : nat) (k1 k2 : Steps) (f : nat -> nat),
          n <= 100 ->
          fAcc (11 + n) k1 f ->
          fAcc (iter F k1 f (11 + n)) k2 f ->
            fAcc n (S (k1 + k2)) f.

Definition fDom (n : nat) : Type :=
  {k : Steps & (*forall f : nat -> nat,*) fAcc n k id}.

Definition f' {n : nat} (d : fDom n) : nat :=
match d with
    | existT _ k _ => iter F k id n
end.

Compute iter F 12 id 87.

Unset Guard Checking.
Lemma fDom_all :
  forall n : nat, fDom n.
Proof.
  unfold fDom.
  fix IH 1.
  intro.
  destruct (le_gt_dec n 100).
    Focus 2. exists 1. constructor. assumption.
    {
      destruct (IH (11 + n)) as [k1 h1].
      destruct (IH (iter F k1 id (11 + n))) as [k2 h2].
      exists (S (k1 + k2)).
      constructor 2.
        assumption.
        apply h1.
        apply h2.
    }
Defined.
Unset Guard Checking.

Definition f (n : nat) : nat :=
  f' (fDom_all n).

Compute f 50.

Lemma fDom_all' :
  forall n : nat, fDom n.
Proof.
  apply (@well_founded_induction_type _ (fun n m => 101 - n < 101 - m)).
    apply wf_inverse_image. apply lt_wf.
    intros n IH. destruct (le_lt_dec n 100).
      Focus 2. exists 1. constructor. assumption.
(*
      {
        destruct (IH (11 + n) ltac:(lia)) as [k1 h1].
        edestruct (IH (iter F k1 id (11 + n))) as [k2 h2].
          Focus 2. red. exists (S (k1 + k2)). constructor 2; assumption.
          cbn.
      }
*)
Abort.