Require Import Arith.
Require Import Omega.

Eval simpl in fix f (n m : nat) : nat :=
    match n with
        | 0 => m
        | _ => match m with
            | 0 => n
            | S m' => f n m'
        end
    end.

(* Impossible without well founded recursion.
Fixpoint nat_ind_l (k : nat) (knot0 : k <> 0) (P : nat -> Prop)
    (Hbase : forall k' : nat, k' <= k -> P k')
    (Hstep : forall n : nat, P n -> P (k + n))
    (n : nat) : P n.
Proof.
  destruct (le_dec n k).
    apply Hbase. assumption.
    replace n with (k + (n - k)).
      apply Hstep. apply (nat_ind_l k knot0 P Hbase Hstep (n - k)).
      omega.
Defined. *)