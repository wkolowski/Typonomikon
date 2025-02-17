Require Import Recdef.

Axiom wut : False.

Unset Guard Checking.
Function f (n : nat) {measure id n} : nat := f (S n).
Proof.
Admitted.
Fixpoint g (n : nat) : nat := g (S n).
(*
  destruct wut.
Defined.
*)
Compute f 15.
(* Does not terminate. *)
Fail Timeout 1 Compute g 15.