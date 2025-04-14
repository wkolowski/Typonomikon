Definition id {A} (x : A) : A := x.

Definition comp {A B C} (f : A -> B) (g : B -> C) : A -> C :=
  fun a => g (f a).

Fixpoint funpow {A} (f : A -> A) (n : nat) : A -> A :=
match n with
| 0 => id
| S n' => comp f (funpow f n')
end.

Require Import Recdef.

(* Type error. *)
Fail Function weirdest_zero (n : nat) : nat :=
  funpow weirdest_zero n 0.

(*
Unset Guard Checking.
Fixpoint weirdest_zero (n : nat) : nat :=
  funpow weirdest_zero n 0.
Set Guard Checking.
*)
