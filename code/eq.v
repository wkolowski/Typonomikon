Require Import Recdef.

Inductive T : Type :=
| C1 (n : nat)
| C2
| C3.

Function wut (t : T) : nat :=
match t with
| C1 0 => 1
| _ => 0
end.

(*
Search "wut".

Require Import Equations.
*)