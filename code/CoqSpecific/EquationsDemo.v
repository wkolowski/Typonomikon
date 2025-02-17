(*
From Equations Require Import Equations.

Require Import List.
Import ListNotations.

Equations filter {A} (p : A -> bool) : list A -> list A :=
| p, [] => []
| p, h :: t with p h =>
  | true  => h :: filter p t
  | false => filter p t.

(* Fixpoint filter {A : Type} (p : A -> bool) (l : list A) : list A :=
match l with
| [] => []
| h :: t => if p h then h :: filter p t else filter p t
end. *)
*)