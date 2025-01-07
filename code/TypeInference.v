Require Import String.
Check (fun x => x) : string -> string.
(* ===> fun x : ?T => x : ?T -> ?T *)


(*
Definition x : unit :=
  let f := (fun x : _ => x) in.
  (f id) (f tt).
*)

Definition x1 : unit :=
  (id id) (id tt).