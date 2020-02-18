Fixpoint length {A : Type} (l : list A) : nat :=
match l with
    | nil => 0
    | cons h t => 1 + length t
end.

Print list.

(* F X := unit + A * X *)

(*
Fixpoint list_rec'
  {A : Type}
  {X : Type} (n : X) (c : A -> X -> X)
  (l : list A) : X :=

Lemma list_rec' :
  forall (A : Type)
    (X : Type),
    X ->
    (A -> X -> X) ->
      list A -> X.
Proof.
*)

Unset Guard Checking.

Fixpoint wut (n : nat) : False := wut n.

Check wut 5.

Unset Positivity Checking.

Inductive Cantor : Type :=
    | cantor : (Cantor -> Cantor) -> Cantor.