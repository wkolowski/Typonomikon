Require Import List.
Import ListNotations.

Inductive Code : Type :=
  | Last : Type -> Type -> Code
  | Cons : Type -> Code -> Code.

Fixpoint funType (c : Code) : Type :=
match c with
    | Last A B => A -> B
    | Cons A c' => A -> funType c'
end.

Fixpoint listType (c : Code) : Type :=
match c with
    | Last A B => list A -> list B
    | Cons A c' => list A -> listType c'
end.

Fixpoint NIL (c : Code) : listType c :=
match c with
    | Last A B => fun _ : list A => []
    | Cons A c' => fun _ : list A => NIL c'
end.

(*
Fixpoint CONS (c : Code) : listType c :=
match c with
    | 
*)

Fixpoint zipWith (c : Code) (f : funType c) {struct c} : listType c.
Proof.
  destruct c as [A B | A c']; cbn in *.
    exact (map f).
    induction 1 as [| h t].
      exact (NIL c').
      specialize (f h). specialize (zipWith _ f). exact zipWith.
Defined.

Compute
  zipWith (Cons nat (Cons nat (Last nat nat))) (fun a b c => a + b + c)
  [1; 2; 3] [4; 5; 6] [7; 8; 9].