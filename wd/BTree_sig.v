Inductive BTree (A : Type) : Type :=
    | empty : BTree A
    | node : A -> BTree A -> BTree A -> BTree A.

Arguments empty {A}.
Arguments node {A} _ _ _.

(*Parameter elem : forall A : Type, A -> BTree A -> Prop.

Parameter elem_decb :
  {A : LinDec} (x : A) (t : BTree A) : bool.
Parameter isHeap {A : LinDec} : BTree A -> Prop.*)


(** Basic observers *)
Parameter leaf : forall A : Type, A -> BTree A.

Parameter isEmpty : forall A : Type, BTree A -> bool.

Parameter root : forall A : Type, BTree A -> option A.
Parameter left : forall A : Type, BTree A -> BTree A.
Parameter right : forall A : Type, BTree A -> BTree A.

(* TODO *)
Parameter leftmost : forall A : Type, BTree A -> option A.
Parameter rightmost : forall A : Type, BTree A -> option A.

Parameter size : forall A : Type, BTree A -> nat.

Parameter height : forall A : Type, BTree A -> nat.

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter bfs_aux :
  forall A : Type, list (BTree A) -> list A -> list A.

Parameter bfs : forall A : Type, BTree A -> list A.

(** Basic operations *)
Parameter mirror : forall A : Type, BTree A -> BTree A.

Parameter complete : forall A : Type, nat -> A -> BTree A.

Parameter index : forall A : Type, list bool -> BTree A -> option A.

Parameter take : forall A : Type, nat -> BTree A -> BTree A.
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).

Parameter intersperse : forall A : Type, A -> BTree A -> BTree A.

Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.

(** Operacje z predykatem boolowskim. *)
Parameter any : forall A : Type, (A -> bool) -> BTree A -> bool.
Parameter all : forall A : Type, (A -> bool) -> BTree A -> bool.

Parameter find : forall A : Type, (A -> bool) -> BTree A -> option A.
Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).

Parameter count : forall A : Type, (A -> bool) -> BTree A -> nat.

Parameter takeWhile : forall A : Type, (A -> bool) -> BTree A -> BTree A.

Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).

(** Operacje z funkcją. *)
Parameter map : forall A B : Type, (A -> B) -> BTree A -> BTree B.

Parameter zipWith :
  forall A B C : Type, (A -> B -> C) -> BTree A -> BTree B -> BTree C.

Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.

(** foldy i scany *)

(** Predykaty *)

Parameter Elem : forall A : Type, A -> BTree A -> Prop.

Parameter Any : forall A : Type, (A -> Prop) -> BTree A -> Prop.
Parameter All : forall A : Type, (A -> Prop) -> BTree A -> Prop.

Parameter Dup : forall A : Type, BTree A -> Prop.

Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtMost : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.

Parameter SameStructure : forall A B : Type, BTree A -> BTree B -> Prop.

Parameter subtree : forall A : Type, BTree A -> BTree A -> Prop.