Inductive BTree (A : Type) : Type :=
    | empty : BTree A
    | node : A -> BTree A -> BTree A -> BTree A.

Arguments empty {A}.
Arguments node {A} _ _ _.

Parameter elem : forall A : Type, A -> BTree A -> Prop.

Parameter isHeap {A : LinDec} : BTree A -> Prop.

Parameter singleton : forall Type, A -> BTree A.

Parameter elem_decb :
  {A : LinDec} (x : A) (t : BTree A) : bool.

Parameter root {A : Type} (bt : BTree A) : option A.

Parameter isEmpty {A : Type} (t : BTree A) : bool.

Parameter BTree_toList {A : Type} (t : BTree A) : list A.

Parameter BTree_toList'_aux
  {A : LinDec} (t : BTree A) (acc : list A) : list A.

Parameter BTree_toList' {A : LinDec} (t : BTree A) : list A.

Parameter size {A : Type} (bt : BTree A) : nat.

Parameter count_BTree {A : LinDec} (x : A) (t : BTree A) : nat.

Parameter mirror {A : Type} (t : BTree A) : BTree A.

Parameter complete {A : Type} (n : nat) (x : A) : BTree A.

Parameter pow2 (n : nat) : nat.

Parameter takeWhile {A : Type} (p : A -> bool) (t : BTree A) : BTree A.

Parameter inorder {A : Type} (t : BTree A) : list A.

Parameter preorder {A : Type} (t : BTree A) : list A.

Parameter postorder {A : Type} (t : BTree A) : list A.

Parameter leaf {A : Type} (x : A) : BTree A.

Parameter wut {A : Type} (t : BTree A) : nat.

Parameter sumOfWuts {A : Type} (l : list (BTree A)) : nat.

Parameter bfs_aux
  {A : Type} (ts : list (BTree A)) (acc : list A) {measure sumOfWuts ts}
  : list A.

Parameter bfs {A : Type} (t : BTree A) : list A.


Parameter sumOfSizes {A : Type} (l : list (BTree A)) : nat.

Parameter intersperse {A : Type} (x : A) (t : BTree A) : BTree A.

Parameter height {A : Type} (t : BTree A) : nat.

Parameter zipWith
  {A B C : Type} (f : A -> B -> C)
  (ta : BTree A) (tb : BTree B) : BTree C.

Parameter find {A : Type} (p : A -> bool) (t : BTree A) : option A.

Parameter Any {A : Type} (P : A -> Prop) : BTree A -> Prop.

Parameter Dup {A : Type} : BTree A -> Prop.

Parameter Exactly {A : Type} (P : A -> Prop) : nat -> BTree A -> Prop.

Parameter count {A : Type} (p : A -> bool) (t : BTree A) : nat.

Parameter All {A : Type} (P : A -> Prop) : BTree A -> Prop.

Parameter SameStructure {A B : Type} : BTree A -> BTree B -> Prop.

Parameter subtree {A : Type} : BTree A -> BTree A -> Prop.