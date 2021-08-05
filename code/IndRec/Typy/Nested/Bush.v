(* Wzięte stąd: https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-hosc09.pdf *)

(*
Inductive BushF (F : Type -> Type) (A : Type) : Type :=
    | LeafF : BushF F A
    | NodeF : A -> F (F A) -> BushF F A.

(* Inductive Bush (A : Type) : Type :=
    | In : BushF Bush A -> Bush A.
 *)

Definition BushC (A : Type) : Type :=
  forall (F : Type -> Type) (leaf : F A) (node : A -> F (F A) -> F A), F A.

Definition mapC {A B : Type} (f : A -> B) (b : BushC A) : BushC B.
unfold BushC in *.
intros F leaf node.
specialize (b F).
*)

Unset Positivity Checking.
Inductive Bush (A : Type) : Type :=
    | Leaf : Bush A
    | Node : A -> Bush (Bush A) -> Bush A.
Set Positivity Checking.

Arguments Leaf {A}.
Arguments Node {A} _ _.

Require Import D5.

Unset Guard Checking.
Fixpoint map {A B : Type} (f : A -> B) (b : Bush A) {struct b} : Bush B :=
match b with
    | Leaf      => Leaf
    | Node v bs => Node (f v) (map (map f) bs)
end.

Fixpoint sum (b : Bush nat) : nat :=
match b with
    | Leaf => 0
    | Node n bs => n + sum (map sum bs)
end.

Fixpoint size {A : Type} (b : Bush A) {struct b} : nat :=
match b with
    | Leaf => 0
    | Node v bs => 1 + sum (map size bs)
end.

Fixpoint toList {A : Type} (b : Bush A) {struct b} : list A :=
match b with
    | Leaf      => []
    | Node v bs => v :: join (toList (map toList bs))
end.

Fixpoint replicate (h : nat) {A : Type} (x : A) : Bush A :=
match h with
    | 0    => Leaf
    | S h' => Node x (replicate h' (replicate h' x))
end.




(* Fixpoint join {A : Type} (b : Bush (Bush A)) {struct b} : Bush A :=
match b with
    | Leaf => Leaf
    | Node v bs => Node (join v) (join (map join bs))
end.
 *)

Compute  (replicate 3 (Node 5 Leaf)).

Set Guard Checking.
