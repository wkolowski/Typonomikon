Inductive InfTree (B A : Type) : Type :=
    | E : InfTree B A
    | N : A -> (B -> InfTree B A) -> InfTree B A.

Arguments E {B A}.
Arguments N {B A} _ _.

Definition leaf {A : Type} (x : A) : InfTree False A :=
  N x (fun e : False => match e with end).

Definition isEmpty {B A : Type} (t : InfTree B A) : bool :=
match t with
    | E => true
    | _ => false
end.

Definition root {B A : Type} (t : InfTree B A) : option A :=
match t with
    | E => None
    | N x _ => Some x
end.

Definition unN {B A : Type} (t : InfTree B A)
  : option (A * {B : Type & B -> InfTree B A}) :=
match t with
    | E => None
    | N x f => Some (x, @existT Type _ B f)
end.

(** Zagadka, że o ja jebie: udowodnij, że funkcji [size] i [height] nie da
    się zaimplementować. *)

(*
Parameter size : forall A : Type, BTree A -> nat.
Parameter height : forall A : Type, BTree A -> nat.
*)

(*
Parameter leftmost : forall A : Type, BTree A -> option A.
Parameter rightmost : forall A : Type, BTree A -> option A.

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter bfs_aux :
  forall A : Type, list (BTree A) -> list A -> list A.

Parameter bfs : forall A : Type, BTree A -> list A.
*)

(*
Parameter mirror' : forall A : Type, BTree A -> BTree A.
*)

Fixpoint complete {B A : Type} (n : nat) (x : A) : InfTree B A :=
match n with
    | 0 => E
    | S n' => N x (fun _ => complete n' x)
end.

Fixpoint iterate
  {B A : Type} (f : A -> A) (n : nat) (x : A) : InfTree B A :=
match n with
    | 0 => E
    | S n' => N x (fun _ => iterate f n' (f x))
end.

Fixpoint take {B A : Type} (n : nat) (t : InfTree B A) : InfTree B A :=
match n, t with
    | 0, _ => E
    | _, E => E
    | S n', N x f => N x (fun b : B => take n' (f b))
end.

(*
Parameter index : forall A : Type, list bool -> BTree A -> option A.
Parameter nth : forall A : Type, nat -> BTree A -> option A.
*)

(*
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).
*)

Fixpoint intersperse {B A : Type} (v : A) (t : InfTree B A) : InfTree B A :=
match t with
    | E => E
    | N x f => N x (fun _ => N v f)
end.

(*
Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.
*)

(*
Parameter any : forall A : Type, (A -> bool) -> BTree A -> bool.
Parameter all : forall A : Type, (A -> bool) -> BTree A -> bool.
*)

(*
Parameter find : forall A : Type, (A -> bool) -> BTree A -> option A.
Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).
*)

(*
Parameter count : forall A : Type, (A -> bool) -> BTree A -> nat.
*)

(*
Fixpoint takeWhile {A : Type} (p : A -> bool) (t : InfTree A) : InfTree A :=
match t with
    | E => E
    | N x B f => if p x then N x B (fun b : B => takeWhile p (f b)) else E
end.

(*
Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).
*)

Fixpoint map {A B : Type} (f : A -> B) (t : InfTree A) : InfTree B :=
match t with
    | E => E
    | N x C g => N (f x) C (fun c : C => map f (g c))
end.

(*
Fixpoint zipWith
  {A B C : Type} (f : A -> B -> C)
  (t1 : InfTree A) (t2 : InfTree B) : InfTree C :=
match t1, t2 with
    | E, _ => E
    | _, E => E
    | N a D f, N b E g => N (f a b) (fun 
*)

(*
Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.
*)

(** Predykaty *)

Inductive Elem {A : Type} (x : A) : InfTree A -> Prop :=
    | Elem_here :
        forall (B : Type) (f : B -> InfTree A),
          Elem x (N x B f)
    | Elem_there :
        forall (B : Type) (f : B -> InfTree A) (b : B),
          Elem x (f b) -> Elem x (N x B f).

Inductive Exists {A : Type} (P : A -> Prop) : InfTree A -> Prop :=
    | Exists_here :
        forall (x : A) (B : Type) (f : B -> InfTree A),
          P x -> Exists P (N x B f)
    | Exists_there :
        forall (x : A) (B : Type) (f : B -> InfTree A) (b : B),
          Exists P (f b) -> Exists P (N x B f).

Inductive Forall {A : Type} (P : A -> Prop) : InfTree A -> Prop :=
    | Forall_E : Forall P E
    | Forall_N :
        forall (x : A) (B : Type) (f : B -> InfTree A),
          (forall b : B, Forall P (f b)) -> Forall P (N x B f).

(*
Parameter Dup : forall A : Type, BTree A -> Prop.

Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtMost : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
*)

Inductive SameStructure {A B : Type} : InfTree A -> InfTree B -> Prop :=
    | SS_E : SameStructure E E
    | SS_N :
        forall
          (x : A) (y : B) (C : Type)
          (f : C -> InfTree A) (g : C -> InfTree B),
            (forall c : C, SameStructure (f c) (g c)) ->
              SameStructure (N x C f) (N y C g).

(*
Parameter SameStructure : forall A B : Type, BTree A -> BTree B -> Prop.
Parameter SameShape : forall A B : Type, BTree A -> BTree B -> Prop.
*)

Inductive InfTreeDirectSubterm
  {A : Type} : InfTree A -> InfTree A -> Prop :=
    | ITDS_E :
        forall (x : A) (B : Type) (f : B -> InfTree A) (b : B),
          InfTreeDirectSubterm (f b) (N x B f).

Parameter subtree : forall A : Type, BTree A -> BTree A -> Prop.
Parameter Subterm : forall A : Type, BTree A -> BTree A -> Prop.
*)