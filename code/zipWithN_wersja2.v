Require Import List.
Import ListNotations.

Inductive Code : Type :=
  | Singl : Type -> Code
  | Cons : Type -> Code -> Code.

Fixpoint listType (c : Code) (R : Type) : Type :=
match c with
    | Singl A => list A -> R
    | Cons A c' => list A -> listType c' R
end.

Fixpoint prods (c : Code) : Type :=
match c with
    | Singl A => list A
    | Cons A c' => list A * prods c'
end.

Fixpoint zip2 {A B : Type} (l : list A) (r : list B) : list (A * B) :=
match l, r with
  | [], _ => []
  | _, [] => []
  | hl :: tl, hr :: tr => (hl, hr) :: zip2 tl tr
end.

Fixpoint prod (c : Code) : Type :=
match c with
  | Singl A => A
  | Cons A c' => A * prod c'
end.

Fixpoint zip (c : Code) : prods c -> list (prod c) :=
match c with
  | Singl A => fun x => x
  | Cons A c' => fun x => let (l, y) := x in zip2 l (zip _ y)
end.

Compute
  zip
    (Cons bool (Singl nat))
    ([true; false], [4; 5]).

Fixpoint funType (c : Code) (R : Type) : Type :=
match c with
    | Singl A => A -> R
    | Cons A c' => A -> funType c' R
end.

Fixpoint uncurry
  (c : Code) : forall R : Type, funType c R -> prod c -> R.
(*
match c with
  | Singl A => fun (R : Type) (f : A -> R) => f
  | Cons A c' => fun R f '(x, p) => uncurry c' R (f x) p
end.
*)
Proof.
  destruct c; cbn in *; intros R f.
    exact f.
    destruct 1 as [t p]. exact (uncurry _ _ (f t) p). Show Proof.
Defined.

Definition zipWith {c : Code} {R : Type} (f : funType c R) : listType c R.
Abort.