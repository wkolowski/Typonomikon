From stdpp Require Import prelude.

Inductive BHeapF {A : Type} (R : A -> A -> Prop) (X : Type) (Y : A -> X -> Prop) : Type :=
    | E
    | N (v : A) (l r : X) (okl : Y v l) (okr : Y v r).

Arguments E {A R X Y}.
Arguments N {A R X Y} _ _ _ _ _.

Definition OKR
  {A : Type} (R : A -> A -> Prop) (X : Type) (Y : A -> X -> Prop)
  (v : A) (h : BHeapF R X Y) : Prop :=
match h with
    | E => True
    | N hv l _ _ _ => R v hv
end.

Fail Inductive BHeap {A : Type} (R : A -> A -> Prop) : Type :=
    | In : BHeapF R (BHeap R) (OKR R (BHeap R) (fun _ _ => True)) -> BHeap R.

(*
Inductive BHeapF {A : Type} (R : A -> A -> Prop) (X Y Z : Type) : Type :=
    | E
    | N (v : A) (l r : X) (okl : Y) (okr : Z).

Arguments E {A R X Y Z}.
Arguments N {A R X Y Z} _ _ _ _ _.

Definition OKR
  {A : Type} (R : A -> A -> Prop) (X Y Z : Type)
  (v : A) (h : BHeapF R X Y Z) : Prop :=
match h with
    | E => True
    | N hv l _ _ _ => R v hv
end.

Inductive BHeap {A : Type} (R : A -> A -> Prop) : Type :=
    | In : BHeapF R (BHeap R) (OKR R (BHeap R) (forall _ _, True) (forall _ _, True)) (OKR R (BHeap R) (fun _ _ => True)) -> BHeap R.

*)