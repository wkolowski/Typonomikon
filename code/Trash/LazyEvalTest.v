Require Import List.
Import ListNotations.

Fixpoint to0 (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: to0 n'
end.

Inductive llist (A : Type) : Type :=
    | lnil : llist A
    | lcons : A -> (unit -> llist A) -> llist A.

Arguments lnil {A}.
Arguments lcons {A} _ _.

Fixpoint lazy_to0 (n : nat) : llist nat :=
match n with
    | 0 => lcons 0 (fun _ => lnil)
    | S n' => lcons n (fun _ => lazy_to0 n')
end.

Definition lhead {A : Type} (l : llist A) : option A :=
match l with
    | lnil => None
    | lcons h _ => Some h
end.

Fixpoint lapp {A : Type} (l1 l2 : llist A) : llist A :=
match l1 with
    | lnil => l2
    | lcons h t => lcons h (fun _ => lapp (t tt) l2)
end.

Infix "+++" := lapp (at level 50).

(** Commented out for build purposes. *)

Definition sl := to0 3000.
Definition ll := lazy_to0 3000.

(* Fail Time Eval cbv in head
  ((((((sl ++ sl) ++ sl) ++ sl) ++ sl) ++ sl) ++ sl). *)
(* Time Eval cbv in head
  (sl ++ sl ++ sl ++ sl ++ sl ++ sl ++ sl). *)
(* Time Eval cbv in lhead
  ((((((ll +++ ll) +++ ll) +++ ll) +++ ll) +++ ll) +++ ll). *)

(* Time Eval cbn in head
  ((((((sl ++ sl) ++ sl) ++ sl) ++ sl) ++ sl) ++ sl). *)
(* Time Eval cbn in head
  (sl ++ sl ++ sl ++ sl ++ sl ++ sl ++ sl). *)
(* Time Eval cbn in lhead
  ((((((ll +++ ll) +++ ll) +++ ll) +++ ll) +++ ll) +++ ll). *)

Require Import Arith.

Fixpoint ins (n : nat) (l : list nat) : list nat :=
match l with
    | [] => [n]
    | h :: t =>
        if leb n h
        then n :: l
        else h :: ins n t
end.

Fixpoint insertionSort (l : list nat) : list nat :=
match l with
    | [] => []
    | h :: t => ins h (insertionSort t)
end.

Fixpoint take (n : nat) {A : Type} (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

Fixpoint lins (n : nat) (l : llist nat) : llist nat :=
match l with
    | lnil => lcons n (fun _ => lnil)
    | lcons h t =>
        if leb n h
        then lcons n (fun _ => l)
        else lcons h (fun _ => lins n (t tt))
end.

Fixpoint lazyInsertionSort (l : llist nat) : llist nat :=
match l with
    | lnil => lnil
    | lcons h t => lins h (lazyInsertionSort (t tt))
end.

Fixpoint ltake (n : nat) {A : Type} (l : llist A) : llist A :=
match n, l with
    | 0, _ => lnil
    | _, lnil => lnil
    | S n', lcons h t => lcons h (fun _ => ltake n' (t tt))
end.

Fixpoint ltake' (n : nat) {A : Type} (l : llist A) : list A :=
match n, l with
    | 0, _ => []
    | _, lnil => []
    | S n', lcons h t => h :: ltake' n' (t tt)
end.

(*
Time Eval cbv in take 3 (insertionSort (to0 300)).
Time Eval cbv in ltake 3 (lazyInsertionSort (lazy_to0 300)).
Time Eval cbv in ltake' 3 (lazyInsertionSort (lazy_to0 300)).
*)