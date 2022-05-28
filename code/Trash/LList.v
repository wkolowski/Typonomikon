Require Export CoqAlgs.Base.

Require Export CoqMTL.Control.Applicative.
Require Export CoqMTL.Control.Monad.Lazy.

Notation "'delay' x" := (fun _ : unit => x) (at level 50, only parsing).
Notation "'delay' $ x" := (fun _ : unit => x) (at level 50, only parsing).

Inductive llist (A : Type) : Type :=
    | lnil : llist A
    | lcons : A -> Lazy (llist A) -> llist A.

Arguments lnil {A}.
Arguments lcons {A} _ _.

Notation "[[ ]]" := lnil.
Notation "[[ x ]]" := (lcons x (delay lnil)).

Notation "[[ x ; y ; .. ; z ]]" :=
  (lcons x (delay $ lcons y .. (delay $ lcons z (delay lnil)) ..)).

Definition lhead {A : Type} (l : llist A) : option A :=
match l with
    | lnil => None
    | lcons h _ => Some h
end.

Definition ltail {A : Type} (l : llist A) : option (llist A) :=
match l with
    | lnil => None
    | lcons _ t => Some (force t)
end.

Fixpoint lapp {A : Type} (l1 l2 : llist A) : llist A :=
match l1 with
    | lnil => l2
    | lcons h t => lcons h $ delay $ lapp (force t) l2
end.

Infix "+++" := lapp (at level 50).

Fixpoint ltake {A : Type} (n : nat) (l : llist A) : llist A :=
match n, l with
    | 0, _ => lnil
    | _, lnil => lnil
    | S n', lcons h t => lcons h $ delay $ ltake n' (force t)
end.

Fixpoint ldrop {A : Type} (n : nat) (l : llist A) : llist A :=
match n, l with
    | 0, _ => l
    | _, lnil => l
    | S n', lcons h t => ldrop n' (force t)
end.

Definition ldrop' {A : Type} (n : nat) (l : llist A) : llist A :=
  let f :=
    fix f (n : nat) (l : llist A) : llist A :=
    match n, l with
        | 0, _ => l
        | _, lnil => l
        | S n', lcons h t => f n' (force t)
    end
  in f n l.

(** Ex. 4.1 *)
Lemma Ex_4_1 :
  forall (A : Type) (n : nat) (l : llist A),
    ldrop n l = ldrop' n l.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn'. unfold ldrop'. reflexivity.
Qed.

(** Ex. 4.2 *)

Require Import List.
Import ListNotations.

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

Fixpoint lazy_to0 (n : nat) : llist nat :=
match n with
    | 0 => lcons 0 $ delay lnil
    | S n' => lcons n $ delay $ lazy_to0 n'
end.

From CoqAlgs Require Import Sorting.InsertionSort.

Fixpoint take (n : nat) {A : Type} (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

Fixpoint to0 (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: to0 n'
end.

Set Warnings "-abstract-large-number".
Definition sl := to0 6000.
Definition ll := lazy_to0 6000.
Set Warnings "abstract-large-number".

(*
Time Eval cbv in head
  ((((((sl ++ sl) ++ sl) ++ sl) ++ sl) ++ sl) ++ sl).

Time Eval cbv in head
  (sl ++ sl ++ sl ++ sl ++ sl ++ sl ++ sl).

Time Eval cbv in lhead
  ((((((ll +++ ll) +++ ll) +++ ll) +++ ll) +++ ll) +++ ll).

Time Eval cbn in head
  ((((((sl ++ sl) ++ sl) ++ sl) ++ sl) ++ sl) ++ sl).

Time Eval cbn in head
  (sl ++ sl ++ sl ++ sl ++ sl ++ sl ++ sl).

Time Eval cbn in lhead
  ((((((ll +++ ll) +++ ll) +++ ll) +++ ll) +++ ll) +++ ll).

Time Eval cbv in take 10 (insertionSort natlt (to0 100)).
Time Eval cbv in ltake 10 (lazyInsertionSort (lazy_to0 100)).

Time Eval cbn in take 10 (insertionSort natlt (to0 100)).
Time Eval cbn in ltake 10 (lazyInsertionSort (lazy_to0 100)).

Time Eval lazy in take 10 (insertionSort natlt (to0 100)).
Time Eval lazy in ltake 10 (lazyInsertionSort (lazy_to0 100)).
*)

Fixpoint lfilter {A : Type} (p : A -> bool) (l : llist A) : llist A :=
match l with
    | lnil => lnil
    | lcons h t =>
        if p h
        then lcons h $ delay $ lfilter p (force t)
        else lfilter p (force t)
end.