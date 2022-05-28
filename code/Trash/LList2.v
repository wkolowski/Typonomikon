Require Export CoqMTL.Control.Applicative.
Require Export CoqMTL.Control.Monad.Lazy.

Inductive Stream (A : Type) : Type :=
    | mkStream : Lazy (StreamCell A) -> Stream A

with StreamCell (A : Type) : Type :=
    | lnil : StreamCell A
    | lcons : A -> Stream A -> StreamCell A.

Arguments mkStream {A} _.
Arguments lnil {A}.
Arguments lcons {A} _ _.

Scheme Stream_ind_full :=
  Induction for Stream Sort Prop

with StreamCell_ind_full :=
  Induction for StreamCell Sort Prop.

Definition force' {A : Type} (s : Stream A) : StreamCell A :=
match s with
    | mkStream c => force c
end.

Lemma Stream_ind_full' :
  forall (A : Type) (P0 : StreamCell A -> Prop),
    let
      P := fun s => P0 (force' s)
    in
      (forall l : Lazy (StreamCell A), P0 (l tt) -> P (mkStream l)) ->
      P0 lnil ->
      (forall (a : A) (s : Stream A), P s -> P0 (lcons a s)) ->
        forall s : Stream A, P s.
Proof.
  intros.
  induction s using Stream_ind_full with (P0 := P0) (P := P).
    apply H. apply H2.
    apply H0.
    apply H1. assumption.
Qed.

Lemma Stream_ind_listlike :
  forall (A : Type) (P : Stream A -> Prop)
    (Hlnil : P (mkStream (delay lnil)))
    (Hlcons : forall (h : A) (t : Stream A),
        P t ->
          P (mkStream (delay (lcons h t)))),
      forall s : Stream A, P s.
Proof.
  intros A P.
  induction s using Stream_ind_full
  with (P := P) (P0 := fun c => P (mkStream (delay c))).
    replace l with (delay $ force l).
      apply H.
      cbv. ext u. destruct u. reflexivity.
    apply Hlnil.
    apply Hlcons. assumption.
Qed.

Definition lhead {A : Type} (l : Stream A) : option A :=
match force' l with
    | lnil => None
    | lcons h _ => Some h
end.

Definition ltail {A : Type} (l : Stream A) : option (Stream A) :=
match force' l with
    | lnil => None
    | lcons _ t => Some t
end.

Notation "'delay' x" := (fun _ : unit => x) (at level 50, only parsing).
Notation "'delay' $ x" := (fun _ : unit => x) (at level 50, only parsing).

Fixpoint lapp {A : Type} (l1 l2 : Stream A) : Stream A :=
match force' l1 with
    | lnil => l2
    | lcons h t => mkStream $ delay $ lcons h (lapp t l2)
end.

Fixpoint lapp' {A : Type} (l1 l2 : Stream A) : Stream A :=
  mkStream $ delay $
match force' l1 with
    | lnil => force' l2
    | lcons h t => lcons h (lapp' t l2)
end.

Lemma lapp_lapp' :
  forall (A : Type) (l1 l2 : Stream A),
    lapp l1 l2 = lapp' l1 l2.
Proof.
  induction l1 using Stream_ind_listlike; cbn; intros.
    destruct l2. f_equal. ext u. destruct u. compute. reflexivity.
    f_equal. ext u. rewrite IHl1. reflexivity.
Qed.

Infix "+++" := lapp (at level 50).

(*
Fixpoint ltake {A : Type} (n : nat) (l : Stream A) : Stream A :=
match n, l with
    | 0, _ => mkStream (fun _ => lnil)
    | _, mkStream lnil => mkStream lnil
    | S n', mkStream (lcons h t) => lcons h $ delay $ ltake n' (force t)
end.

Fixpoint ldrop {A : Type} (n : nat) (l : Stream A) : Stream A :=
match n, l with
    | 0, _ => l
    | _, lnil => l
    | S n', lcons h t => ldrop n' (force t)
end.

Definition ldrop' {A : Type} (n : nat) (l : Stream A) : Stream A :=
  let f :=
    fix f (n : nat) (l : Stream A) : Stream A :=
    match n, l with
        | 0, _ => l
        | _, lnil => l
        | S n', lcons h t => f n' (force t)
    end
  in f n l.

(** Ex. 4.1 *)
Lemma Ex_4_1 :
  forall (A : Type) (n : nat) (l : Stream A),
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

Fixpoint lins (n : nat) (l : Stream nat) : Stream nat :=
match l with
    | lnil => lcons n (fun _ => lnil)
    | lcons h t =>
        if leb n h
        then lcons n (fun _ => l)
        else lcons h (fun _ => lins n (t tt))
end.

Fixpoint lazyInsertionSort (l : Stream nat) : Stream nat :=
match l with
    | lnil => lnil
    | lcons h t => lins h (lazyInsertionSort (t tt))
end.

Fixpoint lazy_to0 (n : nat) : Stream nat :=
match n with
    | 0 => lcons 0 $ delay lnil
    | S n' => lcons n $ delay $ lazy_to0 n'
end.

(*Fixpoint lazy_to0 (n : nat) : Stream nat :=
match n with
    | 0 => lcons 0 (fun _ => lnil)
    | S n' => lcons n (fun _ => lazy_to0 n')
end.*)

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

Definition sl := to0 30000.
Definition ll := lazy_to0 30000.

Fail
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

Fixpoint lfilter {A : Type} (p : A -> bool) (l : Stream A) : Stream A :=
match l with
    | lnil => lnil
    | lcons h t =>
        if p h
        then lcons h $ delay $ lfilter p (force t)
        else lfilter p (force t)
end.*)