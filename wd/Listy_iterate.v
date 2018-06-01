Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Fixpoint iterate
  {A : Type} (f : A -> A) (x : A) (n : nat) : list A :=
match n with
    | 0 => [x]
    | S n' => x :: iterate f (f x) n'
end.

Parameter isEmpty_iterate :
  forall (A : Type) (f : A -> A) (x : A) (n : nat),
    isEmpty (iterate f x n) = false.

Lemma length_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    length (iterate f x n) = S n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

(* TODO: app, snoc, rev *)

Lemma map_iterate :
  forall (A : Type) (f : A -> A) (x : A) (n : nat),
    map f (iterate f x n) = iterate f (f x) n.
(* begin hide *)
Proof.
  intros A f x n. revert x.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

(* TODO: join, bind, replicate *)

Parameter head_iterate :
  forall (A : Type) (f : A -> A) (x : A) (n : nat),
    head (iterate f x n) = Some x.

Lemma tail_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    tail (iterate f x n) =
    match n with
        | 0 => Some []
        | S n' => Some (iterate f (f x) n')
    end.
(* begin hide *)
Proof.
  destruct n as [| n']; cbn; reflexivity.
Qed.
(* end hide *)

(* TODO: [last] *)

Lemma init_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    init (iterate f x n) =
    match n with
        | 0 => Some []
        | S n' => Some (iterate f x n')
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. destruct n'; cbn; reflexivity.
Qed.
(* end hide *)

Lemma take_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    take (S n) (iterate f x m) = iterate f x (min n m).
(* begin hide *)
Proof.
  intros A f n m. revert n.
  induction m as [| m']; cbn; intros.
    rewrite take_nil. rewrite Min.min_0_r. cbn. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite <- IHm'. cbn. reflexivity.
Qed.
(* end hide *)

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n

Parameter iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f x n