Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Fixpoint iterate
  {A : Type} (f : A -> A) (n : nat) (x : A) : list A :=
match n with
    | 0 => [x]
    | S n' => x :: iterate f n' (f x)
end.

Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
match n with
    | 0 => x
    | S n' => iter f n' (f x)
end.

Parameter isEmpty_iterate :
  forall (A : Type) (f : A -> A) (x : A) (n : nat),
    isEmpty (iterate f n x) = false.

Lemma length_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    length (iterate f n x) = S n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma iterate_plus_S :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    iterate f (S n + m) x =
    iterate f n x ++ iterate f m (iter f (S n) x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite <- IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma iterate_plus :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    iterate f (n + m) x =
    match n with
        | 0 => iterate f m x
        | S n' => iterate f n' x ++ iterate f m (iter f n x)
    end.
(* begin hide *)
Proof.
  destruct n as [| n'].
    cbn. reflexivity.
    intros. rewrite iterate_plus_S. reflexivity.
Qed.
(* end hide *)

Lemma map_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    map f (iterate f n x) = iterate f n (f x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

(* TODO: join, bind, replicate *)

Lemma head_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    head (iterate f n x) = Some x.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma tail_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    tail (iterate f n x) =
    match n with
        | 0 => Some []
        | S n' => Some (iterate f n' (f x))
    end.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma last_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    last (iterate f n x) = Some (iter f n x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    specialize (IHn' (f x)). destruct (iterate f n' (f x)); cbn in *.
      inversion IHn'.
      assumption.
Qed.
(* end hide *)

Lemma init_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    init (iterate f n x) =
    match n with
        | 0 => Some []
        | S n' => Some (iterate f n' x)
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
    take (S m) (iterate f n x) = iterate f (min n m) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite take_nil. cbn. reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite <- IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)