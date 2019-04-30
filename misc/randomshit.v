Require Import Arith.

Set Universe Polymorphism.

(** Lemat: aksjomat K dla liczb naturalnych. *)

Fixpoint code (n m : nat) : Type :=
match n, m with
    | 0, 0 => unit
    | S _, 0 => Empty_set
    | 0, S _ => Empty_set
    | S n', S m' => code n' m'
end.

Fixpoint encode_aux (n : nat) : code n n :=
match n with
    | 0 => tt
    | S n' => encode_aux n'
end.

Definition encode {n m : nat} (p : n = m) : code n m :=
match p with
    | eq_refl => encode_aux n
end.

Fixpoint decode {n m : nat} : code n m -> n = m :=
match n, m with
    | 0, 0 => fun _ => eq_refl
    | 0, S _ => fun c => match c with end
    | S _, 0 => fun c => match c with end
    | S n', S m' => fun c => @f_equal _ _ S _ _ (@decode n' m' c)
end.

Lemma decode_encode :
  forall (n m : nat) (p : n = m),
    decode (encode p) = p.
Proof.
  destruct p; cbn.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.

Lemma isProp_code :
  forall (n m : nat) (c1 c2 : code n m), c1 = c2.
Proof.
  induction n as [| n']; destruct m as [| m']; cbn; try destruct c1, c2.
    reflexivity.
    intros. apply IHn'.
Qed.

Lemma encode_decode :
  forall (n m : nat) (c : code n m),
    encode (decode c) = c.
Proof.
  induction n as [| n']; destruct m as [| m']; cbn; try destruct c.
    reflexivity.
    intro. apply isProp_code.
Qed.

Lemma K_nat :
  forall (n : nat) (p : n = n), p = eq_refl.
Proof.
  intros. rewrite <- (decode_encode _ _ p).
  replace (encode p) with (encode_aux n).
    induction n as [| n']; cbn.
      reflexivity.
      rewrite IHn'.
        cbn. reflexivity.
        reflexivity.
    apply isProp_code.
Qed.

Definition idtoeqv {A B : Type} (p : A = B) : A -> B.
Proof.
  destruct p. intro x. exact x.
Defined.

Lemma idtoeqv_sur :
  forall (A B : Type) (p : A = B) (b : B),
    exists a : A, idtoeqv p a = b.
Proof.
  destruct p. intro a. exists a. reflexivity.
Qed.

Definition wut
  (f : nat -> Type) (n : nat) (h : f n -> forall m : nat, f m -> bool)
  : forall k : nat, f k -> bool.
Proof.
  intros k x. destruct (Nat.eqb_spec n k).
    destruct e. exact (negb (h x n x)).
    exact true.
Defined.

Theorem nat_not_Type : ~ @eq Type nat Type.
Proof.
  intro p.
  pose (f := idtoeqv p); pose (idtoeqv_sur _ _ p);
  change (idtoeqv p) with f in e; clearbody f e.
  pose (A := forall n : nat, f n -> bool).
  destruct (e A) as [n q].
  pose (h := idtoeqv q); pose (e' := idtoeqv_sur _ _ q);
  change (idtoeqv q) with h in e'; clearbody h e'.
  destruct (e' (wut f n h)) as [x r]; unfold wut in r.
  apply (@f_equal _ _ (fun f => f n x)) in r.
  destruct (Nat.eqb_spec n n) as [s | s].
    rewrite (K_nat _ s) in r. destruct (h x n x); inversion r.
    contradiction.
Qed.