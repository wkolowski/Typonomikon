(** * H1: Uniwersa - pusty *)

(** Chwilowo nic tu nie ma. *)

(* begin hide *)

Require Import Arith.

Set Universe Polymorphism.

Require Import Bool.

Variables
  (A : Type)
  (eq_dec : A -> A -> bool)
  (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
  (K : forall (x : A) (p : x = x), p = eq_refl).

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
  (f : A -> Type) (x : A) (h : f x -> forall y : A, f y -> bool)
  : forall z : A, f z -> bool.
Proof.
  intros y fy. destruct (eq_dec_spec x y).
    destruct e. exact (negb (h fy x fy)).
    exact true.
Defined.

Theorem A_not_Type : ~ @eq Type A Type.
Proof.
  intro p.
  pose (f := idtoeqv p); pose (idtoeqv_sur _ _ p);
  change (idtoeqv p) with f in e; clearbody f e.
  pose (H := forall x : A, f x -> bool).
  destruct (e H) as [x q].
  pose (h := idtoeqv q); pose (e' := idtoeqv_sur _ _ q);
  change (idtoeqv q) with h in e'; clearbody h e'.
  destruct (e' (wut f x h)) as [fx r]; unfold wut in r.
  apply (@f_equal _ _ (fun f => f x fx)) in r.
  destruct (eq_dec_spec x x) as [s | s].
    rewrite (K _ s) in r. destruct (h fx x fx); inversion r.
    contradiction.
Qed.

(* end hide *)