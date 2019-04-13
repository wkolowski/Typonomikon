Set Universe Polymorphism.

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

Require Import Arith.

Axiom K_nat : forall (n : nat) (p : n = n), p = eq_refl.

Theorem nat_not_Type : ~ @eq Type nat Type.
Proof.
  intro p.
  pose (f := idtoeqv p); pose (idtoeqv_sur _ _ p);
  change (idtoeqv p) with f in e; clearbody f e.
  pose (A := forall n : nat, f n -> bool).
  destruct (e A) as [n q].
  pose (h := idtoeqv q); pose (e' := idtoeqv_sur _ _ q);
  change (idtoeqv q) with h in e'; clearbody h e'.
  Set Nested Proofs Allowed.
  Definition wut
    (f : nat -> Type) (n : nat) (h : f n -> forall n : nat, f n -> bool)
    : forall k : nat, f k -> bool.
  Proof.
    intros k x. destruct (Nat.eqb_spec n k).
      destruct e. exact (negb (h x n x)).
      exact true.
  Defined.
  destruct (e' (wut f n h)) as [x r]; unfold wut in r.
  apply (@f_equal _ _ (fun f => f n x)) in r.
  destruct (Nat.eqb_spec n n) as [s | s].
    rewrite (K_nat _ s) in r. destruct (h x n x); inversion r.
    contradiction.
Qed.