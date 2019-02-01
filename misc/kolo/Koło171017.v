Record rat : Set :=
{
    top : nat;
    bottom : nat;
    bottom_not_0 : bottom <> 0
}.

Class Equivalence {A : Type} (R : A -> A -> Prop) : Type :=
{
    reflexive : forall x : A, R x x;
    symmetry : forall x y : A, R x y -> R y x;
    transitive : forall x y z : A, R x y -> R y z -> R x z
}.

Instance Equivalence_eq (A : Type) : Equivalence (@eq A).
Proof.
  split.
    trivial.
    intros. rewrite H. trivial.
    intros. rewrite H, H0. trivial.
Qed.

Definition equiv_ex_rel (p1 p2 : nat * nat) : Prop :=
    fst p1 + snd p1 = fst p2 + snd p2.

Instance Equivalence_ex1 : Equivalence equiv_ex_rel.
Abort.

Definition equiv_kernel {A B : Type} (f : A -> B) : A -> A -> Prop :=
    fun x x' : A => f x = f x'.

Instance Equiv_kernel {A B : Type} {f : A -> B} : Equivalence (equiv_kernel f).
Abort.

Class Pos : Type :=
{
    carrier : Type;
    leq : carrier -> carrier -> Prop;
    pos_refl : forall x : carrier, leq x x;
    pos_sym : forall x y : carrier, leq y x;
    pos_trans : forall x y z : carrier, leq x y -> leq y z -> leq x z
}.

Check @carrier.

Coercion carrier : Pos >-> Sortclass.
(*Coercion leq : Pos >-> Funclass.*)

Theorem pos_leq_refl : forall (P : Pos) (x : P), leq x x.
Proof.
  intros. apply pos_refl.
Qed.

Class Lin : Type :=
{
    pos : Pos;
    total : forall x y : pos, leq x y \/ leq y x
}.

Coercion pos : Lin >-> Pos.

(* Predykaty induktywne *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

Theorem zero_is_even : even 0.
Proof.
  exact even0.
Restart.
  apply even0.
Qed.

Theorem two_is_even : even 2.
Proof.
  apply evenSS. constructor.
Qed.

Theorem satan_is_even : even 666.
Proof.
  repeat constructor.
Qed.

Print satan_is_even.

Theorem one_is_not_even : ~ even 1.
Proof.
  unfold not. intro. inversion H.
Qed.

(*Theorem satans_neighbour_not_even : ~ even 667.
  unfold not. intro.
  Time repeat (inversion H; clear H H0; rename H1 into H; try (clear n0)).
Qed.*)

Check even_ind.

Require Import Arith.

SearchAbout plus.

SearchPattern (_ + 0 = _).

Theorem even_is_2k : forall n : nat, even n -> exists k : nat, n = 2 * k.
Abort.


























Require Import Arith.

Theorem even_double : forall n : nat, even n -> even (2 * n).
Proof.
  induction 1; simpl.
    constructor.
    rewrite <- plus_n_O. rewrite plus_comm.
      replace (S (S n) + n) with (S (S (n + n))); auto.
      constructor. constructor. simpl in *.
      replace (n + 0) with n in IHeven; auto.
(*Restart.
  induction n as [| n']; simpl in *; intro.
    trivial.
    rewrite <- plus_n_O in *. rewrite plus_comm. simpl. constructor.
      apply IHn'. assumption.*)
Defined.

Theorem even_sum : forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction 1; simpl; intro.
    trivial.
    constructor. apply IHeven. assumption.
Defined.

Theorem even_is_double : forall n : nat,
    even n -> exists k : nat, n = 2 * k.
Proof.
  induction 1.
    exists 0. trivial.
    destruct IHeven. exists (S x). simpl in *. rewrite <- plus_n_O in *.
      rewrite plus_comm. simpl. do 2 f_equal. assumption.
Defined.

Theorem double_is_even : forall n : nat, even (2 * n).
Proof.
  induction n as [| n']; simpl in *.
    constructor.
    rewrite <- plus_n_O in *. rewrite plus_comm. simpl.
      constructor. assumption.
Defined.
