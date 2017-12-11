
Reguły unikalności wyrażają unikalność funkcji, których dziedziną lub
    przeciwdziedziną jest dany typ.

    W tym drugim przypadku 
(** * Klasy *)

(** W językach obiektowych występuje pojęcie interfejsu. Oznacza
    ono pewną abstrakcyjną specyfikację, którą klasa implementująca
    go musi spełnić. Podobny mechanizm istnieje również w Coqu,
    ale tu interfejsy zwą się klasami, co początkowo może być mylące. *)

(** * Setoidy *)

Record Q : Set :=
{
    top : nat;
    bot : nat;
    cond : bot <> 0
}.

Axiom Q_eq : forall q1 q2 : Q,
    top q1 * bot q2 = top q2 * bot q1 -> q1 = q2.

Definition one : Q.
  refine {| top := 1; bot := 1 |}. auto.
Defined.

Definition one' : Q.
  refine {| top := 2; bot := 2 |}. auto.
Defined.

Program Definition one'' : Q := {| top := 1; bot := 1 |}.
Program Definition one''' : Q := {| top := 2; bot := 2 |}.

Definition aux (q : Q) : Prop :=
match q with
    | Build_Q 1 1 _ => True
    | _ => False
end.

Theorem contradiction : False.
Proof.
  replace False with (aux one).
    simpl. trivial.
    replace one with one'.
      simpl. trivial.
      apply Q_eq. simpl. trivial.
Qed.

(** Jednym z zastosowań klas jest konstrukcja struktur matematycznych.
    W językach imperatywnych wykorzystanie interfejsów w podobnym celu
    jest znikome, gdyż myślenie matematyczne nie jest tam rozpowszechnione,
    lecz w Coqu jest ono niezbędne. *)

Class Setoid (A : Type) : Type :=
{
    equiv : A -> A -> Prop;
    equiv_refl : forall x : A, equiv x x;
    equiv_sym : forall x y : A, equiv x y -> equiv y x;
    equiv_trans : forall x y z : A, equiv x y -> equiv y z -> equiv x z
}.

Instance TypeEq : Setoid Type :=
{
    equiv := eq
}.
Proof. auto. auto. intros. subst. auto. Qed.

Instance TypeEq' : Setoid Type.
refine
{|
    equiv := eq
|};
  intros; subst; auto.

Require Import Omega.

Instance QSetoid : Setoid Q :=
{
    equiv := fun q1 q2 : Q => top q1 * bot q2 = top q2 * bot q1
}.
Proof.
  auto.
  auto. intros. assert (top x * bot y * top y * bot z = 
    top y * bot x * top z * bot y). rewrite H.
    rewrite <- mult_assoc. rewrite H0. rewrite mult_assoc. auto.
    Require Import Arith. 
  intros. cut (top y * top x * bot z = top y * top z * bot x).
Abort.

Instance Setoid_kernel (A B : Type) (f : A -> B) : Setoid A :=
{
    equiv := fun x x' : A => f x = f x'
}.
Proof.
  eauto.
  eauto.
  intros. eapply eq_trans; eauto.
Defined.

Instance Setoid_1 : Setoid (nat * nat) :=
{
    equiv := fun p1 p2 : nat * nat => fst p1 + snd p1 = fst p2 + snd p2
}.
Proof.
  reflexivity.
  intros. symmetry. assumption.
  intros. apply eq_trans with (fst y + snd y); assumption.
Restart.
  apply Setoid_kernel with nat. destruct 1. exact (n + n0).
Defined.



