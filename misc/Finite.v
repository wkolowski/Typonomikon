Require Import List.
Import ListNotations.

Class Finite (A : Type) : Type :=
{
    enumerate : list A;
    spec : forall x : A, In x enumerate
}.

Arguments Finite _.
Arguments enumerate _ [Finite].

Instance Finite_bool : Finite bool :=
{
    enumerate := [false; true]
}.
Proof.
  destruct x; compute; auto.
Defined.

Instance Finite_option {A : Type} (FA : Finite A) : Finite (option A) :=
{
    enumerate := None :: map (@Some A) (enumerate A)
}.
Proof.
  destruct x.
    right. apply in_map. apply spec.
    left. trivial.
Defined.

Class Enumerable (A : Type) : Type :=
{
    size : A -> nat;
    enum : nat -> list A;
    enum_spec : forall (n : nat) (x : A), size x <= n <-> In x (enum n)
}.

Arguments size [A Enumerable] _.
Arguments enum _ [Enumerable] _.

Instance Enumerable_bool : Enumerable bool :=
{
    size b := 1;
    enum n :=
    match n with
        | 0 => []
        | _ => [false; true]
    end
}.
Proof.
  Require Import Omega.
  destruct n, x; compute; repeat split; auto; omega.
Defined.

Instance all_lists {A : Type} (E: Enumerable A) (n : nat)
  : list (list A) :=
match n with
    | 0 => []
    | S n' => 


Instance Enumerable_list {A : Type} (FA : Enumerable A) : Enumerable (list A) :=
{
    size := @length A
}.