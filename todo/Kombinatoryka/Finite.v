Require Import X3.

Class Finite (A : Type) : Type :=
{
    enumerate : list A;
    spec : forall x : A, elem x enumerate
}.

Arguments enumerate _ [Finite].

Instance Finite_bool : Finite bool :=
{
    enumerate := [false; true]
}.
Proof.
  destruct x; repeat constructor.
Defined.

Instance Finite_option {A : Type} (FA : Finite A) : Finite (option A) :=
{
    enumerate := None :: map (@Some A) (enumerate A)
}.
Proof.
  destruct x.
    right. apply elem_map. apply spec.
    left.
Defined.

Fixpoint sum (l : list nat) : nat :=
match l with
    | [] => 0
    | h :: t => h + sum t
end.

Require Import Omega.

Lemma Finite_nat :
  Finite nat -> False.
Proof.
  intros [l H].
  specialize (H (S (sum l))).
  assert (forall n : nat, elem n l -> n < S (sum l)).
    clear H. induction 1; cbn; omega.
  specialize (H0 _ H). apply Nat.lt_irrefl in H0. assumption.
Qed.

Instance Finite_list_Empty :
  Finite (list Empty_set) :=
{|
    enumerate := [[]];
|}.
Proof.
  destruct x.
    constructor.
    destruct e.
Defined.

Lemma Finite_list :
  forall (A : Type) (x : A),
    Finite (list A) -> False.
Proof.
  intros A x [l H].
  specialize (H (x :: join l)).
  assert (forall l' : list A, elem l' l -> length l' < S (length (join l))).
    clear H. induction 1; cbn; rewrite length_app; omega.
  specialize (H0 _ H). cbn in H0. omega.
Qed.