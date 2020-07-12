Require Import D5.

Class Finite (A : Type) : Type :=
{
    elems : list A;
    elems_all : forall x : A, elem x elems;
    elems_NoDup : ~ Dup elems;
}.

#[refine]
Instance Finite_unit : Finite unit :=
{|
    elems := [tt];
|}.
Proof.
  destruct x. constructor.
  intro H. inv H; inv H1.
Defined.

#[refine]
Instance Finite_bool : Finite bool :=
{|
    elems := [false; true];
|}.
Proof.
  destruct x; repeat constructor.
  intro H. inv H.
    inv H1. inv H2.
    inv H1; inv H0.
Defined.

#[refine]
Instance Finite_option
  {A : Type} (FA : Finite A) : Finite (option A) :=
{|
    elems := None :: map Some (@elems _ FA);
|}.
Proof.
  all: destruct FA as [els H1 H2].
    destruct x as [a |].
      constructor. apply elem_map. apply H1.
      constructor.
    intro. inv H.
      apply elem_map_conv in H3. inv H3. inv H. inv H0.
      apply Dup_map_conv in H3.
        contradiction.
        intros. inv H. reflexivity.
Defined.

Fixpoint sum (l : list nat) : nat :=
match l with
    | [] => 0
    | h :: t => h + sum t
end.

Lemma elem_sum :
  forall {n : nat} {l : list nat},
    elem n l -> n <= sum l.
Proof.
  induction 1; cbn; lia.
Qed.

Lemma nat_not_Finite :
  Finite nat -> False.
Proof.
  intros [els H1 H2].
  specialize (H1 (S (sum els))).
  apply elem_sum in H1.
  lia.
Qed.

Lemma join_elem_length :
  forall {A : Type} {l : list A} {ll : list (list A)},
    elem l ll -> length l <= length (join ll).
Proof.
  induction 1; cbn;
  rewrite length_app;
  lia.
Qed.

Lemma list_not_Finite :
  forall A : Type,
    Finite (list A) -> A -> False.
Proof.
  destruct 1 as [els H1 H2].
  intro x.
  specialize (H1 (x :: join els)).
  apply join_elem_length in H1; cbn in H1.
  lia.
Qed.

Lemma bool_not_isProp :
  ~ forall b1 b2 : bool, b1 = b2.
Proof.
  intro. specialize (H true false). congruence.
Qed.

Lemma unit_not_bool : unit <> bool.
Proof.
  intro.
  apply bool_not_isProp.
  destruct H, b1, b2.
  reflexivity.
Qed.