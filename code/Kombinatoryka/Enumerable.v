Require Import Lia Arith.

Require Import D5.

Class Enumerable (A : Type) : Type :=
{
    size : A -> nat;
    enum : nat -> list A;
    enum_spec : forall (n : nat) (x : A), size x = n <-> In x (enum n)
}.

Arguments size {A Enumerable}.
Arguments enum _ {Enumerable} _.

#[refine]
Instance Enumerable_bool : Enumerable bool :=
{
    size b := 1;
    enum n :=
    match n with
        | 0 => []
        | 1 => [false; true]
        | _ => []
    end
}.
Proof.
  destruct n as [| [| n']], x; compute; repeat split; auto; lia.
Defined.

Definition flip
  {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
    fun b a => f a b.

Fixpoint all_lists {A : Type} (E : Enumerable A) (n : nat)
  : list (list A) :=
match n with
    | 0 => [[]]
    | 1 => map (fun x => [x]) (enum A 1)
    | S n' =>
        flip bind (enum A 1) (fun h =>
        flip bind (all_lists E n') (fun t => [h :: t]))
end.

Compute all_lists (Enumerable_bool) 3.

#[refine]
Instance Enumerable_list {A : Type} (FA : Enumerable A)
  : Enumerable (list A) :=
{
    size := @length A;
    enum := all_lists FA
}.
Proof.
  induction n as [| n']; cbn.
    destruct x; cbn; split; auto.
      inversion 1.
      destruct 1; inversion H.
    destruct x; cbn.
      split.
        inversion 1.
        admit.
      split.
        inversion 1; subst. destruct x as [| h t]; cbn in *.
          destruct (IHn' []). destruct (H0 eq_refl).
Abort.