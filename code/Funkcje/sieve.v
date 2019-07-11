(*
Require Import List.
Import ListNotations.

Inductive D' : nat -> nat -> Type :=
    | D'0 : forall n m : nat, n < m -> D' n m
    | D'1 :
        forall n m : nat, m <= n ->
          D' (n - S m) m -> D' n m.

Fixpoint divides' {n m : nat} (d : D' n m) : bool :=
match d with
    | D'0 0 _ _ => true
    | D'0 _ _ _ => false
    | D'1 _ _ _ d' => divides' d'
end.

Lemma D'_all :
  forall n m : nat, D' n m.
Proof.
  apply (
    @well_founded_induction_type nat
      lt PeanoNat.Nat.lt_wf_0
      (fun n : nat => forall m : nat, D' n m)).
  destruct x as [| n'].
Abort.
*)

Require Import D5.

Inductive D {A : Type} (f : A -> A -> bool) : list A -> Type :=
    | D0 : D f []
    | D1 :
        forall (h : A) (t : list A),
          D f (filter (f h) t) -> D f (h :: t).

Arguments D0 {A f}.
Arguments D1 {A f} _ _ _.

Fixpoint sieve'
  {A : Type} (f : A -> A -> bool)
  {l : list A} (d : D f l) : list A :=
match d with
    | D0 => []
    | D1 h t d' => h :: sieve' f d'
end.

Require Import Wellfounded Omega.

Lemma lemma :
  forall A : Type,
    well_founded (fun l1 l2 : list A => length l1 < length l2).
Proof.
  red. induction a as [| h t]; cbn.
    constructor. inversion 1.
    inversion IHt. constructor. destruct y as [| h' t'].
      constructor. inversion 1.
      intro. constructor. intros. apply H. cbn in *. omega.
Defined.

Lemma D_all :
  forall (A : Type) (f : A -> A -> bool) (l : list A), D f l.
Proof.
  intros A f.
  eapply (
    @well_founded_induction_type
      (list A)
      (fun l1 l2 => length l1 < length l2) _ (D f)).
    destruct x as [| h t]; intros IH.
      constructor.
      constructor. apply IH. clear IH. induction t as [| h' t']; cbn.
        constructor.
        destruct (f h h'); cbn in *.
          apply le_n_S. apply IHt'.
          apply le_S. apply IHt'.
    Unshelve. apply lemma.
Defined.

Definition sieve
  {A : Type} (f : A -> A -> bool) (l : list A) : list A :=
    sieve' f (D_all A f l).

Definition divides (n m : nat) : bool :=
  any (fun k : nat => n * k =? m) (iterate S (S m) 0).

Compute iterate S 10 2.

Compute sieve (fun n m => negb (divides n m)) (iterate S 100 2).