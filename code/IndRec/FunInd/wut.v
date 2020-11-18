Require Import List Recdef.
Import ListNotations.

Function take {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

Lemma take_ind' :
  forall {A : Type} (P : nat -> list A -> list A -> Type),
    (forall l : list A, P 0 l []) ->
    (forall n : nat, P n [] [])   ->
    (forall (n' : nat) (h : A) (t : list A),
      P n' t (take n' t) ->
        P (S n') (h :: t) (take (S n') (h :: t))) ->
    forall (n : nat) (l : list A), P n l (take n l).
Proof.
  intros.
  functional induction (take n l).
    apply X.
    apply X0.
    apply X1. assumption.
Defined.

Lemma take_nil_r :
  forall {A : Type} (n : nat),
    take n (@nil A) = [].
Proof.
  intros. remember [] as l. revert Heql.
  functional induction take n l;
  intros; congruence.
Qed.

Lemma take_take :
  forall {A : Type} (n m : nat) (l : list A),
    take m (take n l) = take (min n m) l.
Proof.
  intros. revert m.
  functional induction (take n l); cbn; intros.
    destruct m; reflexivity.
    rewrite 2!take_nil_r. reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      f_equal. apply IHl0.
Qed.