Require Import D5.

(** * Partycje listy *)

Definition Partition
  {A : Type} (ll : list (list A)) (l : list A) : Prop :=
    Permutation (join ll) l.

Lemma Partition_rev :
  forall {A : Type} (ll : list (list A)) (l : list A),
    Partition ll l -> Partition (rev (map rev ll)) (rev l).
Proof.
  unfold Partition. intros.
  rewrite <- rev_join, !Permutation_rev.
  assumption.
Qed.