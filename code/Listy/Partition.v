Require Import D5.

(** * Partycje listy *)

Module Partition.

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

End Partition.

Module OPartition.

Record OPartition
  {A : Type} (ll : list (list A)) (l : list A) : Prop :=
{
    nonempty : forall l' : list A, elem l' ll -> l' <> [];
    all : join ll = l;
}.

Lemma OPartition_app :
  forall {A : Type} (ll1 ll2 : list (list A)) (l1 l2 : list A),
    OPartition ll1 l1 -> OPartition ll2 l2 ->
      OPartition (ll1 ++ ll2) (l1 ++ l2).
Proof.
  

Abort.

End OPartition.

Module IPartition.

Inductive IPartition {A : Type} : list (list A) -> list A -> Prop :=
    | IP_nil : IPartition [[]] []
    | IP_cons :
        forall (ll : list (list A)) (l1 l2 : list A),
          l1 <> [] -> IPartition ll l2 ->
            IPartition (l1 :: ll) (l1 ++ l2).

(*
Lemma OPartition_app :
  forall {A : Type} (ll1 ll2 : list (list A)) (l1 l2 : list A),
    OPartition ll1 l1 -> OPartition ll2 l2 ->
      OPartition (ll1 ++ ll2) (l1 ++ l2).
Proof.
*)

End IPartition.