Require Import B3.

(** ** Silna negacja koniunkcji *)

Definition nand' (P Q : Prop) : Prop := ~ P \/ ~ Q.

Lemma nand_nand' :
  forall P Q : Prop,
    nand' P Q -> nand P Q.
(* begin hide *)
Proof.
  unfold nand, nand'.
  intros P Q [np | nq] [p q]; contradiction.
Qed.
(* end hide *)

Lemma nand'_nand_classically :
  (forall P : Prop, P \/ ~ P) ->
    forall P Q : Prop,
      nand P Q -> nand' P Q.
(* begin hide *)
Proof.
  unfold nand, nand'.
  intros lem P Q npq.
  destruct (lem P) as [p | np].
  - right. intros q. apply npq. split; assumption.
  - left. assumption.
Qed.
(* end hide *)

Lemma nand'_nand_tabu :
  (forall P Q : Prop, nand P Q -> nand' P Q)
    ->
  (forall P : Prop, P \/ ~ P).
(* begin hide *)
Proof.
  unfold nand, nand'.
  intros nand'_nand P.
Abort.
(* end hide *)