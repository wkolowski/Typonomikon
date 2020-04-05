(** * Double negation shift *)

(** Wzięte z https://ncatlab.org/nlab/show/double-negation+shift *)

Require Import W3.

Definition DNS : Prop :=
  forall (A : Type) (P : A -> Prop),
    (forall x : A, ~ ~ P x) -> ~ ~ forall x : A, P x.

Print LEM.

Lemma DNS_not_not_LEM :
  DNS <-> ~ ~ LEM.
Proof.
  unfold DNS, LEM. split.
    intros DNS H.
      specialize (DNS Prop (fun P => P \/ ~ P) LEM_irrefutable).
      apply DNS. intro H'. contradiction.
    intros NNLEM A P H1 H2. apply NNLEM. intro LEM.
      assert (forall x : A, P x).
        intro x. destruct (LEM (P x)).
          assumption.
          specialize (H1 x). contradiction.
        contradiction.
Qed.