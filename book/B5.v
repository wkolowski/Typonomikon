(** * B5: Strzępki logicznych kodów [TODO] *)

(** * [constructive_dilemma] (TODO) *)

Lemma constructive_dilemma :
  forall P Q R S : Prop,
    (P -> R) -> (Q -> S) -> P \/ Q -> R \/ S.
(* begin hide *)
Proof.
  intros P Q R S PR QS H.
  destruct H as [p | q].
    left. apply PR. assumption.
    right. apply QS. assumption.
Qed.
(* end hide *)

Lemma destructive_dilemma :
  forall P Q R S : Prop,
    (P -> R) -> (Q -> S) -> ~ R \/ ~ S -> ~ P \/ ~ Q.
(* begin hide *)
Proof.
  intros P Q R S PR QS H.
  destruct H as [nr | ns].
    left. intro p. apply nr, PR. assumption.
    right. intro q. apply ns, QS. assumption.
Qed.
(* end hide *)

Lemma idempotency_of_entailment :
  forall P Q : Prop,
    (P -> Q) <-> (P -> P -> Q).
(* begin hide *)
Proof.
  split.
    intros pq p1 p2. apply pq. assumption.
    intros ppq p. apply ppq.
      assumption.
      assumption.
Qed.
(* end hide *)



(** * Double negation shift (TODO) *)

(** Wzięte z https://ncatlab.org/nlab/show/double-negation+shift *)

Definition DNS : Prop :=
  forall (A : Type) (P : A -> Prop),
    (forall x : A, ~ ~ P x) -> ~ ~ forall x : A, P x.

Print LEM.

Lemma DNS_not_not_LEM :
  DNS <-> ~ ~ LEM.
(* begin hide *)
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
(* end hide *)