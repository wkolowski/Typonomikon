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