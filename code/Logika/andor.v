Inductive andor (P Q : Prop) : Prop :=
    | left  : P ->      andor P Q
    | right :      Q -> andor P Q
    | both  : P -> Q -> andor P Q.

Lemma and_or_l :
  forall P Q : Prop, P /\ Q -> P \/ Q.
Proof.
  destruct 1 as [p q]. left. assumption.
Qed.

Lemma and_or_r :
  forall P Q : Prop, P /\ Q -> P \/ Q.
Proof.
  destruct 1 as [p q]. right. assumption.
Qed.

Lemma andor_or :
  forall P Q : Prop, andor P Q <-> P \/ Q.
Proof.
  split.
    destruct 1 as [p | q | p q].
      left. assumption.
      right. assumption.
      left. assumption.
    destruct 1 as [p | q].
      apply left. assumption.
      apply right. assumption.
Qed.