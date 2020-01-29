Lemma DNE_LEM :
  (forall P : Prop, ~ ~ P -> P)
    <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
    intros DNE P. apply DNE. intro nlem. apply nlem. right. intro p.
      apply nlem. left. assumption.
    intros LEM P nnp. destruct (LEM P).
      assumption.
      contradiction.
Qed.

Lemma material_implication_LEM :
  (forall P Q : Prop, (P -> Q) -> ~ P \/ Q)
    <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
    intros mi P. apply or_comm. apply mi. intro. assumption.
    intros LEM P Q H. destruct (LEM P) as [p | p].
      right. apply H. assumption.
      left. assumption.
Qed.

Lemma material_equivalence_LEM :
  (forall P Q : Prop, (P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q))
    <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
    intros me P. destruct (me P P).
      split; trivial.
      destruct H. left. assumption.
      destruct H. right. assumption.
    intros LEM P Q HPQ. destruct HPQ as [PQ QP].
      destruct (LEM P) as [p | np], (LEM Q) as [q | nq].
        left. split; assumption.
        specialize (PQ p). contradiction.
        specialize (QP q). contradiction.
        right. split; assumption.
Qed.


Lemma Peirce_LEM :
  (forall P Q : Prop, ((P -> Q) -> P) -> P)
    <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
    Focus 2. intros LEM P Q H. destruct (LEM P) as [p | np].
      assumption.
      apply H. intro. contradiction.
    intros Peirce P. apply (Peirce _ (~ P)). intro H. right. intro p.
      apply H.
        left. assumption.
        assumption.
Qed.

Lemma consequentia_mirabilis_LEM :
  (forall P : Prop, (~ P -> P) -> P)
    <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
    intros CM P. apply CM. intro notLEM. right. intro p. apply notLEM.
      left. assumption.
    intros LEM P H. destruct (LEM P) as [p | np].
      assumption.
      apply H. assumption.
Qed.

Lemma contraposition_LEM :
  (forall P Q : Prop, (~ Q -> ~ P) -> (P -> Q))
    <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
    intros C P. apply (C (~ ~ (P \/ ~ P))).
      intros H1 H2. contradiction.
      intro H. apply H. right. intro p. apply H. left. assumption.
    intros LEM P Q H p. destruct (LEM Q) as [q | nq].
      assumption.
      specialize (H nq). contradiction.
Qed.



Lemma DNE_MI :
  DNE <-> MI.
Proof.
  u.
    intros DNE P Q pq. apply DNE. intro H. apply H. left. intro p.
      apply H. right. apply pq. assumption.
    intros MI P nnp. destruct (MI P P) as [np | p].
      intro p. assumption.
      contradiction.
      assumption.
Qed.

Lemma DNE_ME :
  DNE <-> ME.
Proof.
  u.
    intros DNE P Q H. destruct H as [pq qp]. apply DNE.
      intro H. apply H. right. split.
        intro p. apply H. left. split.
          assumption.
          apply pq. assumption.
        intro q. apply H. left. split.
          apply qp. assumption.
          assumption.
    intros ME P nnp. destruct (ME P P).
      split; trivial.
      destruct H. assumption.
      destruct H. contradiction.
Qed.

Lemma CM_MI :
  CM <-> MI.
Proof.
  u.
    intros CM P Q pq. apply CM. intro H. left. intro p. apply H.
      right. apply pq. assumption.
    intros MI P H. destruct (MI P P) as [np | p].
      intro p. assumption.
      apply H. assumption.
      assumption.
Qed.

Lemma CM_ME :
  CM <-> ME.
Proof.
  u.
    intros CM P Q H. destruct H as [pq qp]. apply CM. intro H.
      right. split.
        intro p. apply H. left. split.
          assumption.
          apply pq. assumption.
        intro q. apply H. left. split.
          apply qp. assumption.
          assumption.
    intros ME P H. destruct (ME P P) as [p | np].
      split; trivial.
      destruct p. assumption.
      destruct np. apply H. assumption.
Qed.

Lemma MI_ME :
  MI <-> ME.
Proof.
  u.
    intros MI P Q [pq qp]. destruct (MI _ _ pq) as [np | q].
      right. split.
        assumption.
        intro q. apply np. apply qp. assumption.
      left. split.
        apply qp. assumption.
        assumption.
    intros ME P Q pq. destruct (ME P P).
      split; trivial.
      right. apply pq. destruct H. assumption.
      left. destruct H. assumption.
Qed.

Lemma MI_Peirce :
  MI <-> Peirce.
Proof.
  u.
    intros MI P Q H. destruct (MI P P).
      trivial.
      apply H. intro p. contradiction.
      assumption.
    intros Peirce P Q. apply (Peirce _ False). intros H pq.
      left. intro p. apply H. intros _. right. apply pq. assumption.
Qed.

Lemma MI_Contra :
  MI <-> Contra.
Proof.
  u.
    intros MI P Q H p. destruct (MI Q Q).
      trivial.
      contradiction H.
      assumption.
    intros Contra P Q. apply Contra. intros H1 H2. apply H1.
      left. intro p. apply H1. right. apply H2. assumption.
Qed.

Lemma ME_Peirce :
  ME <-> Peirce.
Proof.
  u.
    intros ME P Q H. destruct (ME P P) as [p | np].
      split; trivial.
      destruct p. assumption.
      destruct np. apply H. intro p. contradiction.
    intros Peirce P Q [pq qp]. apply (Peirce _ False). intros H.
      right. split.
        intro p. apply H. left. split.
          assumption.
          apply pq. assumption.
        intro q. apply H. left. split.
          apply qp. assumption.
          assumption.
Qed.

Lemma ME_Contra :
  ME <-> Contra.
Proof.
  u.
    intros ME P Q npnq p. destruct (ME Q Q).
      split; trivial.
      destruct H. assumption.
      destruct H. specialize (npnq H). contradiction.
    intros Contra P Q. apply Contra. intros H [pq qp].
      apply H. right. split.
        intro p. apply H. left. split.
          assumption.
          apply pq. assumption.
        intro q. apply H. left. split.
          apply qp. assumption.
          assumption.
Qed.
