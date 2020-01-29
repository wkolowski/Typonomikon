
Lemma WLEM :
  forall P : Prop, ~ P \/ ~ ~ P.
Proof.
  intro P. left. intro p.
Restart.
  intro P. right. intro np. apply np.
Abort.

Lemma WLEM_irrefutable :
  forall P : Prop, ~ ~ (~ P \/ ~ ~ P).
Proof.
  intros P H.
  apply H. left. intro p.
  apply H. right. intro np.
  contradiction.
Qed.

Lemma LEM_WLEM :
  (forall P : Prop, P \/ ~ P) ->
    (forall P : Prop, ~ P \/ ~ ~ P).
Proof.
  intros LEM P.
  destruct (LEM P) as [p | np].
    right. intro np. contradiction.
    left. assumption.
Qed.