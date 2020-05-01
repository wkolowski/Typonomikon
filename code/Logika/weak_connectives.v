

Lemma weak_and_elim :
  forall P Q R : Prop,
    (P -> R) -> (Q -> R) -> (~ ~ R -> R) -> ~ (~ P /\ ~ Q) -> R.
(* begin hide *)
Proof.
  intros P Q R pr qr nnrr pq.
  apply nnrr. intro nr.
  apply pq. split.
    intro p. apply nr, pr, p.
    intro q. apply nr, qr, q.
Qed.
(* end hide *)

Lemma weak_ex_elim :
  forall (A : Type) (P : A -> Prop) (R : Prop),
    (forall x : A, P x -> R) -> (~ ~ R -> R) ->
      ~ (forall x : A, ~ P x) -> R.
(* begin hide *)
Proof.
  intros A P R Hpr Hnr Hnp.
  apply Hnr. intro nr.
  apply Hnp. intros x np.
  apply nr, (Hpr x), np.
Qed.
(* end hide *)

Lemma ex_dec :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, P x \/ ~ P x) ->
      (exists x : A, P x) \/ ~ (exists x : A, P x).
Abort.

Lemma forall_dec :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, P x \/ ~ P x) ->
      (forall x : A, P x) \/ ~ (forall x : A, P x).
(* begin hide *)
Proof.
  intros A P H.
Abort.
(* end hide *)