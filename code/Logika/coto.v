Goal
  ~
  (forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x : A, P x -> Q) -> (forall x : A, P x) -> Q).
Proof.
  intro H.
  apply (H False (fun _ => False)).
    intros. assumption.
    trivial.
Qed.

Goal forall P : Prop,
  (P \/ ~ P) <-> (~ ~ (P \/ ~ P) -> P \/ ~ P).
Proof.
  split; intros H.
  - intros _. assumption.
  - apply H. intro H'. apply H'. right. intro p. apply H'. left. assumption.
Qed.