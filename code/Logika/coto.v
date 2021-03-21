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