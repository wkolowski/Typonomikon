Definition UIP : Prop :=
  forall (A : Type) (x y : A) (p q : x = y), p = q.

Definition ProofIrrelevance : Prop :=
  forall (P : Prop) (p1 p2 : P), p1 = p2.

Definition PropExt : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Theorem PropExt_and_UIP_imply_ProofIrrelevance :
  PropExt -> UIP -> ProofIrrelevance.
Proof.
  unfold PropExt, UIP, ProofIrrelevance.
  intros PropExt UIP P p1 p2.
  assert (P = (P = True)).
  {
    apply PropExt. firstorder.
  }
  revert p1 p2.
  rewrite H.
  apply UIP.
Qed.
