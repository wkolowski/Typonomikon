Goal
  forall x1 y1 z1 x2 y2 z2 : nat,
    (x1, (y1, z1)) = (x2, (y2, z2)) -> z1 = z2.
Proof.
  intros * [= _ _ ->].
  reflexivity.
Qed.