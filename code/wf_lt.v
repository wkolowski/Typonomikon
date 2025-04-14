Require Import Recdef.

Function lt (n m : nat) : Prop :=
match n, m with
| n, 0 => False
| 0, S _ => True
| S n', S m' => lt n' m'
end.

Lemma lt_trans :
  forall x y z : nat, lt x y -> lt y z -> lt x z.
Proof.
  intros x y z; revert y.
  functional induction (lt x z).
  - now intros []; cbn.
  - easy.
  - intros []; cbn; [easy |].
    apply IHP.
Qed.

Lemma lt_trans' :
  forall x y z : nat, lt x y -> lt y z -> lt x z.
Proof.
  intros x y z; revert x z.
  induction y as [| y' IH].
  - now intros [] z; cbn.
  - intros [] []; cbn; [easy.. |].
    apply IH.
Restart.
  intros x y z; revert x y.
  induction z as [| z' IH].
  - now intros x []; cbn.
  - intros [] []; cbn; [easy.. |].
    now apply IH.
Restart.
  induction x as [| x' IH].
  - now intros [] [].
  - intros [] []; cbn; [easy.. |].
    apply IH.
Qed.