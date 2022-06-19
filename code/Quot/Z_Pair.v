Require Import Recdef StrictProp Bool Lia.

Inductive Z : Type :=
| pair : nat -> nat -> Z.

Function norm (n m : nat) : nat * nat :=
match n, m with
| S n', S m' => norm n' m'
| _   , _    => (n, m)
end.

Definition norm' (k : Z) : Z :=
match k with
| pair n m => let (n', m') := norm n m in pair n' m'
end.

Record Z' : Type :=
{
    num : Z;
    norm_num : Squash (norm' num = num);
}.

Lemma norm_idempotent :
  forall n m n' m' : nat,
    norm n m = (n', m') ->
      norm n' m' = (n', m').
Proof.
  intros n m n' m' Hnorm.
  functional induction norm n m.
  - apply IHp; assumption.
  - destruct n, m; inversion Hnorm; subst; cbn.
    1-3: reflexivity.
    contradiction.
Qed.

Lemma norm'_idempotent :
  forall k : Z,
    norm' (norm' k) = norm' k.
Proof.
  intros [n m].
  unfold norm'.
  destruct (norm n m) eqn: Heq1.
  destruct (norm n0 n1) eqn: Heq2.
  erewrite norm_idempotent in Heq2.
  - congruence.
  - eassumption.
Qed.