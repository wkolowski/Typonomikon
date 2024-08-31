Fixpoint ack (n : nat) : nat -> nat :=
match n with
| 0 => S
| S n' =>
  fix ack' (m : nat) : nat :=
  match m with
  | 0 => ack n' 1
  | S m' => ack n' (ack' m')
  end
end.

Fixpoint ack2 (n : nat) : nat -> nat :=
match n with
| 0 => S
| S n' =>
  (fix ack2' (f : nat -> nat) (m : nat) : nat :=
  match m with
  | 0 => f 1
  | S m' => f (ack2' f m')
  end) (ack2 n')
end.

Fixpoint ack3' (f : nat -> nat) (m : nat) : nat :=
match m with
| 0 => f 1
| S m' => f (ack3' f m')
end.

Fixpoint ack3 (n : nat) : nat -> nat :=
match n with
| 0 => S
| S n' => ack3' (ack3 n')
end.

Lemma ack2_spec :
  forall n m : nat,
    ack2 n m = ack n m.
Proof.
  induction n as [| n']; cbn; [easy |].
  induction m as [| m']; cbn; [easy |].
  now rewrite IHm', IHn'.
Qed.

Lemma ack3_spec :
  forall n m : nat,
    ack3 n m = ack n m.
Proof.
  induction n as [| n']; cbn; [easy |].
  induction m as [| m']; cbn; [easy |].
  now rewrite IHm', IHn'.
Qed.