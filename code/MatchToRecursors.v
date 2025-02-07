Fixpoint half (n : nat) : nat :=
match n with
| 0 => 0
| 1 => 0
| S (S n') => S (half n')
end.

Fixpoint half' (acc : nat) (n : nat) : nat :=
match n with
| 0 => acc
| 1 => acc
| S (S n') => half' (S acc) n'
end.

Lemma half'_spec :
  forall acc n : nat,
    half' acc n = acc + half n.
Proof.
  fix IH 2.
  destruct n as [| [| n']]; cbn.
  - now rewrite <- plus_n_O.
  - now rewrite <- plus_n_O.
  - now rewrite IH, <- plus_n_Sm; cbn.
Qed.

Fixpoint halve' (n : nat) : nat * nat :=
match n with
| 0 => (0, 0)
| S n' => let '(a, b) := halve' n' in (b, S a)
end.

Lemma halve'_spec :
  forall n : nat,
    halve' n = (half n, half (S n)).
Proof.
  induction n as [| n']; cbn; [easy |].
  now rewrite IHn'; cbn.
Qed.

Definition halve (n : nat) : nat * nat :=
  nat_rec _ (0, 0) (fun n' halve_n' =>
    let '(a, b) := halve_n' in (b, S a)) n.

Fixpoint div3 (n : nat) : nat :=
match n with
| 0 => 0
| 1 => 0
| 2 => 0
| S (S (S n')) => S (div3 n')
end.

Fixpoint div3' (n : nat) : nat * nat * nat :=
match n with
| 0 => (0, 0, 0)
| S n' => let '(a, b, c) := div3' n' in (b, c, S a)
end.

Definition div3_rec (n : nat) : nat * nat * nat :=
  nat_rec _ (0, 0, 0) (fun n' '(a, b, c) => (b, c, S a)) n.

Lemma div3_rec_spec :
  forall n : nat,
    div3_rec n = div3' n.
Proof.
  induction n as [| [| n']]; cbn in *; [easy.. |].
  now rewrite IHn; cbn.
Qed.

Lemma div3_rec_spec' :
  forall n : nat,
    div3_rec n = (div3 n, div3 (S n), div3 (S (S n))).
Proof.
  induction n as [| [| n']]; cbn in *; [easy.. |].
  now rewrite IHn; cbn.
Qed.