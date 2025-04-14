Inductive search (p : nat -> bool) : nat -> nat -> Prop :=
| search_here : forall n : nat, p n = true -> search p n n
| search_succ : forall n r : nat, p n = false -> search p (S n) r -> search p n r.

Lemma search_spec :
  forall (p : nat -> bool) (n r : nat),
    search p n r -> p r = true.
Proof.
  induction 1.
  - assumption.
  - assumption.
Qed.