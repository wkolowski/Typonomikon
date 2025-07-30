Inductive loop : unit -> unit -> Prop :=
| loop' : forall x r : unit, loop x r -> loop x r.

Lemma loop_div :
  forall x r : unit, loop x r -> False.
Proof.
  induction 1.
  assumption.
Qed.

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

Inductive bad : bool -> bool -> Prop :=
| bad' : forall b r : bool, bad b (negb r) -> bad b r.

Lemma bad_spec :
  forall b r : bool,
    ~ bad b r.
Proof.
  induction 1.
  assumption.
Qed.