Function fact (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => S n' * fact n'
end.

Function factCPS {A : Type} (n : nat) (k : nat -> A) : A :=
match n with
    | 0 => k 1
    | S n' => factCPS n' (fun res : nat => k (n * res))
end.

Theorem factCPS_spec :
  forall (A : Type) (n : nat) (k : nat -> A),
    factCPS n k = k (fact n).
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Restart.
  intros.
  functional induction @factCPS A n k; rewrite ?IHa; cbn; reflexivity.
Qed.

Check fact_ind.
Check factCPS_ind.

Fixpoint plus (n m : nat) : nat :=
match n with
    | 0 => m
    | S n' => S (plus n' m)
end.

Function plusCPS {A : Type} (n m : nat) (k : nat -> A) : A :=
match n with
    | 0 => k m
    | S n' => plusCPS n' m (fun res => k (S res))
end.

Theorem plusCPS_spec :
  forall (A : Type) (n m : nat) (k : nat -> A),
    plusCPS n m k = k (plus n m).
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.

Function fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') => fib n'' + fib n'
end.

Fixpoint fibCPS (n : nat) (k : nat -> nat) : nat :=
match n with
    | 0 => k 0
    | 1 => k 1
    | S (S n'' as n') =>
        fibCPS n'' (fun arg1 => fibCPS n' (fun arg2 => k (arg1 + arg2)))
end.

Lemma fibCPS_eq :
  forall (n : nat) (k : nat -> nat),
    fibCPS (S (S n)) k =
        fibCPS n (fun arg1 => fibCPS (S n) (fun arg2 => k (arg1 + arg2))).
Proof. reflexivity. Qed.

Theorem fibCPS_spec :
  forall (n : nat) (k : nat -> nat),
    fibCPS n k = k (fib n).
Proof.
  intros. generalize dependent k.
  functional induction fib n; intros;
    try rewrite fibCPS_eq, IHn0, IHn1; reflexivity.
Qed.

Axiom pi : forall (P : Prop) (p1 p2 : P), p1 = p2.

Inductive Erasable (A : Type) : Prop :=
    | erasable : A -> Erasable A.

Arguments erasable {A} _.

Axiom Erasable_inj :
  forall (A : Type) (x y : A), erasable x = erasable y -> x = y.

Theorem wut : False.
Proof.
  cut (0 = 1).
    inversion 1.
    apply Erasable_inj, pi.
Qed.