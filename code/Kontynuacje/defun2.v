(** * Defunkcjonalizacja, przykład 2 *)

(** Wzięte z https://ncatlab.org/nlab/show/defunctionalization *)

Fixpoint fac (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => n * fac n'
end.

Compute fac 5.

Fixpoint facCPS (n : nat) (k : nat -> nat) : nat :=
match n with
    | 0 => k 1
    | S n' => facCPS n' (fun r => k (n * r))
end.

Compute facCPS 5 (fun n => n).

Inductive DefunNatNat : Type :=
    | Id : DefunNatNat
    | Mul : nat -> DefunNatNat -> DefunNatNat.

Fixpoint eval (k : DefunNatNat) (n : nat) : nat :=
match k with
    | Id => n
    | Mul r k' => eval k' (r * n)
end.

Compute eval (Mul 5 Id) 1.

Fixpoint facCPSDefun (n : nat) (k : DefunNatNat) : nat :=
match n with
    | 0 => eval k 1
    | S n' => facCPSDefun n' (Mul n k)
end.

Compute facCPSDefun 5 Id.

Lemma facCPS_spec :
  forall (n : nat) (k : nat -> nat),
    facCPS n k = k (fac n).
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    intros. rewrite IHn'. reflexivity.
Qed.

Lemma facCPSDefun_spec :
  forall (n : nat) (k : DefunNatNat),
    facCPSDefun n k = eval k (fac n).
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    intros. rewrite IHn'. cbn. reflexivity.
Qed.