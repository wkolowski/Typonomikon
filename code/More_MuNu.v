(** * Ordinary inductive types *)

Module NatF.

Inductive NatF (X : Type) : Type :=
    | Zero : NatF X
    | Succ : X -> NatF X.

Arguments Zero {X}.
Arguments Succ {X} _.

Inductive Nat : Type :=
    | In : NatF Nat -> Nat.

Fixpoint f (n : nat) : Nat :=
match n with
    | 0 => In Zero
    | S n' => In (Succ (f n'))
end.

Fixpoint g (n : Nat) : nat :=
match n with
    | In Zero => 0
    | In (Succ n') => S (g n')
end.

Lemma fg :
  forall n : nat,
    g (f n) = n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    f_equal. assumption.
Qed.

Lemma gf :
  forall n : Nat,
    f (g n) = n.
Proof.
  fix IH 1.
  destruct n as [[| n']]; cbn.
    reflexivity.
    do 2 f_equal. apply IH.
Qed.

End NatF.

(** * Parameterized types *)

Module BTreeF.

Inductive BTreeF (F : Type -> Type) (A : Type) : Type :=
    | EF : BTreeF F A
    | NF : A -> F A -> F A -> BTreeF F A.

Arguments EF {F A}.
Arguments NF {F A} _ _ _.

Inductive BTree (A : Type) : Type :=
    | In : BTreeF BTree A -> BTree A.

End BTreeF.

(** * Mutual inductive types *)

Module FinitaryTreeF.

Inductive Tree (A : Type) : Type :=
    | Empty : Tree A
    | Node  : A -> Forest A -> Tree A

with Forest (A : Type) : Type :=
    | Nil  : Forest A
    | Cons : Tree A -> Forest A -> Forest A.

Inductive TreeF (T F : Type -> Type) (A : Type) : Type :=
    | EmptyF : TreeF T F A
    | NodeF  : A -> T A -> TreeF T F A

with ForestF (T F : Type -> Type) (A : Type) : Type :=
    | NilF  : ForestF T F A
    | ConsF : T A -> F A -> ForestF T F A.

Unset Positivity Checking.
Fail Inductive Tree' (A : Type) : Type :=
    | InT : TreeF Tree' Forest' A -> Tree' A

with Forest' (A : Type) : Type :=
    | InF : ForestF Tree' Forest' A -> Forest' A.

End FinitaryTreeF.

(** * Indexed families *)

(** See MuNu.v *)

