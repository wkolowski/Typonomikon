Module BiedaBeth.

Fixpoint Beth (n : nat) (A : Type) : Type :=
match n with
| 0 => A
| S n' => Beth n' A -> bool
end.

Compute Beth 20 nat.

Definition StrongLimit : Type :=
  {n : nat & Beth n nat}.

Definition inj {n : nat} (b : Beth n nat) : StrongLimit :=
  existT _ n b.

End BiedaBeth.

Module BethNaBogato.

Inductive Ord : Type :=
    | Z   : Ord
    | S   : Ord -> Ord
    | Lim : (nat -> Ord) -> Ord.

Fixpoint Beth (o : Ord) : Type :=
match o with
| Z     => nat
| S o'  => Beth o' -> bool
| Lim f => {n : nat & Beth (f n)}
end.


Compute Beth (Lim (fun n : nat => Z)).

End BethNaBogato.