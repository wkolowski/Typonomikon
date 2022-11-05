Inductive ALVec (A : Type) : nat -> Type :=
| Nil  : ALVec A 0
| Cons : forall (m : nat) (h : A) {n : nat} (t : ALVec A n), ALVec A (1 + m + n).

