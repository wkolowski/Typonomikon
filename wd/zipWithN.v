Require Import List.
Import ListNotations.

Set Universe Polymorphism.

Fixpoint opr (f : Type -> Type -> Type) (R : Type) (ts : list Type) : Type :=
match ts with
    | [] => R
    | t :: ts' => f t (opr f R ts')
end.

Definition arr (A B : Type) : Type := A -> B.

Fixpoint zipWithN_Type_aux (n : nat) (R : Type) (ts : list Type) : Type :=
match n with
    | 0 => opr arr R (rev ts) -> opr arr R (map list (rev ts))
    | S n' => forall A : Type, zipWithN_Type_aux n' R (A :: ts)
end.

Definition zipWithN_Type (n : nat) (R : Type) : Type :=
  zipWithN_Type_aux n R [].

Compute zipWithN_Type 2 nat.




