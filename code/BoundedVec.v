Inductive vek (A : Type) : nat -> Type :=
    | vknil  :
        forall n : nat, vek A n
    | vkcons :
        forall (h : A) {n : nat} (t : vek A n), vek A (S n).

