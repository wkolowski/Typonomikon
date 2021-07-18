Inductive BT (A : Type) : Type :=
    | Empty    : BT A
    | NonEmpty : NonEmptyBT A -> BT A

with NonEmptyBT (A : Type) : Type :=
    | Nnode    : A -> BT A -> BT A -> NonEmptyBT A.

