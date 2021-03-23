Inductive List (A : Type) : Type :=
    | Empty : List A
    | Nonempty : NonEmptyList A -> List A

with NonEmptyList (A : Type) : Type :=
    | Cons  : A -> List A -> NonEmptyList A.