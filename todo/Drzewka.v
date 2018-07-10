Inductive Wisienka (A : Type) : Type :=
    | L : A -> Wisienka A
    | N : Wisienka A -> Wisienka A -> Wisienka A.

Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N0 : A -> list (Tree A) -> Tree A.

Inductive DużaWisienka (A : Type) : Type :=
    | L0 : A -> DużaWisienka A
    | N1 : list (DużaWisienka A) -> DużaWisienka A.