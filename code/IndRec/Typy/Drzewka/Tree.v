Inductive Tree (A : Type) : Type :=
    | E0 : Tree A
    | N0 : A -> list (Tree A) -> Tree A.