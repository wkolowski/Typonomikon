Inductive SwapTree (A B : Type) : Type :=
    | E : SwapTree A B
    | N : A -> SwapTree B A -> SwapTree B A -> SwapTree A B.