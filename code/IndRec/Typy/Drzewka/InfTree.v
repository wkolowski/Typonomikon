
Inductive InfTree (A : Type) : Type :=
    | E1 : InfTree A
    | N1 : A -> forall {B : Type}, (B -> InfTree A) -> InfTree A.