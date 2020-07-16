


Inductive FinWisienka (A : Type) : Type :=
    | L0 : A -> FinWisienka A
    | N0 : list (FinWisienka A) -> FinWisienka A.