
Inductive InfWisienka (A : Type) : Type :=
    | L1 : A -> InfWisienka A
    | N1 : forall {B : Type}, (B -> InfWisienka A) -> InfWisienka A.