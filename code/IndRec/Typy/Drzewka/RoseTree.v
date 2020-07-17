
Inductive RoseTree (A : Type) : Type :=
    | L : A -> RoseTree A
    | N : list (RoseTree A) -> RoseTree A.

Scheme RoseTree_ind' := Induction for RoseTree Sort Prop.

Check RoseTree_ind'.