(* Wzięte stąd: https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-hosc09.pdf *)

Inductive BushF (F : Type -> Type) (A : Type) : Type :=
    | LeafF : BushF F A
    | NodeF : A -> F (F A) -> BushF F A.

Fail Inductive Bush (A : Type) : Type :=
    | Leaf : Bush A
    | Node : A -> Bush (Bush A) -> Bush A.