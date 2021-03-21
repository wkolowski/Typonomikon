Inductive IR (D : Type) : Type :=
    | iota  : D -> IR D
    | sigma : forall A : Type, (A -> IR D) -> IR D
    | delta : forall A : Type, ((A -> D) -> IR D) -> IR D.