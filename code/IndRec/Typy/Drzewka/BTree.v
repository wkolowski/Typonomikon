

(** Pamiętać, że w RCC jest jakotaka implementacja BTree, którą można tu
    po prostu skopiować. *)

Inductive BTree (A : Type) : Type :=
    | E : BTree A
    | N : A -> BTree A -> BTree A -> BTree A.