Module Preorder_ind.

Inductive PreOrdCmp : Type :=
| LtEq
| GtEq
| Both
| Neither.

End Preorder_ind.

Module Preorder_def.

Definition PreOrdCmp : Type := bool * bool.

End Preorder_def.

Module PartialOrder.

Inductive PosetCmp : Type :=
| Lt
| Eq
| Gt
| Neither.

End PartialOrder.

Module LinearOrder.

Inductive LinOrdCmp : Type :=
| Lt
| Eq
| Gt.

End LinearOrder.

(** Beware: total orders and linear orders are actually different things constructively! *)

Module TotalOrder.

Inductive TotalOrderCmp : Type :=
| Lt
| Eq
| Gt.

End TotalOrder.