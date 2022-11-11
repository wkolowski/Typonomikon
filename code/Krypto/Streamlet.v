From Typonomikon Require Import Hashable.

Section Streamlet.

Context
  (Payload : Type)
  `{Hashable Payload}.

Record Block : Type :=
{
  parentHash : int;
  epoch : nat;
  payload : Payload;
}.

#[export] Instance Hashable_Block : Hashable Block :=
{
  hash b := add (hash (parentHash b)) (add (hash (epoch b)) (hash (payload b)));
}.

Inductive Chain : Type :=
| Genesis
| Extend : Block -> Chain -> Chain.

Inductive Valid : Chain -> Prop :=
| vg : Valid Genesis
| vs : forall b : Block, Valid (Extend b Genesis)
| ve : forall (b1 b2 : Block) (c : Chain),
         Valid (Extend b2 c) -> epoch b2 < epoch b1 -> hash b1 = parentHash b2 ->
           Valid (Extend b1 (Extend b2 c)).

End Streamlet.