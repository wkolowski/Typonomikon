(** TODO: opisać to gdzieś tyż *)

Scheme Equality for list.

Check list_beq.
(* ===> list_beq : forall A : Type, (A -> A -> bool) -> list A -> list A -> bool *)

Check list_eq_dec.
(* ===> list_eq_dec :
          forall (A : Type) (eq_A : A -> A -> bool),
            (forall x y : A, eq_A x y = true -> x = y) ->
            (forall x y : A, x = y -> eq_A x y = true) ->
              forall x y : list A, {x = y} + {x <> y}
*)

Set Decidable Equality Schemes.

Set Boolean Equality Schemes.