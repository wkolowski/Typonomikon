Require Import List.

Inductive RoseTree (A : Type) : Type :=
    | E : RoseTree A
    | N : A -> list (RoseTree A) -> RoseTree A.

(** Okazuje się, że [decide_equality] potrafi udowodnić, że [RoseTree A] ma rozstrzygalną równość. *)
Lemma RoseTree_eq_dec :
  forall
    (A : Type) (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (x y : RoseTree A), {x = y} + {x <> y}.
Proof.
  fix RoseTree_eq_dec 3.
  decide equality.
  apply list_eq_dec. apply RoseTree_eq_dec. assumption.
Defined.

(** Uwaga: to całkiem dziwne, że poszło aż tak łatwo, bo przecież funkcja którą definiujemy
    jest użyta rekurencyjnie jako argument [list_eq_dec], tzn. mamy do czynienia z rekursją
    wyższego rzędu. *)