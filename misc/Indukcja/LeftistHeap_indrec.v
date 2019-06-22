(* Bez sensu.

  Inductive LHeap {A : Type} (R : A -> A -> bool) : Type :=
      | E : LHeap R
      | N :
          forall (v : A) (l r : LHeap R),
            rspine r <=? rspine l = true ->
            ok v l = true -> ok v r = true -> LHeap R

  with

  Fixpoint rspine {A : Type} {R : A -> A -> bool} (h : LHeap R) : nat :=
  match h with
      | E => 0
      | N _ _ r _ _ _ => 1 + rspine r
  end

  with

  Definition
    ok {A : Type} {R : A -> A -> bool} (x : A) (h : LHeap A) : bool :=
  match h with
      | E => true
      | N v _ _ _ _ _ => R v x
  end.

*)

(*

  Inductive LHeap {A : Type} (R : A -> A -> bool) : nat -> Type :=
      | E : LHeap R 0
      | N :
          forall (v : A) {n m : nat} (l : LHeap n) (r : LHeap R m),
            m <=? n = true -> ok v l = true -> ok v r = true ->
              LHeap R (S m)

  with

  Definition
    ok {A : Type} {R : A -> A -> bool}
       (x : A) {n : nat} (h : LHeap A n) : bool :=
  match h with
      | E => true
      | N v _ _ _ _ _ => R v x
  end.

*)