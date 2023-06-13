(** * D2e: Rekursja polimorficzna [TODO] *)

From Typonomikon Require Import D5.

(** * Rekursja polimorficzna *)

Module Nested.

Inductive Nested (A : Type) : Type :=
  Epsilon | Cons (h : A) (t : Nested (list A)).

Arguments Epsilon {A}.
Arguments Cons    {A} _ _.

Inductive Nested' : Type -> Type :=
| Epsilon' : forall A : Type, Nested' A
| Cons' : forall A : Type, A -> Nested' (list A) -> Nested' A.

Fixpoint len {A : Type} (l : Nested A) : nat :=
match l with
| Epsilon => 0
| Cons _ t => 1 + len t
end.

End Nested.

Module Seq.

Inductive Seq (A : Type) : Type :=
| SNil : Seq A
| SCons : A -> Seq (A * A) -> Seq A.

Arguments SNil  {A}.
Arguments SCons {A} _ _.

Fixpoint size {A : Type} (s : Seq A) : nat :=
match s with
| SNil => 0
| SCons _ t => 1 + 2 * size t
end.

End Seq.

Module Nested2.

Inductive Nested (A : Type) : Type :=
| Singl : A -> Nested A
| Nestd : Nested (list A) -> Nested A.

End Nested2.