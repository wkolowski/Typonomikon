Require Import List.
Import ListNotations.

Inductive Tree (A : Type) : Type :=
| E0 : Tree A
| N0 : A -> list (Tree A) -> Tree A.

Arguments E0 {A}.
Arguments N0 {A} _ _.

Fixpoint tmap {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
match t with
| E0 => E0
| N0 v ts => N0 (f v) (map (tmap f) ts)
end.