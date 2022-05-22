Require Import List.
Import ListNotations.

Inductive llist (A : Type) : Type :=
    | lnil : llist A
    | lcons : A -> (unit -> llist A) -> llist A.

Arguments lnil  {A}.
Arguments lcons {A} _ _.

Notation "[[]]" := lnil.
Notation "x ::: y" := (lcons x y) (at level 60, right associativity).
Notation "[[ x ; .. ; y ]]" := (lcons x .. (lcons y lnil) ..).

Fixpoint length {A : Type} (l : llist A) : nat :=
match l with
    | [[]] => 0
    | h ::: t => S (length (t tt))
end.

Fixpoint fromList {A : Type} (l : list A) : llist A :=
match l with
    | [] => [[]]
    | h :: t => h ::: fun _ => fromList t
end.

(* TODO: is there any point in it? *)