Inductive option (A : Type) : Type :=
    | None : option A
    | Some : A -> option A.

Arguments None {A}.
Arguments Some {A} _.

Definition isNone {A : Type} (o : option A) : bool :=
match o with
    | None => true
    | _ => false
end.

Definition orElse {A : Type} (o : option A) (x : A) : A :=
match o with
    | None => x
    | Some a => a
end.

Notation "o 'or' 'else' x" := (orElse o x) (at level 50).

Require Import List.
Import ListNotations.

(*Definition optionToList {A : Type} (o : option A) : list A :=
match o with
    | None => []
    | Some x => [x]
end.*)

Fixpoint catOptions {A : Type} (l : list (option A)) : list A :=
match l with
    | [] => []
    | None :: t => catOptions t
    | Some h :: t => h :: catOptions t
end.

Definition omap {A B : Type} (f : A -> B) (x : option A) : option B :=
match x with
    | None => None
    | Some a => Some (f a)
end.

