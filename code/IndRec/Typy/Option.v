Require Import List.
Import ListNotations.
Require Import Bool.

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

Definition isSome {A : Type} (ma : option A) : bool :=
match ma with
    | Some _ => true
    | None => false
end.

Definition orElse {A : Type} (o : option A) (x : A) : A :=
match o with
    | None => x
    | Some a => a
end.

Notation "o 'or' 'else' x" := (orElse o x) (at level 50).

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

Lemma isSome_or_isNone :
  forall (A : Type) (ma : option A),
    isSome ma || isNone ma = true.
Proof.
  destruct ma; cbn; trivial.
Qed.

Definition bind
  {A B : Type} (ma : option A) (f : A -> option B) : option B :=
match ma with
    | Some a => f a
    | None => None
end.