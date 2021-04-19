Inductive List (A : Type) : Type :=
    | Empty : List A
    | Nonempty : NonEmptyList A -> List A

with NonEmptyList (A : Type) : Type :=
    | Cons  : A -> List A -> NonEmptyList A.

Arguments Empty    {A}.
Arguments Nonempty {A} _.
Arguments Cons     {A} _ _.

(** Despite being weird, these lists are normal and ordinary. *)

Require Import List.
Import ListNotations.

Fixpoint f {A : Type} (w : List A) : list A :=
match w with
    | Empty => []
    | Nonempty (Cons x l) => x :: f l
end.

Fixpoint g {A : Type} (l : list A) : List A :=
match l with
    | [] => Empty
    | h :: t => Nonempty (Cons h (g t))
end.

Lemma fg :
  forall {A : Type} (w : List A), g (f w) = w.
Proof.
  fix IH 2.
  destruct w as [| [h t]]; cbn.
    reflexivity.
    rewrite IH. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (l : list A), f (g l) = l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.