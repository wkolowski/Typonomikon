Inductive List (A : Type) : Type :=
    | Empty : List A
    | NonEmpty : NonEmptyList A -> List A

with NonEmptyList (A : Type) : Type :=
    | Cons  : A -> List A -> NonEmptyList A.

Arguments Empty    {A}.
Arguments NonEmpty {A} _.
Arguments Cons     {A} _ _.

(** Despite being weird, these lists are normal and ordinary. *)

Module TheSameAsOrdinary.

Require Import List.
Import ListNotations.

Fixpoint f {A : Type} (w : List A) : list A :=
match w with
    | Empty => []
    | NonEmpty (Cons x l) => x :: f l
end.

Fixpoint g {A : Type} (l : list A) : List A :=
match l with
    | [] => Empty
    | h :: t => NonEmpty (Cons h (g t))
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

End TheSameAsOrdinary.

Print List.

Definition isEmpty {A : Type} (l : List A) : bool :=
match l with
    | Empty => true
    | NonEmpty _ => false
end.

Definition neisEmpty {A : Type} (ne : NonEmptyList A) : bool :=
  false.

Fixpoint len {A : Type} (l : List A) : nat :=
match l with
    | Empty => 0
    | NonEmpty ne => nelen ne
end

with nelen {A : Type} (ne : NonEmptyList A) : nat :=
match ne with
    | Cons h t => 1 + len t
end.

Fixpoint app {A : Type} (l1 l2 : List A) : List A :=
match l1 with
    | Empty => l2
    | NonEmpty ne => NonEmpty (neapp ne l2)
end

with neapp {A : Type} (ne : NonEmptyList A) (l : List A) : NonEmptyList A :=
match ne with
    | Cons h t => Cons h (app t l)
end.

Fixpoint snoc {A : Type} (x : A) (l : List A) : NonEmptyList A :=
match l with
    | Empty => Cons x Empty
    | NonEmpty ne => nesnoc x ne
end

with nesnoc {A : Type} (x : A) (ne : NonEmptyList A) : NonEmptyList A :=
match ne with
    | Cons h t => Cons h (NonEmpty (snoc x t))
end.

Fixpoint rev {A : Type} (l : List A) : List A :=
match l with
    | Empty => Empty
    | NonEmpty ne => NonEmpty (nerev ne)
end

with nerev {A : Type} (ne : NonEmptyList A) : NonEmptyList A :=
match ne with
    | Cons h t => snoc h (rev t)
end.

Fixpoint map {A B : Type} (f : A -> B) (l : List A) : List B :=
match l with
    | Empty => Empty
    | NonEmpty n => NonEmpty (nemap f n)
end

with nemap {A B : Type} (f : A -> B) (ne : NonEmptyList A) : NonEmptyList B :=
match ne with
    | Cons h l => Cons (f h) (map f l)
end.

Fixpoint filter {A : Type} (p : A -> bool) (l : List A) : List A :=
match l with
    | Empty => Empty
    | NonEmpty ne => nefilter p ne
end

with nefilter {A : Type} (p : A -> bool) (ne : NonEmptyList A) : List A :=
match ne with
    | Cons h t => if p h then NonEmpty (Cons h (filter p t)) else filter p t
end.

(*
join
bind
replicate
iterate i iter
head, tail i uncons
head
tail
uncons
last, init i unsnoc
last
init
unsnoc


nth
take
drop

cycle
splitAt
insert
replace
remove
zip
unzip
zipWith
unzipWith
*)