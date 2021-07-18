Inductive List (A : Type) : Type :=
    | Empty : List A
    | NonEmpty : NonEmptyList A -> List A

with NonEmptyList (A : Type) : Type :=
    | Cons  : A -> List A -> NonEmptyList A.

Arguments Empty    {A}.
Arguments NonEmpty {A} _.
Arguments Cons     {A} _ _.

(** Despite being weird, these lists are equivalent to the ordinary lists. *)

Require List.

Module TheSameAsOrdinary.

Import List.
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

Fixpoint join {A : Type} (l : List (List A)) : List A :=
match l with
    | Empty => Empty
    | NonEmpty ne => nejoin ne
end

with nejoin {A : Type} (ne : NonEmptyList (List A)) : List A :=
match ne with
    | Cons h t => app h (join t)
end.

Fixpoint bind {A B : Type} (l : List A) (f : A -> List B) : List B :=
match l with
    | Empty => Empty
    | NonEmpty ne => nebind ne f
end

with nebind {A B : Type} (ne : NonEmptyList A) (f : A -> List B) : List B :=
match ne with
    | Cons h t => app (f h) (bind t f)
end.

Fixpoint replicate (n : nat) {A : Type} (x : A) {struct n} : List A :=
match n with
    | 0 => Empty
    | S n' => NonEmpty (Cons x (replicate n' x))
end.

Fixpoint take (n : nat) {A : Type} (l : List A) : List A :=
match l with
    | Empty => Empty
    | NonEmpty ne => netake n ne
end

with netake (n : nat) {A : Type} (ne : NonEmptyList A) : List A :=
match n, ne with
    | 0, _ => Empty
    | S n', Cons h t => NonEmpty (Cons h (take n' t))
end.

(*
iterate i iter
head, tail i uncons
last, init i unsnoc
*)

Fixpoint drop (n : nat) {A : Type} (l : List A) : List A :=
match l with
    | Empty => Empty
    | NonEmpty ne => nedrop n ne
end

with nedrop (n : nat) {A : Type} (ne : NonEmptyList A) : List A :=
match n, ne with
    | 0, _ => Empty
    | S n', Cons h t => drop n' t
end.

Fixpoint nth (n : nat) {A : Type} (l : List A) : option A :=
match l with
    | Empty => None
    | NonEmpty ne => nenth n ne
end

with nenth (n : nat) {A : Type} (ne : NonEmptyList A) : option A :=
match n, ne with
    | 0, Cons h _ => Some h
    | S n', Cons _ t => nth n' t
end.

Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (la : List A) (lb : List B) : List C :=
match la, lb with
    | Empty, _ => Empty
    | _, Empty => Empty
    | NonEmpty na, NonEmpty nb => NonEmpty (nezipWith f na nb)
end

with nezipWith {A B C : Type} (f : A -> B -> C)
  (na : NonEmptyList A) (nb : NonEmptyList B) : NonEmptyList C :=
match na, nb with
    | Cons ha ta, Cons hb tb => Cons (f ha hb) (zipWith f ta tb)
end.

Lemma app_Empty_r :
  forall {A : Type} (l : List A),
    app l Empty = l.
Proof.
  fix IH 2.
  destruct l as [| [h t]]; cbn.
    reflexivity.
    rewrite IH. reflexivity.
Qed.

Lemma snoc_app :
  forall {A : Type} (l1 l2 : List A) (x : A),
    NonEmpty (snoc x (app l1 l2)) = app l1 (NonEmpty (snoc x l2)).
Proof.
  fix IH 2.
  destruct l1 as [| [h1 t1]]; cbn; intros.
    reflexivity.
    rewrite IH. reflexivity.
Qed.

Lemma rev_app :
  forall {A : Type} (l1 l2 : List A),
    rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
  fix IH 2.
  destruct l1 as [| [h1 t1]]; cbn; intros.
    rewrite app_Empty_r. reflexivity.
    rewrite IH. rewrite snoc_app. reflexivity.
Qed. 

(* TODO for WeirdLists:
cycle
splitAt
insert
replace
remove
unzip
unzipWith
*)