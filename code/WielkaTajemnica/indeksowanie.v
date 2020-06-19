(** * Indeksowanie struktur danych *)

Require Import D5.

(** Pamiętasz zapewne funkcję [nth] z rozdziału o listach, której
    celem było znalezienie [n]-tego elementu na liście [l]. Jeżeli
    twoja implementacja była poprawna i elegancka, to wyglądała
    zapewne jakoś tak: *)

Print nth.
(* ===> nth =
        fix nth (A : Type) (n : nat) (l : list A) {struct l} :
        option A :=
          match l with
          | [] => None
          | h :: t => match n with
                      | 0 => Some h
                      | S n' => nth A n' t
                      end
          end
             : forall A : Type, nat -> list A -> option A *)

(** Obraz wyłaniający się z tej definicji jest prosty:
    - w pustej liście nic nie znajdziemy
    - jeżeli lista jest niepusta, to przemierzamy ją, zerkając co i rusz
      na indeks [n]. [0] oznacza "już", zaś [S _] oznacza "jeszcze krok"

    Ma to sens, czyż nie? Zastanówmy się więc teraz, jak można
    indeksować inne struktury danych, takie jak wektory czy drzewa (co
    w zasadzie wyczerpuje pytanie, bo elementy każdego typu induktywnego
    to nic innego jak drzewa). *)

Definition nat' : Type := list unit.

(** Pierwsza rzecz, którą musimy zauważyć, to to, że liczby naturalne i
    listy [unit]ów to w zasadzie to samo. No bo pomyśl:
    - jest [0] i jest [nil]
    - jest [S 0] i jest [tt :: nil]
    - jest [S (S 0)] i jest [tt :: tt :: nil]
    - etc. *)

(** **** Ćwiczenie *)

(** Pokaż, że typy [nat] i [list unit] są izomorficzne. *)

(* begin hide *)
(* TODO *)
(* end hide *)

(** Podsumowując: listy indeksujemy liczbami naturalnymi, które są tym
    samym co listy [unit]ów. Przypadek? Nie sądzę. Można tę konstatację
    sparafrazować tak: [list A] indeksujemy za pomocą [list unit].

    Jest w tym sporo mądrości: [list A] to podłużny byt wypełniony
    elementami typu [A], zaś [list unit] to po prostu podłużny byt -
    jego zawartość jest nieistotna.

    ACHTUNG: to wszystko kłamstwa, sprawa jest skomplikowańsza niż
    myślałem. *)

(* 1 + A * X^2 *)
Module BT.

Inductive BT (A : Type) : Type :=
    | E : BT A
    | N : A -> BT A -> BT A -> BT A.

Arguments E {A}.
Arguments N {A} _ _ _.

(* 1 + 2 * X *)
Inductive IndexBT : Type :=
    | here : IndexBT
    | L : IndexBT -> IndexBT
    | R : IndexBT -> IndexBT.

Fixpoint index {A : Type} (t : BT A) (i : IndexBT) : option A :=
match t, i with
    | E, _          => None
    | N v _ _, here => Some v
    | N _ l _, L i' => index l i'
    | N _ _ r, R i' => index r i'
end.
End BT.

Module T.

(* 1 + A * X^I *)
Inductive T (I A : Type) : Type :=
    | E : T I A
    | N : A -> (I -> T I A) -> T I A.

Arguments E {I A}.
Arguments N {I A} _ _.

(* 1 + I * X *)
Inductive Index (I : Type) : Type :=
    | here : Index I
    | there : I -> Index I -> Index I.

Arguments here {I}.
Arguments there {I} _ _.

Fixpoint index {I A : Type} (t : T I A) (i : Index I) : option A :=
match t, i with
    | E, _ => None
    | N v _, here => Some v
    | N _ f, there j i' => index (f j) i'
end.

End T.

Module T2.

(* 1 + A + B + A * B * X^I *)
Inductive T (I A B : Type) : Type :=
    | E0 : T I A B
    | E1 : A -> T I A B
    | E2 : B -> T I A B
    | N  : A -> B -> (I -> T I A B) -> T I A B.

Arguments E0 {I A B}.
Arguments E1 {I A B}.
Arguments E2 {I A B}.
Arguments N  {I A B}.

(* Typ argumentów nieindukcyjnych: 1 + A + B + A * B *)
Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Reversible Pattern Implicit.

Inductive Arg (A B : Type) : Type :=
    | E0' : Arg A B
    | E1' : A -> Arg A B
    | E2' : B -> Arg A B
    | N'  : A -> B -> Arg A B.

Arguments E0' {A B}.
Arguments E1' {A B}.
Arguments E2' {A B}.
Arguments N'  {A B}.

(* Typ indeksów: 4 + I * X *)
Inductive Index (I : Type) : Type :=
    | E0i : Index I
    | E1i : Index I
    | E2i : Index I
    | N1i : Index I
    | N2i : I -> Index I -> Index I.

Arguments E0i {I}.
Arguments E1i {I}.
Arguments E2i {I}.
Arguments N1i {I}.
Arguments N2i {I}.

Fixpoint index
  {I A B : Type} (t : T I A B) (i : Index I) : option (Arg A B) :=
match t, i with
    | E0, E0i           => Some E0'
    | E1 a, E1i         => Some (E1' a)
    | E2 b, E2i         => Some (E2' b)
    | N a b f, N1i      => Some (N' a b)
    | N _ _ f, N2i j i' => index (f j) i'
    | _, _              => None
end.

(* Typ indeksów: 1 + I * X *)
Inductive Index' (I : Type) : Type :=
    | stop : Index' I
    | go   : I -> Index' I -> Index' I.

Arguments stop {I}.
Arguments go   {I}.

Fixpoint index'
  {I A B : Type} (t : T I A B) (i : Index' I) : option (Arg A B) :=
match t, i with
    | E0      , stop    => Some E0'
    | E1 a    , stop    => Some (E1' a)
    | E2 b    , stop    => Some (E2' b)
    | N a b _ , stop    => Some (N' a b)
    | N _ _ f , go j i' => index' (f j) i'
    | _       , _       => None
end.

End T2.

(** Przemyślenia: indeksowanie jest dużo bardziej związane z zipperami,
    niż mi się wydawało. Zipper pozwala sfokusować się na jakimś miejscu
    w strukturze i musimy pamiętać, jak do tego miejsca doszliśmy, tj.
    co pominęliśmy po drodze.

    Jeżeli zależy nam wyłącznie na tym, aby pokazać palcem na dane
    miejsce w strukturze, to nie musimy pamiętać, co pominęliśmy.
    Podsumowując: intuicja dotycząca typów indeksów oraz zipperów
    jest dość jasna, ale związki z różniczkowaniem są mocno pokrętne.

    Kwestią jest też jak przenieść te intuicje na indeksowane rodziny.
    Na pewno indeksami [Vec n] jest [Fin n], a skądinąd [Vec n] to
    [{n : nat & {l : list A | length l = n}}], zaś [Fin n] to [nat],
    tylko trochę ograniczone.

    Zapewne działa to bardzo dobrze... taki huj, jednak nie. *)

Module TH.

Inductive BTH (A : Type) : nat -> Type :=
    | E : BTH A 0
    | N : forall {n m : nat},
            A -> BTH A n -> BTH A m -> BTH A (1 + max n m).

Inductive Index : nat -> Type :=
    | here : forall n : nat, Index (S n)
(*    | L : forall n : nat, Index n -> Index (S n)
    | R : forall n : nat, Index n -> Index (S n).*)
    | LR : forall n m : nat, Index n + Index m -> Index (1 + max n m).

Fixpoint index {A : Type} {n : nat} (t : BTH A n) (i : Index n) : A.
Proof.
  destruct t.
    inversion i.
    inversion i; subst.
      exact a.
      try exact (index _ _ t1 H0).
Abort.

End TH.