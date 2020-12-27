(** * B2: Konstruktywny rachunek kwantyfikatorów [TODO] *)

(** * Typy i ich elementy (TODO) *)

(** Tu zestawić ze sobą P : Prop, A : Type, p : P, x : A *)

(** * Predykaty i relacje (TODO) *)

(** * Równość - najważniejsza relacja (TODO) *)

(* begin hide *)
Require Export B1.
(*
TODO: Być może coś więcej o równości (i jej alternatywnej definicji?).
TODO: Arystoteles i Leibniz
*)
(* end hide *)

(** Dobrze byłoby zapoznać się z równością przed pierwszym jej użyciem
    w rozdziale o typach induktywnych. *)

(** * Kwantyfikatory (TODO) *)

(** ** Kwantyfikator uniwersalny (TODO) *)

(** ** Kwantyfikator egzystencjalny (TODO) *)

(** ** Kwantyfikator unikatowy (TODO) *)

Print unique.
Search unique.

Definition unique {A : Type} (P : A -> Prop) : Prop :=
  exists x : A, P x /\ forall y : A, P y -> x = y.

(** Poznawszy relację równości oraz kwantyfikatory uniwersalny i
    egzystencjalny, możemy zdefiniować inny bardzo ważny "kwantyfikator",
    a mianowicie kwantyfikator unikatowy, który głosi, że istnieje
    dokładnie jeden obiekt spełniający daną właściwość. *)

(** * α-konwersja i inne rodzaje równości (TODO) *)

(** https://github.com/wkolowski/Typonomikon/blob/master/txt/równość.md *)

(* begin hide *)
(*
TODO 1: Opisać związki rodzajów równości ze składnią i semantyką
        (empiryczna obserwacja: studenci pierwszego roku nie są
        zbyt płynni w posługiwaniu się składnią _in abstracto_).
TODO 2: Pomysł na jeszcze jeden podrozdział, semantyka vs składnia
TODO 3: Użyć nominalizmów do wytłumaczenia wiązania nazw zmiennych.
*)
(* end hide *)

(** * Zadania (TODO) *)

(** - modelowanie różnych sytuacji za pomocą zdań i predykatów
    - rozwiązywanie zagadek logicznych
    - więcej zadań z exists *)

(** **** Ćwiczenie *)

(* begin hide *)
(*
Definition Classically (A : Type) : Type :=
  (forall P : Prop, P \/ ~ P) -> A.

Notation "f $ x" := (f x) (at level 100, only parsing).

Ltac cls := progress unfold Classically; intro LEM.
*)
(* end hide *)

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Sesshomaru, Naraku i Inuyasha należą do sekty Warring Era. Każdy
    członek tej sekty jest albo demonem, albo człowiekiem, albo i jednym
    i drugim. Żaden człowiek nie lubi deszczu, a wszystkie demony lubią
    śnieg. Naraku nie cierpi wszystkiego, co lubi Sesshomaru, a lubi
    wszystko czego nie lubi Sesshomaru. Sesshomaru lubi deszcz i śnieg.

    Wyraź opis powyższego tekstu w logice pierwszego rzędu. Czy jest
    ktoś, kto jest człowiekiem, ale nie jest demonem? Udowodnij, że
    twoja odpowiedź jest poprawna. *)

(* begin hide *)
Axioms
  (WarringEra : Type)
  (Sesshomaru Naraku Inuyasha : WarringEra)
  (isHuman isDemon : WarringEra -> Prop)
  (Thing : Type)
  (Rain Snow : Thing)
  (likes : WarringEra -> Thing -> Prop)
  (H0 : forall x : WarringEra,
    isHuman x \/ isDemon x \/ (isHuman x /\ isDemon x))
  (H1 : forall x : WarringEra, isHuman x -> ~ likes x Rain)
  (H2 : forall x : WarringEra, isDemon x -> likes x Snow)
  (H3 : forall x : Thing, likes Sesshomaru x -> ~ likes Naraku x)
  (H4 : forall x : Thing, ~ likes Sesshomaru x -> likes Naraku x)
  (H5 : likes Sesshomaru Rain)
  (H6 : likes Sesshomaru Snow).

Lemma isDemon_Sesshomaru :
  isDemon Sesshomaru.
Proof.
  elim: (H0 Sesshomaru) => [| [| []]];
  by try move/(@H1 _)/(_ H5) => [].
Qed.

Lemma isHuman_Naraku :
  isHuman Naraku.
Proof.
  elim: (H0 Naraku) => [| [| []]]; try done.
    by move/(@H2 _)/(H3 H6).
Qed.

Lemma not_isDemon_Naraku :
  ~ isDemon Naraku.
Proof.
  by move/H2/(H3 H6).
Qed.
(* end hide *)

(** * Ściąga (TODO) *)