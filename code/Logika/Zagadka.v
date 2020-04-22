Definition Classically (A : Type) : Type :=
  (forall P : Prop, P \/ ~ P) -> A.

Notation "f $ x" := (f x) (at level 100, only parsing).

Ltac cls := progress unfold Classically; intro LEM.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Sesshomaru, Naraku i Inuyasha należą do sekty Warring Era. Każdy członek
    tej sekty jest albo demonem, albo człowiekiem, albo i jednym i drugim.
    Żaden człowiek nie lubi deszczu, a wszystkie demony lubią śnieg. Naraku
    nie cierpi wszystkiego, co lubi Sesshomaru, a lubi wszystko czego nie
    lubi Sesshomaru. Sesshomaru lubi deszcz i śnieg.

    Wyraź opis powyższego tekstu w logice pierwszego rzędu. Czy jest ktoś,
    kto jest człowiekiem, ale nie jest demonem? Udowodnij, że twoja odpowiedź
    jest poprawna. *)

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