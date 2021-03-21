CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A} _.
Arguments tl {A} _.

CoFixpoint zeros : Stream nat :=
{|
    hd := 0;
    tl := zeros;
|}.

Compute hd zeros. (* = 0 : nat *)
Compute hd (tl zeros). (* = 0 : nat *)
Compute hd (tl (tl zeros)). (* = 0 : nat *)

(** Zadanie: napisz funkcję `stake : forall A : Type, nat -> Stream A -> list A`, która bierze ze strumienia
    `n` pierwszych elementów i robi z nich listę. *)

(** Zadanie: zdefiniuj funkcję `smap : forall A B : Type, (A -> B) -> Stream A -> Stream B`. Domyśl się, co
    ma robić ta funkcja. *)

(** Zadanie: czy da się napisać funkcję `f : forall A : Type, list A -> Stream A`, która zamienia listę w
    strumień? *)

(** Zadanie: czy da się napisać funkcję `f : forall A : Type, Stream A -> list A`, która zamienia strumień
    w listę? *)

(** Zadanie: zdefiniuj typ `coList A`, który reprezentuje koinduktywne listy. Koinduktywna lista to coś takiego,
    że być może można z niej wyjąć głowę typu `A` i ogon, który też jest kolistą... a być może nie można
    nic wyjąć. *)