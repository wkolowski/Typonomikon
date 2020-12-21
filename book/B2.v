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

(** https://github.com/wkolowski/CoqBookPL/blob/master/txt/równość.md *)

(* begin hide *)
(*
TODO 1: Opisać związki rodzajów równości ze składnią i semantyką
        (empiryczna obserwacja: studenci pierwszego roku nie są
        zbyt płynni w posługiwaniu się składnią _in abstracto_).
TODO 2: Pomysł na jeszcze jeden podrozdział, semantyka vs składnia
TODO 3: Użyć nominalizmów do wytłumaczenia wiązania nazw zmiennych.
*)
(* end hide *)

(** * Predykatywizm (TODO) *)

(** * Esencjalizm vs strukturalizm *)

(* begin hide *)
(* TODO: tutaj opisać impredykatywne definicje spójników *)
(* end hide *)

(** * Paradoks golibrody *)

(** Języki naturalne, jakimi ludzie posługują się w życiu codziennym
    (polski, angielski suahili, język indian Navajo) zawierają spory
    zestaw spójników oraz kwantyfikatorów ("i", "a", "oraz", "lub",
    "albo", "jeżeli ... to", "pod warunkiem, że ", "wtedy", i wiele
    innych).

    Należy z całą stanowczością zaznaczyć, że te spójniki i kwantyfikatory,
    a w szczególności ich intuicyjna interpretacja, znacznie różnią się
    od analogicznych spójników i kwantyfikatorów logicznych, które mieliśmy
    okazję poznać w tym rozdziale. Żeby to sobie uświadomić, zapoznamy się
    z pewnego rodzaju "paradoksem". *)

Theorem barbers_paradox :
  forall (man : Type) (barber : man)
    (shaves : man -> man -> Prop),
      (forall x : man, shaves barber x <-> ~ shaves x x) -> False.
(* begin hide *)
Proof.
  intros. destruct (H barber). apply H0.
    apply H1. intro. apply H0; assumption.
    apply H1. intro. apply H0; assumption.
Qed.
(* end hide *)

(** Twierdzenie to formułowane jest zazwyczaj tak: nie istnieje człowiek,
    który goli wszystkich tych (i tylko tych), którzy sami siebie nie golą.

    Ale cóż takiego znaczy to przedziwne zdanie? Czy matematyka dają nam
    magiczną, aprioryczną wiedzę o fryzjerach?

    Odczytajmy je poetycko. Wyobraźmy sobie pewne miasteczko. Typ [man]
    będzie reprezentował jego mieszkańców. Niech term [barber] typu [man]
    oznacza hipotetycznego golibrodę. Hipotetycznego, gdyż samo użycie
    jakiejś nazwy nie powoduje automatycznie, że nazywany obiekt istnieje
    (przykładów jest masa, np. jednorożce, sprawiedliwość społeczna).

    Mamy też relację [shaves]. Będziemy ją interpretować w ten sposób, że
    [shaves a b] zachodzi, gdy [a] goli brodę [b]. Nasza hipoteza
    [forall x : man, shaves barber x <-> ~ shaves x x] jest zawoalowanym
    sposobem podania następującej definicji: golibrodą nazwiemy te osoby,
    który golą wszystkie te i tylko te osoby, które same siebie nie golą.

    Póki co sytuacja rozwija się w całkiem niekontrowersyjny sposób. Żeby
    zburzyć tę sielankę, możemy zadać sobie następujące pytanie: czy
    golibroda rzeczywiście istnieje? Dziwne to pytanie, gdy na każdym
    rogu ulicy można spotkać fryzjera, ale nie dajmy się zwieść.

    W myśl rzymskich sentencji "quis custodiet ipsos custodes?" ("kto będzie
    pilnował strażników?") oraz "medice, cure te ipsum!" ("lekarzu, wylecz
    sam siebie!") możemy zadać dużo bardziej konkretne pytanie: kto goli
    brody golibrody? A idąc jeszcze krok dalej: czy golibroda goli sam siebie?

    Rozstrzygnięcie jest banalne i wynika wprost z definicji: jeśli golibroda
    ([barber]) to ten, kto goli ([shaves barber x]) wszystkich tych i tylko
    tych ([forall x : man]), którzy sami siebie nie golą ([~ shaves x x]), to
    podstawiając [barber] za [x] otrzymujemy sprzeczność: [shaves barber
    barber] zachodzi wtedy i tylko wtedy, gdy [~ shaves barber barber].

    Tak więc golibroda, zupełnie jak Święty Mikołaj, nie istnieje. Zdanie to
    nie ma jednak wiele wspólnego ze światem rzeczywistym: wynika ono jedynie
    z takiej a nie innej, przyjętej przez nas całkowicie arbitralnie definicji
    słowa "golibroda". Można to łatwo zobrazować, przeformułowywując powyższe
    twierdzenie z użyciem innych nazw: *)

Lemma barbers_paradox' :
  forall (A : Type) (x : A) (P : A -> A -> Prop),
    (forall y : A, P x y <-> ~ P y y) -> False.
(* begin hide *)
Proof.
  intros. destruct (H x). apply H0.
    apply H1. intro. apply H0; assumption.
    apply H1. intro. apply H0; assumption.
Qed.
(* end hide *)

(** Nieistnienie "golibrody" i pokrewny mu paradoks pytania "czy golibroda
    goli sam siebie?" jest konsekwencją wyłącznie formy powyższego zdania
    logicznego i nie mówi nic o rzeczywistoświatych golibrodach.

    Paradoksalność całego "paradoksu" bierze się z tego, że typom, zmiennym
    i relacjom specjalnie nadano takie nazwy, żeby zwykły człowiek bez
    głębszych dywagacji nad definicją słowa "golibroda" przjął, że golibroda
    istnieje. Robiąc tak, wpada w sidła pułapki zastawionej przez logika i
    zostaje trafiony paradoksalną konkluzją: golibroda nie istnieje. *)

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