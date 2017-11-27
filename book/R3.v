(** * R3: Taktyki i automatyzacja *)

(** Matematycy uważają, że po osiągnięciu pewnego poziomu zaawansowania i
    obycia (nazywanego zazwyczaj "mathematical maturity") skrupulatne
    rozpisywanie każdego kroku dowodu przestaje mieć sens i pozwalają
    sobie zarzucić je na rzecz bardziej wysokopoziomowego opisu rozumowania.

    Myślę, że ta sytuacja ma miejsce w twoim przypadku — znasz już sporą
    część języka termów Coqa (zwanego Gallina) i potrafisz dowodzić różnych
    właściwości programów. Doszedłeś do punktu, w którym ręczne klepanie
    dowodów przestaje być produktywne, a staje się nudne i męczące.

    Niestety, natura dowodu formalnego nie pozwala nam od tak po prostu
    pominąć mało ciekawych kroków. Czy chcemy czy nie, aby Coq przyjął
    dowód, kroki te muszą zostać wykonane. Wcale nie znaczy to jednak,
    że to my musimy je wykonać — mogą zrobić to za nas programy.

    Te programy to oczywiście taktyki. Większość prymitywnych taktyk, jak
    [intro], [destruct], czy [assumption] już znamy. Choć nie wiesz o tym,
    używaliśmy też wielokrotnie taktyk całkiem zaawansowanych, takich jak
    [induction] czy [inversion], bez których nasze formalne życie byłoby
    drogą przez mękę.

    Wszystkie one są jednak taktykami wbudowanymi, danymi nam z góry przez
    Coqowych bogów i nie mamy wpływu na ich działanie. Jeżeli nie jesteśmy
    w stanie zrobić czegoś za ich pomocą, jesteśmy zgubieni. Czas najwyższy
    nauczyć się pisać własne taktyki, które pomogą nam wykonywać mało ciekawe
    kroki w dowodach, a w dalszej perspektywnie także przeprowadzać bardziej
    zaawansowane rozumowania zupełnie automatycznie.

    W tym rozdziale poznamy podstawy języka [Ltac], który służy do tworzenia
    własnych taktyk. Jego składnię przedstawiono i skrupulatnie opisano tu:
    https://coq.inria.fr/refman/ltac.html

    Choć przykład znaczy więcej niż 0x3E8 stron manuala i postaram się
    dokładnie zilustrować każdy istotny moim zdaniem konstrukt języka
    [Ltac], to i tak polecam zapoznać się z powyższym linkiem.

    Upewnij się też, że rozumiesz dokładnie, jak działają podstawowe
    kombinatory taktyk, które zostały omówione w rozdziale 1, gdyż nie
    będziemy omawiać ich drugi raz. *)

(** * Zarządzanie celami i selektory *)

(** Dowodząc (lub konstruując cokolwiek za pomocą taktyk) mamy do rozwiązania
    jeden lub więcej celów. Cele są ponumerowane i domyślnie zawsze pracujemy
    nad tym, który ma numer 1.

    Jednak wcale nie musi tak być — możemy zaznaczyć inny cel i zacząć nad
    nim pracować. Służy do tego komenda [Focus]. Cel o numerze n możemy
    zaznaczyć komendą [Focus n]. Jeżeli to zrobimy, wszystkie pozostałe cele
    chwilowo znikają. Do stanu domyślnego, w którym pracujemy nad celem nr 1
    i wszystkie cele są widoczne możemy wrócić za pomocą komendy [Unfocus]. *)

Goal forall P Q R : Prop, P /\ Q /\ R -> R /\ Q /\ P.
Proof.
  repeat split.
  Focus 3.
  Unfocus.
  Focus 2.
Abort.

(** Komenda [Focus] jest użyteczna głównie gdy któryś z dalszych celów jest
    łatwiejszy niż obecny. Możemy wtedy przełączyć się na niego, rozwiązać
    go i wyniesione stąd doświadczenie przenieść na trudniejsze cele. Jest
    wskazane, żeby po zakończeniu dowodu zrefaktoryzować go tak, aby komenda
    [Focus] w nim nie występowała.

    Nie jest też tak, że zawsze musimy pracować nad celem o numerze 1. Możemy
    pracować na dowolnym zbiorze celów. Do wybierania celów, na które chcemy
    zadziałać taktykami, służą selektory. Jest ich kilka i mają taką składnię:
    - [n: t] — użyj taktyki t na n-tym celu. [1: t] jest równoważne [t].
    - [a-b: t] — użyj taktyki t na wszystkich celach o numerach od a do b
    - [a1-b1, a2-b2, ..., aN-bN: t] — użyj taktyki [t] na wszystkich celach
      o numerach od a1 do b1, od a2 do b2, ..., od aN do bN (zamiast aK-bK
      możemy też użyć pojedynczej liczby)
    - [all: t] ­- użyj [t] na wszystkich celach *)

Goal forall P Q R : Prop, P /\ Q /\ R -> R /\ Q /\ P.
Proof.
  destruct 1 as [H [H' H'']]. repeat split.
  3: assumption. 2: assumption. 1: assumption.
Restart.
  destruct 1 as [H [H' H'']]. repeat split.
  1-2: assumption. assumption.
Restart.
  destruct 1 as [H [H' H'']]. repeat split.
  1-2, 3: assumption.
Restart.
  destruct 1 as [H [H' H'']]. repeat split.
  all: assumption.
Qed.

(** Selektory przydają się głównie gdy chcemy napisać taktykę rozwiązującą
    wszystkie cele i sprawdzamy jej działanie na każdym celu z osobna. *)

Goal True /\ True.
Proof.
  split.
  let n := numgoals in idtac n.
  all: let n := numgoals in idtac n.
Abort.

(** Ilość celów możemy policzyć za pomocą taktyki [numgoals]. Liczy ona
    wszystkie cele, na które działa, więc jeżeli nie użyjemy żadnego
    selektora, zwróci ona 1. Nie jest ona zbyt użyteczna (poza bardzo
    skomplikowanymi taktykami, które z jakichś powodów nie operują tylko na
    jednym celu, lecz na wszystkich).

    Z wiązaniem [let] w kontekście taktyk spotkamy się już niedługo. *)

(** * Podstawowe rodzaje bytów *)

(** * Backtracking *)

Ltac existNatFrom n :=
  exists n || existNatFrom (S n).

Ltac existNat := existNatFrom O.

Goal exists m, m = 1.
  Fail (existNat; reflexivity).
Abort.

Ltac existNatFrom' n :=
  exists n + existNatFrom' (S n).

Ltac existNat' := existNatFrom' O.

Goal exists m, m = 15.
  existNat'; reflexivity.
Qed.

(** * Dopasowanie celu *)

(** * Dopasowanie termu *)

(** * Inne wesołe rzeczy *)

(* begin hide *)

(** * Ltac — język taktyk *)
Require Import Bool.

Theorem andb_dist_orb : forall b1 b2 b3 : bool,
    b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof.
  destruct b1, b2, b3; simpl; reflexivity.
Qed.

(** Powyższe twierdzenie mówi, że koniunkcja boolowska jest rozdzielna
    względem alternatywy boolowskiej, ale dużo ważniejszy jest jego
    dowód. Myślę, że dostrzegasz już pewien schemat, jeżeli chodzi
    o dowodzenie właściwości funkcji boolowskich: sprowadza się to
    do rozbicia zmiennych na przypadki i obliczenia funkcji, w wyniku
    czego, jeżeli twierdzenie rzeczywiście jest prawdziwe, dostajemy
    pewną ilość tryiwalnych równości. *)

(** Gdybyśmy chcieli zdefiniować więcej funkcji boolowskich i dowodzić
    ich właściwości, moglibyśmy po prostu kopiować dowody i ewentualnie
    przystosowywać je do
    ilości występujących w twierdzeniach zmiennych boolowskich. Nie
    jest to jednak dobry pomysł. Tak jak programista nie powinien
    kopiować fragmentów kodu i wklejać ich gdzie indziej, tak też
    matematyk nie powinien kopiować i wklejać fragmentów dowodów.
    Programista dysponuje narzędziem, które pozwala mu tego uniknąć
    — jest nim możliwość pisania własnych funkcji/procedur, które
    pozwalają nadać kawałkowi kodu nazwę i odwoływać się do niego
    przy jej użyciu. Podobnym narzędziem dysponuje matematyk dowodzący
    w Coqu — jest nim możliwość pisania własnych taktyk w języku [Ltac].
    Dotychczas spotkaliśmy jedynie taktyki standardowe, jak [intro]
    czy [destruct], teraz zaś dowiemy się, jak pisać własne. *)

Ltac solve_bool := intros;
match goal with
    | b : bool |- _ => destruct b; solve_bool
    | _ => simpl; reflexivity
end.

Ltac solve_bool2 :=
match goal with
    | |- forall b : bool, _ => destruct b; solve_bool2
    | _ => simpl; reflexivity
end.

(** Definicje taktyk zaczynają się od słowa kluczowego [Ltac].
    W ciele definicji możemy używać taktyk oraz konstruktu
    [match goal with], który próbuje dopasować kontekst oraz
    cel do podanych niżej wzorców. Mają one postać
    [| kontekst |- cel => taktyka] lub podkreślnika,
    który oznacza "dopasuj cokolwiek". *)

(** Wyrażenie [kontekst] jest
    listą hipotez/wartości, których szukany w kontekście, tzn.
    jest postaci [x1 : A1, x2 : A2...], gdzie [A1] oznacza typ
    pierwszej wartości/hipotezy, a [x1] oznacza nazwę, którą
    nadajemy jej na potrzeby naszej taktyki (nie musi być ona
    taka sama jak rzeczywista nazwa występująca w twierdzeniu
    — możemy ją np. pominąć, używając podkreślnika [_]). *)

(** Wyrażenie [cel] jest typem, który reprezentuje dany cel,
    np. gdybyśmy szukali celów będących równościami, moglibyśmy
    jako [cel] podać wzorzec [_ = _]. *)

(** Po strzałce [=>] następuje nazwa taktyki, której chcemy
    użyć w danym przypadku. Ponieważ możemy użyć tylko jednej,
    zazwyczaj będziemy budować ją z wielu kombinatorów. *)

(** W naszym przypadku taktykę możemy podsumować tak:
    - wprowadź zmienne do kontekstu ([intros])
    - dopasuj cel i kontekst do podanych wzorców ([match goal with])
      - jeżeli w kontekście jest wartość typu [bool], nazwij ją [b],
        rozbij ją, a następnie wywołaj się rekurencyjnie
        ([| b : bool |- _ => destruct b; solve_bool])
      - w przeciwnym przypadku uprość cel i udowodnij trywialne
        równości ([| _ => simpl; reflexivity]) *)

Theorem andb_dist_orb' : forall b1 b2 b3 : bool,
    b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof.
  solve_bool.
Restart.
  solve_bool2.
Qed.

Theorem not_true : forall b1 b2 : bool,
    b1 && b2 = b1 || b2.
Proof.
  try solve_bool.
Abort.

(** Jak widzimy, napisana przez nas taktyka nie jest magiczna
    i nie potrafi udowodnić nieprawdziwego twierdzenia. *)

(** * Automatyzacja *)

Hypotheses A B C D E F G H I J : Prop.

(** * Wyszukiwanie *)

Ltac search := try assumption; (left; search) + (right; search).

Theorem search_0 :
    I -> A \/ B \/ C \/ D \/ E \/ F \/ G \/ I \/ J.
Proof. search. Qed.

Theorem search_1 :
    I -> (((((((A \/ B) \/ C) \/ D) \/ E) \/ F) \/ G) \/ I) \/ J.
Proof. search. Qed.

Theorem search_2 :
    F -> (A \/ B) \/ (C \/ ((D \/ E \/ (F \/ G)) \/ H) \/ I) \/ J.
Proof. search. Qed.

Theorem search_3 :
    C -> (J \/ J \/ ((A \/ A \/ (C \/ D \/ (E \/ E))))).
Proof. search. Qed.

Theorem search_4 :
    A -> A \/ B \/ C \/ D \/ E \/ F \/ G \/ I \/ J.
Proof. search. Qed.

Theorem search_5 :
    D -> ~A \/ ((~B \/ (I -> I) \/ (J -> J)) \/ (D \/ (~D -> ~~D) \/ B \/ B)).
Proof. search. Qed.

Theorem search_6 :
    C -> (~~C /\ ~~~C) \/ ((C /\ ~C) \/ (~C /\ C) \/ (C -> C) \/ (C \/ ~C)).
Proof. search. Qed.

(** * Porządki *)

Ltac destr := intros; repeat
match goal with
    | H : _ /\ _ |- _ => destruct H
end; try assumption.

Theorem destruct_0 :
    A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J -> D.
Proof. destr. Qed.

Theorem destruct_1 :
    ((((((((A /\ B) /\ C) /\ D) /\ E) /\ F) /\ G) /\ H) /\ I) /\ J -> F.
Proof. destr. Qed.

Theorem destruct_2 :
    A /\ ~B /\ (C \/ C \/ C \/ C) /\ ((((D /\ I) /\ I) /\ I) /\ J) -> I.
Proof. destr. Qed.

(** Permutacje koniunktywe. *)

Ltac solve_and_perm := intros; repeat
match goal with
    | H : _ /\ _ |- _ => destruct H
end; repeat split; try assumption.

Theorem and_perm_0 : A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J ->
    J /\ I /\ H /\ G /\ F /\ E /\ D /\ C /\ B /\ A.
Proof. solve_and_perm. Qed.

Theorem and_perm_1 : A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J ->
    (((((((((A /\ B) /\ C) /\ D) /\ E) /\ F) /\ G) /\ H) /\ I) /\ J).
Proof. solve_and_perm. Qed.

Theorem and_perm_2 :
  (A /\ B) /\ (C /\ (D /\ E)) /\ (((F /\ G) /\ H) /\ I) /\ J ->
  (I /\ I /\ J) /\ ((A /\ B /\ (A /\ B)) /\ J) /\ (C /\ (E /\ (D /\ F /\ F))).
Proof. solve_and_perm. Qed.

(** Permutacje dysjunktywne. *)

(** Wskazówka: wykorzystaj taktykę search z ćw. 1 *)

Ltac solve_or_perm := intros; repeat
match goal with
    | H : _ \/ _ |- _ => destruct H
end; search.

Theorem or_perm : A \/ B \/ C \/ D \/ E \/ F \/ G \/ H \/ I \/ J ->
    (((((((((A \/ B) \/ C) \/ D) \/ E) \/ F) \/ G) \/ H) \/ I) \/ J).
Proof. solve_or_perm. Qed.

(** * Negacja *)

Fixpoint negn (n : nat) (P : Prop) : Prop :=
match n with
    | 0 => P
    | S n' => ~ negn n' P
end.

Eval simpl in negn 30.

Theorem dbl_neg : A -> ~~A.
Proof. unfold not. auto. Qed.

Ltac negtac := simpl; unfold not; intros;
match reverse goal with
    | H : _ -> False |- False => apply H; clear H; negtac
    | _ => try assumption
end.

Theorem neg_2_14 : negn 2 A -> negn 14 A.
Proof. negtac. Qed.

Theorem neg_100_200 : negn 100 A -> negn 200 A.
Proof. negtac. Qed.

Theorem neg_42_1000 : negn 42 A -> negn 200 A.
Proof. negtac. Qed.
(* end hide *)