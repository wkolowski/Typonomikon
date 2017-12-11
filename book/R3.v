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
    - [all: t] ­- użyj [t] na wszystkich celach
    - zamiast [t], w powyższych przypadkach możemy też użyć wyrażenia
      [> t_1 | ... | t_n], które aplikuje taktykę [t_i] do i-tego celu
      zaznaczonego danym selektorem *)

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
Restart.
  destruct 1 as [H [H' H'']]. repeat split.
  all: [> assumption | assumption | assumption].  
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

(** * Podstawy języka Ltac *)

(** Ltac jest funkcyjnym językiem programowania, podobnie jak język termów
    Coqa (zwany Gallina), lecz te dwa języki są diametralnie różne:
    - Ltac jest kompletny w sensie Turinga, a Gallina nie. W szczególności,
      taktyki mogą się zapętlać i nie rodzi to żadnych problemów natury
      logicznej.
    - Ltac jest bardzo słabo typowany, podczas gdy Gallina dysponuje potężnym
      systemem typów.
    - W Ltacu nie możemy definiować typów danych, a jedynie taktyki działające
      na kontekstach i celu, podczas gdy Gallina pozwala na definiowanie
      bardzo szerokiej klasy typów i działających na nich funkcji.
    - Ltac, jako metajęzyk jezyka Gallina, posiada dostęp do różnych rzeczy,
      do których Gallina nie ma dostępu, takich jak dopasowanie termów
      dowolnego typu. Dla przykładu, w Ltacu możemy odróżnić termy [4] oraz
      [2 + 2] pomimo tego, że są konwertowalne. *)

(** W Ltacu możemy manipulować trzema rodzajami bytów: taktykami, termami
    Coqa oraz liczbami całkowitymi — te ostatnie nie są tym samym, co liczby
    całkowite Coqa i będziemy ich używać sporadycznie. Zanim zobaczymy
    przykład, przyjrzyjmy się taktyce [pose] oraz konstruktowi [let]. *)

Goal True.
Proof.
  pose true.
  pose (nazwa := 123).
Abort.

(** [pose t] dodaje do kontekstu term o domyślnej nazwie, którego ciałem
    jest [t]. Możemy też napisać [pose x := t], dzięki czemu zyskujemy
    kontrolę nad nazwą termu. *)

Goal True.
Proof.
  Fail let x := 42 in pose x.
  let x := constr:(42) in pose x.
  let x := auto in idtac x.
Abort.

(** W Ltacu, podobnie jak w języku Gallina, mamy do dyspozycji konstrukt
    [let]. Za jego pomocą możemy nadać nazwę dowolnemu wyrażeniu języka
    Ltac. Jego działanie jest podobne jak w języku Gallina, a więc nie
    ma co się nad nim rozwodzić. Jest też konstrukt [let rec], który
    odpowiada [fix]owi Galliny.

    Spróbujmy dodać do kontekstu liczbę [42], nazwaną dowolnie. Komendą
    [let x := 42 in pose x] nie udaje nam się tego osiągnąć. O przyczynie
    niepowodzenia Coq informuje nas wprost: zmienna [x] nie jest termem.
    Czym zatem jest? Jak już się rzekło, Ltac posiada wbudowany typ liczb
    całkowitych, które nie są tym samym, co induktywnie zdefiniowane liczby
    całkowite Coqa. W tym kontekście [42] jest więc liczbą całkowitą Ltaca,
    a zatem nie jest termem.

    Aby wymusić na Ltacu zinterpretowanie [42] jako termu Coqa, musimy
    posłużyć się zapisem [constr:()]. Dzięki niemu argument znajdujący
    się w nawiasach zostanie zinterpretowany jako term. Efektem działania
    drugiej taktyki jest więc dodanie termu [42 : nat] do kontekstu,
    nazwanego domyślnie [n] (co jest, o dziwo, dość rozsądną nazwą).

    Wyrażenie [let x := auto in idtac x] pokazuje nam, że taktyki również
    są wyrażeniami Ltaca i mogą być przypisywane do zmiennych (a także
    wyświetlane za pomocą taktyki [idtac]) tak jak każde inne wyrażenie. *)

Ltac garbage n :=
  pose n; idtac "Here's some garbage: " n.

Goal True.
Proof.
  garbage 0.
Abort.

Ltac garbage' :=
  fun n => pose n; idtac "Here's some garbage: " n.

Goal True.
Proof.
  garbage' 0.
Abort.

(** Dowolną taktykę, której możemy użyć w dowodzie, możemy też nazwać
    za pomocą komendy [Ltac] i odwoływać się do niej w dowodach za pomocą
    tej nazwy. Komenda [Ltac] jest więc taktykowym odpowiednikiem komendy
    [Fixpoint].

    Podobnie jak [Fixpoint]y i inne definicje, tak i taktyki zdefiniowane
    za pomocą komendy [Ltac] mogą brać argumenty, którymi mogą być liczby,
    termy, nazwy hipotez albo inne taktyki.

    Zapis [Ltac name arg_1 ... arg_n := body] jest jedynie skrótem, który
    oznacza [Ltac name := fun arg_1 ... arg_n => body]. Jest to uwaga
    mocno techniczna, gdyż pierwszy zapis jest prawie zawsze preferowany
    wobec drugiego. *)

(** * Backtracking *)

(** Poznałeś już kombinator alternatywy [||]. Nie jest to jednak jedyny
    kombinator służący do wyrażania tej idei — są jeszcze kombinatory [+]
    oraz [tryif t1 then t2 else t3]. Różnią się one działaniem — [||] jest
    left-biased, podczas gdy [+] nie jest biased i może powodować
    backtracking.

    Nie przestrasz się tych dziwnych słów. Stojące za nimi idee są z grubsza
    bardzo proste. Wcześniej dowiedziałeś się, że taktyka może zawieść lub
    zakończyć się sukcesem. W rzeczywistości sprawa jest nieco bardziej
    ogólna: każda taktyka może zakończyć się dowolną ilością sukcesów. Zero
    sukcesów oznacza, że taktyka zawodzi. Większość taktyk, które dotychczas
    poznaliśmy, mogła zakończyć się co najwyżej jednym sukcesem. Są jednak i
    takie, które mogą zakończyć się dwoma lub więcej sukcesami.

    Proces dowodzenia za pomocą taktyk można zobrazować za pomocą procesu
    przeszukiwania drzewa, którego wierzchołkami są częściowo skonstruowane
    prooftermy, zaś krawędziami — sukcesy pochodzące od wywoływania taktyk.
    Liśćmi są prooftermy (dowód się udał) lub ślepe zaułki (dowód się nie
    udał).

    W takiej wizualizacji taktyka może wyzwalać backtracking, jeżeli jej
    użycie prowadzi do powstania rozgałęzienia w drzewie. Samo drzewo
    przeszukiwane jest w głąb, a backtracking polega na tym, że jeżeli
    trafimy na ślepy zaułek (dowód się nie powiódł), to cofamy się (ang.
    "to backtrack" — cofać się) do ostatniego punktu rozgałęzienia i
    próbujemy pójść inną gałęzią.

    Tę intuicję dobrze widać na poniższym przykładzie. *)

Ltac existsNatFrom n :=
  exists n || existsNatFrom (S n).

Ltac existsNat := existsNatFrom O.

Goal exists n : nat, n = 42.
Proof.
  Fail (existsNat; reflexivity).
Abort.

Ltac existsNatFrom' n :=
  exists n + existsNatFrom' (S n).

Ltac existsNat' := existsNatFrom' O.

Goal exists n : nat, n = 42.
Proof.
  existsNat'; reflexivity.
Qed.

(** Próba użycia taktyki [existsNat], która używa kombinatora [||], do
    udowodnienia, że [exists n : nat, n = 42] kończy się niepowodzeniem.
    Jest tak, gdyż [||] nie może powodować backtrackingu — jeżeli taktyka
    [t1] dokona postępu, to wtedy [t1 || t2] ma taki sam efekt, jak [t1],
    a w przeciwnym wypadku taki sam jak [t2]. Nawet jeżeli zarówno [t1]
    jak i [t2] zakończą się sukcesami, to sukcesy [t1 || t2] będą sukcesami
    tylko [t1].

    Na mocy powyższych rozważań możemy skonkludować, że taktyka [existsNat]
    ma co najwyżej jeden sukces i działa jak [exists n] dla pewnej liczby
    naturalnej [n]. Ponieważ użycie [exists 0] na celu [exists n : nat, n = 42]
    dokonuje postępu, to taktyka [existsNat] ma taki sam efekt, jak [exists 0].
    Próba użycia [reflexivity] zawodzi, a ponieważ nie ma już więcej sukcesów
    pochodzących od [existsNat] do wypróbowania, nie wyzwala backtrackingu.
    Wobec tego cała taktyka [existsNat; reflexivity] kończy się porażką.

    Inaczej sytuacja wygląda w przypadku [existsNat'], która bazuje na
    kombinatorze [+]. Sukcesy [t1 + t2] to wszystkie sukcesy [t1], po
    których następują wszystkie sukcesy [t2]. Wobec tego zbiór sukcesów
    [existsNat'] jest nieskończony i wygląda tak: [exists 0], [exists 1],
    [exists 2]... Użycie taktyki [reflexivity], które kończy się porażką
    wyzwala backtracking, więc całe wykonanie taktyki można zobrazować tak:
    - [exists 0; reflexivity] — porażka
    - [exists 1; reflexivity] — porażka
    - ...
    - [exists 42; reflexivity] — sukces *)

(** Na koniec zaznaczyć należy, że backtracking nie jest za darmo — im go
    więcej, tym więcej rozgałęzień w naszym drzewie poszukiwań, a zatem
    tym więcej czasu zajmie wykonanie taktyki. W przypadku użycia taktyk
    takich jak [existsNat], które mają nieskończony zbiór sukcesów, dowód
    może nie zostać znaleziony nigdy, nawet jeżeli istnieje.

    Jednym ze sposobów radzenia sobie z tym problemem może być kombinator
    [once], który ogranicza liczbę sukcesów taktyki do co najwyżej jednego,
    zapobiegając w ten sposób potencjalnemu wyzwoleniu backtrackingu. Innymi
    słowy, [once t] zawsze ma 0 lub 1 sukcesów. *)

Goal exists n : nat, n = 42.
Proof.
  Fail once existsNat'; reflexivity.
Abort.

(** Powyżej byliśmy w stanie udowodnić to twierdzenie za pomocą taktyki
    [existsNat'], gdyż jej 42  sukces pozwalał taktyce [reflexivity]
    uporać się z celem. Jednak jeżeli użyjemy na tej taktyce kombinatora
    [once], to zbiór jej sukcesów zostanie obcięty do co najwyżej jednego

    Skoro [existsNat'] było równoważne któremuś z [exists 0], [exists 1],
    [exists 2], ..., to [once existsNat'] jest równoważne [exists 0], a
    zatem zawodzi.

    Innym sposobem okiełznywania backtrackingu jest kombinator [exactly_once],
    który pozwala upewnić się, że dana taktyka ma dokładnie jeden sukces.
    Jeżeli [t] zawodzi, to [exactly_once t] zawodzi tak jak [t]. Jeżeli [t]
    ma jeden sukces, [exactly_once t] działa tak jak [t]. Jeżeli [t] ma dwa
    lub więcej sukcesów, [exactly_once t] zawodzi. *)

Goal exists n : nat, n = 42.
Proof.
  exactly_once existsNat.
Restart.
  Fail exactly_once existsNat'.
Abort.

(** Taktyka [existsNat], zrobiona kombinatorem alternatywy [||], ma dokładnie
    jeden sukces, a więc [exactly_once existsNat] działa tak jak [existsNat].
    Z drugiej strony taktyka [existsNat'], zrobiona mogącym dokonywać nawrotów
    kombinatorem alternatywy [+], ma wiele sukcesów i wobec tego
    [exactly_once existsNat'] zawodzi. *)

(** **** Ćwiczenie *)

(** Przepisz taktykę [existsNat'] za pomocą konstruktu [let rec] —
    całość ma wyglądać tak: [Ltac existsNat'' := let rec ...] *)

(* begin hide *)
Ltac existsNat'' :=
  let rec f n := exists n + f (n + 1) in f 0.
(* end hide *)

Goal exists n : nat, n = 42.
Proof.
  existsNat''; reflexivity.
Qed.

(** **** Ćwiczenie *)

(** Udowodnij poniższe twierdzenie za pomocą pojedynczej taktyki, która
    generuje wszystkie możliwe listy wartości boolowskich. Całość zrób za
    pomocą konstruktu [let rec] w miejscu, tj. bez użycia komendy [Ltac]. *)

Require Import List.
Import ListNotations.

Goal exists l : list bool, length l = 3.
(* begin hide *)
Proof.
  let rec
    f l := exists l + f (true :: l) + f (false :: l)
  in f (@nil bool); reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Znajdź taki trywialnie prawdziwy cel i taką taktykę, która wywołuje
    [existsNat'], że taktyka ta nie skończy pracy i nigdy nie znajdzie
    dowodu, mimo że dla człowieka znalezienie dowodu jest banalne. *)

(* begin hide *)
Goal (exists n : nat, n = S n) \/ True.
Proof.
  Fail Timeout 1 (left; existsNat'; reflexivity) + (right; trivial).
Abort.
(* end hide *)

(** **** Ćwiczenie *)

(** Napisz taktykę [search], która potrafi udowodnić poniższe twierdzenia.
    Użyj rekursji, ale nie używaj konstruktu [let rec]. *)

Section search.

Hypotheses A B C D E F G H I J : Prop.

(* begin hide *)
Ltac search := try assumption; (left; search) + (right; search).
(* end hide *)

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

End search.

(** **** Ćwiczenie *)

(** Zbadaj samodzielnie na podstawie dokumentacji, jak działa kombinator
    [tryif t1 then t2 else t3]. Wymyśl jakiś mądry przykład, który dobrze
    ukazuje jego działanie w kontraście do [||] i [+]. *)

(** * Dopasowanie kontekstu i celu *)

(** Chyba najważniejszym konstruktem Ltaca jest [match goal], który próbuje
    dopasować kontekst oraz cel do podanych wzorców. Mają one postać
    [| kontekst |- cel => taktyka].

    Wyrażenie [kontekst] jest listą hipotez, których szukamy w kontekście,
    tzn. jest postaci [x_1 : A_1, x_2 : A_2...], gdzie [x_i] jest nazwą
    hipotezy, zaś [A_1] jest wzorcem dopasowującym jej typ. Wyrażenie [cel]
    jest wzorcem dopasowującym typ, który reprezentuje nasz cel. Po strzałce
    [=>] następuje taktyka, której chcemy użyć, jeżeli dany wzorzec zostanie
    dopasowany.

    Zamiast wzorców postaci [| kontekst |- cel => taktyka] możemy też używać
    wzorców postaci [| |- cel => taktyka], które dopasowują jedynie cel, zaś
    kontekst ignorują; wzorców postac [| kontekst |- _ => taktyka], które
    dopasowują jedynie kontekst, a cel ignorują; oraz wzorca [_], który
    oznacza "dopasuj cokolwiek".

    Zobaczmy, jak to wygląda na przykładach. *)

Section Match.

Goal
  forall P Q R S : Prop, P -> Q -> R -> S.
Proof.
  intros.
  match goal with
      | x : Prop |- _ => idtac x
  end.
Abort.

(** W powyższym przykładzie szukamy w celu zdań logicznych, czyli termów
    typu [Prop] i wypisujemy je. Nazwy szukanych obiektów są lokalne dla
    każdej gałęzi dopasowania i nie muszą pokrywać się z rzeczywistymi
    nazwami termów w kontekście. W naszym przypadku nazywamy szukane przez
    nas zdanie [x], choć zdania obecne w naszym kontekście tak naprawdę
    nazywają się [P], [Q], [R] oraz [S].

    Przeszukiwanie obiektów w kontekście odbywa się w kolejności od
    najnowszego do najstarszego. Do wzorca [x : Prop] najpierw próbujemy
    dopasować [H1 : R], ale [R] to nie [Prop], więc dopasowanie zawodzi.
    Podobnie dla [H0 : Q] oraz [H : P]. Następnie natrafiamy na [S : Prop],
    które pasuje do wzorca. Dzięki temu na prawo od strzałki [=>] nazwa [x]
    odnosi się do dopasowanego zdania [S]. Za pomocą taktyki [idtac x]
    wyświetlamy [x] i faktycznie odnosi się on do [S]. Po skutecznym
    dopasowaniu i wykonaniu taktyki [idtac x] cały [match] kończy się
    sukcesem. *)

Goal
  forall P Q R S : Prop, P -> Q -> R -> S.
Proof.
  intros.
  Fail match goal with
      | x : Prop |- _ => idtac x; fail
  end.
Abort.

(** W tym przykładzie podobnie jak wyżej szukamy w kontekście zdań logicznych,
    ale taktyka po prawej od [=>] zawodzi. [match] działa tutaj następująco:
    - próbujemy do wzorca [x : Prop] dopasować [H1 : R], ale bez powodzenia
      i podobnie dla [H0 : Q] oraz [H : P].
    - znajdujemy dopasowanie [S : Prop]. Taktyka [idtac x] wypisuje do okna
      Messages wiadomość "S" i kończy się sukcesem, ale [fail] zawodzi.
    - Wobec powyższego próbujemy kolejnego dopasowania, tym razem [R : Prop],
      które pasuje. [idtac x] wypisuje na ekran "R", ale [fail] znów
      zawodzi.
    - Próbujemy kolejno dopasowań [Q : Prop] i [P : Prop], w wyniku których
      wypisane zostaje "Q" oraz "P", ale również w tych dwóch przypadkach
      taktyka [fail] zawodzi.
    - Nie ma więcej potencjalnych dopasowań, więc cały [match] zawodzi. *)

Goal
  forall P Q R S : Prop, P -> Q -> R -> S.
Proof.
  intros.
  Fail match reverse goal with
      | x : Prop |- _ => idtac x; fail
  end.
Abort.

(** Ten przykład jest podobny do ostatniego, ale [match reverse] przeszukuje
    kontekst w kolejności od najstarszego do najnowszego. Dzięki temu od razu
    natrafiamy na dopasowanie [P : Prop], potem na [Q : Prop] etc. Na samym
    końcu próbujemy do [x : Prop] dopasować [H : P], [H0 : Q] i [H1 : R], co
    kończy się niepowodzeniem.

    Zauważmy, że w dwóch ostatnich przykładach nie wystąpił backtracking —
    [match] nigdy nie wyzwala backtrackingu. Obserwowane działanie [match]a
    wynika stąd, że jeżeli taktyka po prawej od [=>] zawiedzie, to następuje
    próba znalezienia jakiegoś innego dopasowania wzorca [x : Prop]. Dopiero
    gdy taktyka na prawo od [=>] zawiedzie dla wszystkich możliwych takich
    dopasowań, cały [match] zawodzi. *)

Goal
  forall P Q R S : Prop, P -> Q -> R -> S.
Proof.
  intros.
  Fail
  match goal with
      | x : Prop |- _ => idtac x
  end; fail.
Abort.

(** Ten przykład potwierdza naszą powyższą obserwację dotyczącą backtrackingu.
    Mamy tutaj identyczne dopasowanie jak w pierwszym przykładzie — wypisuje
    ono [S] i kończy się sukcesem, ale tuż po nim następuje taktyka [fail],
    przez co cała taktyka [match ...; fail] zawodzi. Jak widać, nie następuje
    próba ponownego dopasownia wzorca [x : Prop]. *)

Goal
  forall P Q R S : Prop, P -> Q -> R -> S.
Proof.
  intros.
  Fail
  lazymatch goal with
      | x : Prop |- _ => idtac x; fail
  end.
Abort.

(** Konstrukt [lazymatch] różni się od [match]a tym, że jeżeli taktyka na
    prawo od [=>] zawiedzie, to alternatywne dopasowania wzorca po lewej
    nie będą rozważane i nastąpi przejście do kolejnej gałęzi dopasowania.
    W naszym przypadku nie ma kolejnych gałęzi, więc po pierwszym dopasowaniu
    [x : Prop] do [S : Prop] i wypisaniu "S" cały [lazymatch] zawodzi. *)

Goal
  forall P Q R S : Prop, P -> Q -> R -> S.
Proof.
  intros.
  Fail
  multimatch goal with
      | x : Prop |- _ => idtac x
  end; fail.
Abort.

(** [multimatch] to wariant [match]a, który wyzwala backtracking. W powyższym
    przykładzie działa on następująco:
    - do wzorca [x : Prop] dopasowujemy [H1 : R], a następnie [H0 : Q] i
      [H : P], co się rzecz jasna nie udaje.
    - Znajdujemy dopasowanie [S : Prop] i cały [multimatch] kończy się
      sukcesem.
    - Taktyka [fail] zawodzi i wobec tego cała taktyka [multimatch ...; fail]
      taże zawodzi.
    - Następuje nawrót i znów próbujemy znaleźć dopasowanie wzorca [x : Prop].
      Znajdujemy [R : Prop], [multimatch] kończy się sukcesem, ale [fail]
      zawodzi.
    - Następują kolejne nawroty i dopasowania do wzorca. Ostatecznie po
      wyczerpaniu się wszystkich możliwość cała taktyka zawodzi. *)

Goal
  forall P Q R S : Prop, P -> Q -> R -> S.
Proof.
  intros.
  match goal with
      | x : Prop |- _ => idtac x
  end.
  multimatch goal with
      | x : Prop |- _ => idtac x
  end.
  repeat match goal with
      | x : Prop |- _ => idtac x
  end.
  repeat multimatch goal with
      | x : Prop |- _ => idtac x
  end.
Abort.

(** Przyjrzyjmy się jeszcze różnicy w zachowaniach [match]a i [multimatch]a
    w połączeniu z kombinatorem [repeat]. Bez [repeat] oba dopasowania
    zachowują się identycznie. Użycie [repeat] przed [match] nie zmienia w
    tym konkretnym wypadku jego działania, ale w przypadku [multimatch]a
    użycie [repeat] ujawnia wszystkie jego sukcesy.

    Źródło różnego zachowania [match]a i [multimatch]a, jeżeli chodzi o
    backtracking, jest bardzo proste: tak naprawdę [match] jest jedynie
    skrótem dla [once multimatch]. [lazymatch], choć nie pokazano tego
    na powyższym przykładzie, w obu wypadkach (z [repeat] i bez) zachowuję
    się tak jak [match].

    Przyjrzyjmy się teraz dopasowaniom celu. *)

Goal
  forall (P Q R S : Prop) (a b c : nat),
    42 = 43 /\ (P -> Q).
Proof.
  intros. split;
  match goal with
      | X : Prop |- P -> Q => idtac X
      | n : nat |- 42 = 43 => idtac n
  end.
Abort.

(** Dopasowanie celu jest jeszcze prostsze niż dopasowanie hipotezy, bo
    cel jest tylko jeden i wobec tego nie trzeba dawać mu żadnej nazwy.
    Powyższa taktyka [split; match ...] działa następująco:
    - [split] generuje dwa podcele i wobec tego [match] działa na
      każdym z nich z osobna
    - pierwszy wzorzec głosi, że jeżeli w kontekście jest jakieś zdanie
      logiczne, które nazywamy [X], a cel jest postaci [P -> Q], to
      wypisujemy [X]
    - drugi wzorzec głosi, że jeżeli w kontekście jest jakaś liczba
      naturalna, którą nazywamy [n], a cel jest postaci [42 = 43], to
      wypisujemy [n]
    - następuje próba dopasowania pierwszego wzorca do pierwszego podcelu.
      Mimo, że w kontekście są zdania logiczne, to cel nie jest postaci
      [P -> Q], a zatem dopasowanie zawodzi.
    - następuje próba dopasowania drugiego wzorca do pierwszego podcelu.
      W kontekście jest liczba naturalna i cel jest postaci [42 = 43], a
      zatem dopasowanie udaje się. Do okna Messages zostaje wypisane "c",
      które zostało dopasowane jako pierwsze, gdyż kontekst jest przeglądany
      w kolejności od najstarszej hipotezy do najświeższej.
    - pierwszy wzorzec zostaje z powodzeniem dopasowany do drugiego podcelu
      i do okna Messages zostaje wypisane "S". *)

Goal
  forall (P Q R S : Prop) (a b c : nat), P.
Proof.
  intros.
  match goal with
      | _ => idtac "-_-"
  end.
  match goal with
      | _ => fail
      | X : Prop |- _ => idtac X
  end.
Abort.

(** Pozostało nam jedynie zademonstrować działanie wzorca [_]. Pierwsza z
    powyższych taktyk z sukcesem dopasowuje wzorzec [_] (gdyż pasuje on do
    każdego kontekstu i celu) i wobec tego do okna Messages zostaje wypisany
    napis "-_-".

    W drugim [match]u również zostaje dopasowany wzorzec [_], ale taktyka
    [fail] zawodzi i następuje przejście do kolejnego wzorca, który także
    pasuje. Wobec tego wypisane zostaje "S". Przypomina to nam o tym, że
    kolejność wzorców ma znaczenie i to nawet w przypadku, gdy któryś z
    nich (tak jak [_]) pasuje do wszystkiego. *)

(** * Wzorce i zmienne unifikacyjne *)

(* begin hide *)

(** TODO: dotąd zrobione
    Skoro wiemy już jak działa dopasowywanie kontekstu do wzorca, czas
    nauczyć się, jaki dokładnie działają wzorce. Jak już zostało wyżej
    napisane, wzorce to termy, które mogą zawierać zmienne unifikacyjne,
    czyli takie, które nie zostały wcześniej związane i których nazwy
    zaczynają się od symbolu [?]. Po udanym dopasowaniu możemy odwoływać
    się do podtermów dopasowanego termu, z którymi te zmienne zostały
    związane. Całość najprościej będzie przedstawić na przykładzie. *)

Goal
  forall P Q : Prop, P -> P \/ Q.
Proof.
  intros.
  match goal with
      | p : P |- P \/ Q => left; assumption
  end.
Qed.

(** Powyższy [match] nie zawiera zmiennych unifikacyjnych i działa w
    następujący sposób:
    - szukamy w kontekście obiektu [p], którego typ pasuje do wzorca [P].
      Obiekt, który nazywamy [p] w rzeczywistości nie musi nazywać się [p],
      ale jego typem rzeczywiście musi być [P].
    - jednocześnie żądamy, by cel był postaci [P \/ Q], gdzie zarówno [P]
      jak i [Q] odnoszą się do obiektów z kontekstu, które rzeczywiście tak
      się nazywają.
    - jeżeli powyższe wzorce zostaną dopasowane, to używamy taktyki [left;
      assumption], która rozwiązuje cel. *)

(** Być może powyższe wytłumaczenie więcej zaciemniło niż rozjaśniło. Rzućmy
    więc okiem na identyczny przykład, w którym zmieniono niektóre nazwy. *)

Goal
  forall A B : Prop, A -> A \/ B.
Proof.
  intros.
  Fail match goal with
      | p : P |- P \/ Q => left; assumption
  end.
  match goal with
      | p : A |- A \/ B => left; assumption
  end.
Restart.
  intros.
  match goal with
      | p : ?P |- ?P \/ ?Q => idtac P; left; assumption
  end.
Qed.

(** Tutaj zamiast [P] mamy [A], zaś zamiast [Q] jest [B]. [match] identyczny
    jak poprzednio tym razem zawodzi. Dzieje się tak, gdyż [P] odnosi się
    tu do obiektu z kontekstu, który nazywa się [P]. Niestety, w kontekście
    nie ma obiektu o takiej nazwie, o czym Coq skrzętnie nas informuje.

    W celu oraz po prawej stronie od [:] w hipotezie nie możemy za pomocą
    nazwy [P] dopasować obiektu, który nazywa się [A]. Żeby dopasować [A]
    możemy jednak użyć nazwy [A]. Ale co, jeżeli nie wiemy, jak nazywa się
    poszukiwany obiekt?

    W tym celu musimy użyć zmiennych unifikacyjnych, których nazwy
    zaczynają się od znaku zapytania. W ostatnim przykładzie widać, że
    wzorzec [?P] pasuje do obiektu [A]. Po prawej stronie [=>] jednak
    piszemy już [P], a nie [?P]. *)

(* end hide *)

(** **** Ćwiczenie *)

(** Napisz taktykę [my_assumption], która działa tak samo, jak [assumption].
    Nie używaj [assumption] — użyj [match]a. *)

(* begin hide *)
Ltac my_assumption :=
match goal with
    | x : ?P |- ?P => exact x
end.
(* end hide *)

Goal
  forall P : Prop, P -> P.
Proof.
  intros. my_assumption.
Qed.

End Match.

(** * Dopasowanie termu *)

(** * Inne wesołe rzeczy *)

(** * Przydatne taktyki *)

(** * Mniej przydatne taktyki *)