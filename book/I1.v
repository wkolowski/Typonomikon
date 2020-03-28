(** * I1: Ltac — język taktyk *)

(** Matematycy uważają, że po osiągnięciu pewnego poziomu zaawansowania i
    obycia (nazywanego zazwyczaj "mathematical maturity") skrupulatne
    rozpisywanie każdego kroku dowodu przestaje mieć sens i pozwalają
    sobie zarzucić je na rzecz bardziej wysokopoziomowego opisu rozumowania.

    Myślę, że ta sytuacja ma miejsce w twoim przypadku — znasz już sporą
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
    nauczyć się pisać własne taktyki, które pomogą nam wykonywać mało ciekawe
    kroki w dowodach, a w dalszej perspektywie także przeprowadzać bardziej
    zaawansowane rozumowania zupełnie automatycznie.

    W tym rozdziale poznamy podstawy języka [Ltac], który służy do tworzenia
    własnych taktyk. Jego składnię przedstawiono i skrupulatnie opisano tu:
    https://coq.inria.fr/refman/proof-engine/ltac.html#syntax

    Choć przykład znaczy więcej niż 0x3E8 stron manuala i postaram się
    dokładnie zilustrować każdy istotny moim zdaniem konstrukt języka
    [Ltac], to i tak polecam zapoznać się z powyższym linkiem.

    Upewnij się też, że rozumiesz dokładnie, jak działają podstawowe
    kombinatory taktyk, które zostały omówione w rozdziale 1, gdyż nie
    będziemy omawiać ich drugi raz. *)

(** * Zarządzanie celami i selektory *)

(** Dowodząc (lub konstruując cokolwiek za pomocą taktyk) mamy do rozwiązania
    jeden lub więcej celów. Cele są ponumerowane i domyślnie zawsze pracujemy
    nad tym, który ma numer 1.

    Jednak wcale nie musi tak być — możemy zaznaczyć inny cel i zacząć nad
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
    łatwiejszy niż obecny. Możemy wtedy przełączyć się na niego, rozwiązać
    go i wyniesione stąd doświadczenie przenieść na trudniejsze cele. Jest
    wskazane, żeby po zakończeniu dowodu zrefaktoryzować go tak, aby komenda
    [Focus] w nim nie występowała.

    Nie jest też tak, że zawsze musimy pracować nad celem o numerze 1. Możemy
    pracować na dowolnym zbiorze celów. Do wybierania celów, na które chcemy
    zadziałać taktykami, służą selektory. Jest ich kilka i mają taką składnię:
    - [n: t] — użyj taktyki t na n-tym celu. [1: t] jest równoważne [t].
    - [a-b: t] — użyj taktyki t na wszystkich celach o numerach od a do b
    - [a_1-b_1, ..., a_n-b_n: t] — użyj taktyki [t] na wszystkich celach
      o numerach od a_1 do b_1, ..., od a_n do b_n (zamiast a_i-b_i
      możemy też użyć pojedynczej liczby)
    - [all: t]  �- użyj [t] na wszystkich celach
    - zamiast [t], w powyższych przypadkach możemy też użyć wyrażenia
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
  1-3: assumption.
Restart.
  destruct 1 as [H [H' H'']]. repeat split.
  all: assumption.
Restart.
  destruct 1 as [H [H' H'']]. repeat split.
  all: [> assumption | assumption | assumption].
Qed.

(** Zauważmy, że powyższe selektory działają jedynie, gdy zostaną umieszczone
    przed wszystkimi taktykami, których dotyczą. Próba użycia ich jako
    argumenty dla innych taktyk jest błędem.

    Dla przykładu, w czwartym z powyższych dowodów nie możemy napisać
    [repeat split; 1-3: assumption], gdyż kończy się to błędem składni
    (nie wspominając o tym, że jest to bez sensu, gdyż dla uzyskania
    pożądanego efektu wystarczy napisać [repeat split; assumption]. *)

Goal forall P Q R : Prop, P /\ Q /\ R -> R /\ Q /\ P.
Proof.
  destruct 1 as [H [H' H'']].
  repeat split; only 1-3: assumption.
Qed.

(** Nie wszystko jednak stracone! Żeby móc używać wyrażeń zawierających
    selektory jako argumenty taktyk, możemy posłużyć się słowem [only].
    Mimo tego, i tak nie możemy napisać [repeat split; only all: ...],
    gdyż kończy się to błędem skadni. *)

Goal forall P Q R S : Prop, P -> P /\ Q /\ R /\ S.
Proof.
  repeat split.
  revgoals. all: revgoals. all: revgoals.
  swap 1 3. all: swap 1 3. all: swap 1 3.
  cycle 42. all: cycle 3. all: cycle -3.
Abort.

(** Jest jeszcze kilka innych taktyk do żonglowania celami. Pamiętaj, że
    wszystkie z nich działają na liście celów wybranych selektorami —
    domyślnie wybrany jest tylko cel numer 1 i wtedy taktyki te nie mają
    żadnego skutku.

    [revgoals] odwraca kolejność celów, na których działa. W naszym przypadku
    [revgoals] nie robi nic (odwraca kolejność celu [P] na [P]), natomiast
    [all: revgoals] zamienia kolejność celów z [P — Q — R — S] na
    [S — R — Q — P].

    [swap n m] zamienia miejscami cele n-ty i m-ty. W przykładzie [swap 1 3]
    nic nie robi, gdyś domyślnie wybrany jest tylko cel numer 1, a zatem nie
    można zamienić go miejscami z celem nr 3, którego nie ma. [all: swap 1 3]
    zamienia kolejność celów z [P — Q — R — S] na [R — Q — P — S].

    [cycle n] przesuwa cele cyklicznie o [n] do przodu (lub do tyłu, jeżeli
    argument jest liczbą ujemną). W naszym przykładzie [cycle 42] nic nie robi
    (przesuwa cyklicznie cel [P] o 42 miejsca, co daje w wyniku [P]), zaś
    [all: cycle 3] zamienia kolejność celów z [P — Q — R — S] na
    [S — P — Q — R].

    Taktyki te nie są zbyt użyteczne, a przynajmniej ja nigdy ich nie użyłem,
    ale dla kompletności wypadało o nich wspomnieć. Jeżeli wątpisz w
    użyteczność selektorów... cóż, nie dziwię ci się. Selektory przydają się
    głównie gdy chcemy napisać taktykę rozwiązującą wszystkie cele i
    sprawdzamy jej działanie na każdym celu z osobna. W pozostałych przypadkach
    są tylko zbędnym balastem. *)

(** * Podstawy języka Ltac *)

(** Ltac jest funkcyjnym językiem programowania, podobnie jak język termów
    Coqa (zwany Gallina), lecz te dwa języki są diametralnie różne:
    - Ltac jest kompletny w sensie Turinga, a Gallina nie. W szczególności,
      taktyki mogą się zapętlać i nie rodzi to żadnych problemów natury
      logicznej.
    - Ltac jest bardzo słabo typowany, podczas gdy Gallina dysponuje potężnym
      systemem typów.
    - W Ltacu nie możemy definiować typów danych, a jedynie taktyki działające
      na kontekstach i celu, podczas gdy Gallina pozwala na definiowanie
      bardzo szerokiej klasy typów i działających na nich funkcji.
    - Ltac, jako metajęzyk jezyka Gallina, posiada dostęp do różnych rzeczy,
      do których Gallina nie ma dostępu, takich jak dopasowanie termów
      dowolnego typu. Dla przykładu, w Ltacu możemy odróżnić termy [4] oraz
      [2 + 2] pomimo tego, że są konwertowalne. *)

(** W Ltacu możemy manipulować trzema rodzajami bytów: taktykami, termami
    Coqa oraz liczbami całkowitymi — te ostatnie nie są tym samym, co liczby
    całkowite Coqa i będziemy ich używać sporadycznie. Zanim zobaczymy
    przykład, przyjrzyjmy się taktyce [pose] oraz konstruktowi [let]. *)

Goal True.
Proof.
  pose true.
  pose (nazwa := 123).
Abort.

(** [pose t] dodaje do kontekstu term o domyślnej nazwie, którego ciałem
    jest [t]. Możemy też napisać [pose x := t], dzięki czemu zyskujemy
    kontrolę nad nazwą termu. *)

Goal True.
Proof.
  Fail let x := 42 in pose x.
  let x := constr:(42) in pose x.
  let x := split in idtac x.
Abort.

(** W Ltacu, podobnie jak w języku Gallina, mamy do dyspozycji konstrukt
    [let]. Za jego pomocą możemy nadać nazwę dowolnemu wyrażeniu języka
    Ltac. Jego działanie jest podobne jak w języku Gallina, a więc nie
    ma co się nad nim rozwodzić. Jest też konstrukt [let rec], który
    odpowiada [fix]owi Galliny.

    Spróbujmy dodać do kontekstu liczbę [42], nazwaną dowolnie. Komendą
    [let x := 42 in pose x] nie udaje nam się tego osiągnąć. O przyczynie
    niepowodzenia Coq informuje nas wprost: zmienna [x] nie jest termem.
    Czym zatem jest? Jak już się rzekło, Ltac posiada wbudowany typ liczb
    całkowitych, które nie są tym samym, co induktywnie zdefiniowane liczby
    całkowite Coqa. W tym kontekście [42] jest więc liczbą całkowitą Ltaca,
    a zatem nie jest termem.

    Aby wymusić na Ltacu zinterpretowanie [42] jako termu Coqa, musimy
    posłużyć się zapisem [constr:()]. Dzięki niemu argument znajdujący
    się w nawiasach zostanie zinterpretowany jako term. Efektem działania
    drugiej taktyki jest więc dodanie termu [42 : nat] do kontekstu,
    nazwanego domyślnie [n] (co jest, o dziwo, dość rozsądną nazwą).

    Wyrażenie [let x := split in idtac x] pokazuje nam, że taktyki również
    są wyrażeniami Ltaca i mogą być przypisywane do zmiennych (a także
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

(** Dowolną taktykę, której możemy użyć w dowodzie, możemy też nazwać
    za pomocą komendy [Ltac] i odwoływać się do niej w dowodach za pomocą
    tej nazwy. Komenda [Ltac] jest więc taktykowym odpowiednikiem komendy
    [Fixpoint].

    Podobnie jak [Fixpoint]y i inne definicje, tak i taktyki zdefiniowane
    za pomocą komendy [Ltac] mogą brać argumenty, którymi mogą być liczby,
    termy, nazwy hipotez albo inne taktyki.

    Zapis [Ltac name arg_1 ... arg_n := body] jest jedynie skrótem, który
    oznacza [Ltac name := fun arg_1 ... arg_n => body]. Jest to uwaga
    mocno techniczna, gdyż pierwszy zapis jest prawie zawsze preferowany
    wobec drugiego. *)

(** * Backtracking *)

(** Poznałeś już kombinator alternatywy [||]. Nie jest to jednak jedyny
    kombinator służący do wyrażania tej idei — są jeszcze kombinatory [+]
    oraz [tryif t1 then t2 else t3]. Różnią się one działaniem — [||] jest
    left-biased, podczas gdy [+] nie jest biased i może powodować
    backtracking.

    Nie przestrasz się tych dziwnych słów. Stojące za nimi idee są z grubsza
    bardzo proste. Wcześniej dowiedziałeś się, że taktyka może zawieść lub
    zakończyć się sukcesem. W rzeczywistości sprawa jest nieco bardziej
    ogólna: każda taktyka może zakończyć się dowolną ilością sukcesów. Zero
    sukcesów oznacza, że taktyka zawodzi. Większość taktyk, które dotychczas
    poznaliśmy, mogła zakończyć się co najwyżej jednym sukcesem. Są jednak i
    takie, które mogą zakończyć się dwoma lub więcej sukcesami.

    Proces dowodzenia za pomocą taktyk można zobrazować za pomocą procesu
    przeszukiwania drzewa, którego wierzchołkami są częściowo skonstruowane
    prooftermy, zaś krawędziami — sukcesy pochodzące od wywoływania taktyk.
    Liśćmi są prooftermy (dowód się udał) lub ślepe zaułki (dowód się nie
    udał).

    W takiej wizualizacji taktyka może wyzwalać backtracking, jeżeli jej
    użycie prowadzi do powstania rozgałęzienia w drzewie. Samo drzewo
    przeszukiwane jest w głąb, a backtracking polega na tym, że jeżeli
    trafimy na ślepy zaułek (dowód się nie powiódł), to cofamy się (ang.
    "to backtrack" — cofać się) do ostatniego punktu rozgałęzienia i
    próbujemy pójść inną gałęzią.

    Tę intuicję dobrze widać na poniższym przykładzie. *)

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
    udowodnienia, że [exists n : nat, n = 42] kończy się niepowodzeniem.
    Jest tak, gdyż [||] nie może powodować backtrackingu — jeżeli taktyka
    [t1] dokona postępu, to wtedy [t1 || t2] ma taki sam efekt, jak [t1],
    a w przeciwnym wypadku taki sam jak [t2]. Nawet jeżeli zarówno [t1]
    jak i [t2] zakończą się sukcesami, to sukcesy [t1 || t2] będą sukcesami
    tylko [t1].

    Na mocy powyższych rozważań możemy skonkludować, że taktyka [existsNat]
    ma co najwyżej jeden sukces i działa jak [exists n] dla pewnej liczby
    naturalnej [n]. Ponieważ użycie [exists 0] na celu [exists n : nat, n = 42]
    dokonuje postępu, to taktyka [existsNat] ma taki sam efekt, jak [exists 0].
    Próba użycia [reflexivity] zawodzi, a ponieważ nie ma już więcej sukcesów
    pochodzących od [existsNat] do wypróbowania, nie wyzwala backtrackingu.
    Wobec tego cała taktyka [existsNat; reflexivity] kończy się porażką.

    Inaczej sytuacja wygląda w przypadku [existsNat'], która bazuje na
    kombinatorze [+]. Sukcesy [t1 + t2] to wszystkie sukcesy [t1], po
    których następują wszystkie sukcesy [t2]. Wobec tego zbiór sukcesów
    [existsNat'] jest nieskończony i wygląda tak: [exists 0], [exists 1],
    [exists 2]... Użycie taktyki [reflexivity], które kończy się porażką
    wyzwala backtracking, więc całe wykonanie taktyki można zobrazować tak:
    - [exists 0; reflexivity] — porażka
    - [exists 1; reflexivity] — porażka
    - ...
    - [exists 42; reflexivity] — sukces *)

(** Na koniec zaznaczyć należy, że backtracking nie jest za darmo — im go
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
    który pozwala upewnić się, że dana taktyka ma dokładnie jeden sukces.
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

(** **** Ćwiczenie (existsNat'') *)

(** Przepisz taktykę [existsNat'] za pomocą konstruktu [let rec] —
    całość ma wyglądać tak: [Ltac existsNat'' := let rec ...] *)

(* begin hide *)
Ltac existsNat'' :=
  let rec f n := exists n + f (n + 1) in f 0.
(* end hide *)

Goal exists n : nat, n = 42.
Proof.
  existsNat''; reflexivity.
Qed.

(** **** Ćwiczenie (exists_length_3_letrec) *)

(** Udowodnij poniższe twierdzenie za pomocą pojedynczej taktyki, która
    generuje wszystkie możliwe listy wartości boolowskich. Całość zrób za
    pomocą konstruktu [let rec] w miejscu, tj. bez użycia komendy [Ltac]. *)

Require Import List.
Import ListNotations.

Theorem exists_length_3_letrec :
  exists l : list bool, length l = 3.
(* begin hide *)
Proof.
  let rec
    f l := exists l + f (true :: l) + f (false :: l)
  in f (@nil bool); reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie (trivial_goal) *)

(** Znajdź taki trywialnie prawdziwy cel i taką taktykę, która wywołuje
    [existsNat'], że taktyka ta nie skończy pracy i nigdy nie znajdzie
    dowodu, mimo że dla człowieka znalezienie dowodu jest banalne. *)

(* begin hide *)
Lemma trivial_goal :
  (exists n : nat, n = S n) \/ True.
Proof.
  Fail Timeout 1 (left; existsNat'; reflexivity) + (right; trivial).
Abort.
(* end hide *)

(** **** Ćwiczenie (search) *)

(** Napisz taktykę [search], która potrafi udowodnić cel będący dowolnie
    złożoną dysjunkcją pod warunkiem, że jeden z jej członów zachodzi na
    mocy założenia. Użyj rekursji, ale nie używaj konstruktu [let rec].

    Wskazówka: jeżeli masz problem, udowodnij połowę poniższych twierdzeń
    ręcznie i spróbuj dostrzec powtarzający si wzorzec. *)

(* begin hide *)
Ltac search := try assumption; (left; search) + (right; search).
(* end hide *)

Section search.

Hypotheses A B C D E F G H I J : Prop.

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

(** **** Ćwiczenie (inne_kombinatory_dla_alternatywy) *)

(** Zbadaj samodzielnie na podstawie dokumentacji, jak działają następujące
    kombinatory:
    - [tryif t1 then t2 else t3]
    - [first [t_1 | ... | t_N]]
    - [solve [t_1 | ... | t_N]] *)

(** Precyzyjniej pisząc: sprawdź kiedy odnoszą sukces i zawodzą, czy mogą
    wyzwalać backtracking oraz wymyśl jakieś mądre przykłady, który dobrze
    ukazują ichdziałanie w kontraście do [||] i [+]. *)

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
    kontekst ignorują; wzorców postaci [| kontekst |- _ => taktyka], które
    dopasowują jedynie kontekst, a cel ignorują; oraz wzorca [_], który
    oznacza "dopasuj cokolwiek".

    Zobaczmy, jak to wygląda na przykładach. *)

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
    każdej gałęzi dopasowania i nie muszą pokrywać się z rzeczywistymi
    nazwami termów w kontekście. W naszym przypadku nazywamy szukane przez
    nas zdanie [x], choć zdania obecne w naszym kontekście tak naprawdę
    nazywają się [P], [Q], [R] oraz [S].

    Przeszukiwanie obiektów w kontekście odbywa się w kolejności od
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
      Messages wiadomość "S" i kończy się sukcesem, ale [fail] zawodzi.
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
    kończy się niepowodzeniem.

    Zauważmy, że w dwóch ostatnich przykładach nie wystąpił backtracking —
    [match] nigdy nie wyzwala backtrackingu. Obserwowane działanie [match]a
    wynika stąd, że jeżeli taktyka po prawej od [=>] zawiedzie, to następuje
    próba znalezienia jakiegoś innego dopasowania wzorca [x : Prop]. Dopiero
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

(** Ten przykład potwierdza naszą powyższą obserwację dotyczącą backtrackingu.
    Mamy tutaj identyczne dopasowanie jak w pierwszym przykładzie — wypisuje
    ono [S] i kończy się sukcesem, ale tuż po nim następuje taktyka [fail],
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
      [H : P], co się rzecz jasna nie udaje.
    - Znajdujemy dopasowanie [S : Prop] i cały [multimatch] kończy się
      sukcesem.
    - Taktyka [fail] zawodzi i wobec tego cała taktyka [multimatch ...; fail]
      taże zawodzi.
    - Następuje nawrót i znów próbujemy znaleźć dopasowanie wzorca [x : Prop].
      Znajdujemy [R : Prop], [multimatch] kończy się sukcesem, ale [fail]
      zawodzi.
    - Następują kolejne nawroty i dopasowania do wzorca. Ostatecznie po
      wyczerpaniu się wszystkich możliwość cała taktyka zawodzi. *)

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

(** Przyjrzyjmy się jeszcze różnicy w zachowaniach [match]a i [multimatch]a
    w połączeniu z kombinatorem [repeat]. Bez [repeat] oba dopasowania
    zachowują się identycznie. Użycie [repeat] przed [match] nie zmienia w
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

(** Dopasowanie celu jest jeszcze prostsze niż dopasowanie hipotezy, bo
    cel jest tylko jeden i wobec tego nie trzeba dawać mu żadnej nazwy.
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
    powyższych taktyk z sukcesem dopasowuje wzorzec [_] (gdyż pasuje on do
    każdego kontekstu i celu) i wobec tego do okna Messages zostaje wypisany
    napis "-_-".

    W drugim [match]u również zostaje dopasowany wzorzec [_], ale taktyka
    [fail] zawodzi i następuje przejście do kolejnego wzorca, który także
    pasuje. Wobec tego wypisane zostaje "S". Przypomina to nam o tym, że
    kolejność wzorców ma znaczenie i to nawet w przypadku, gdy któryś z
    nich (tak jak [_]) pasuje do wszystkiego. *)

(** **** Ćwiczenie (destr_and) *)

(** Napisz taktykę [destr_and], która rozbija wszystkie koniunkcje, które
    znajdzie w kontekście, a następnie udowodni cel, jeżeli zachodzi on na
    mocy założenia.

    Dla przykładu, kontekst [H : P /\ Q /\ R |- _] powinien zostać
    przekształcony w [H : P, H0 : Q, H1 : R].

    Jeżeli to możliwe, nie używaj kombinatora [;] *)

(* begin hide *)
Ltac destr_and := intros; repeat
match goal with
    | H : _ /\ _ |- _ => destruct H
    | _ => try assumption
end.
(* end hide *)

Section destr_and.

Hypotheses A B C D E F G H I J : Prop.

Theorem destruct_0 :
    A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J -> D.
Proof. destr_and. Qed.

Theorem destruct_1 :
    ((((((((A /\ B) /\ C) /\ D) /\ E) /\ F) /\ G) /\ H) /\ I) /\ J -> F.
Proof. destr_and. Qed.

Theorem destruct_2 :
    A /\ ~ B /\ (C \/ C \/ C \/ C) /\ ((((D /\ I) /\ I) /\ I) /\ J) -> I.
Proof. destr_and. Qed.

End destr_and.

(** **** Ćwiczenie (solve_and_perm) *)

(** Napisz taktykę [solve_and_perm], która będzie potrafiła rozwiązywać
    cele postaci [P_1 /\ P_2 /\ ... /\ P_n -> P_i1 /\ P_i2 /\ ... /\ P_iN],
    gdzie prawa strona implikacji jest permutacją lewej strony, tzn. są w
    niej te same zdania, ale występujące w innej kolejności. *)

(* begin hide *)
Ltac solve_and_perm := intros; repeat
match goal with
    | H : _ /\ _ |- _ => destruct H
end; repeat split; try assumption.
(* end hide *)

Section solve_and_perm.

Hypotheses A B C D E F G H I J : Prop.

Theorem and_perm_0 :
  A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J ->
  J /\ I /\ H /\ G /\ F /\ E /\ D /\ C /\ B /\ A.
Proof. solve_and_perm. Qed.

Theorem and_perm_1 :
  A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J ->
  (((((((((A /\ B) /\ C) /\ D) /\ E) /\ F) /\ G) /\ H) /\ I) /\ J).
Proof. solve_and_perm. Qed.

Theorem and_perm_2 :
  (A /\ B) /\ (C /\ (D /\ E)) /\ (((F /\ G) /\ H) /\ I) /\ J ->
  (I /\ I /\ J) /\ ((A /\ B /\ (A /\ B)) /\ J) /\ (C /\ (E /\ (D /\ F /\ F))).
Proof. solve_and_perm. Qed.

End solve_and_perm.

(** **** Ćwiczenie (solve_or_perm) *)

(** Napisz taktykę [solve_or_perm], która będzie potrafiła rozwiązywać
    cele postaci [P_1 \/ P_2 \/ ... \/ P_n -> P_i1 \/ P_i2 \/ ... \/ P_iN],
    gdzie prawa strona implikacji jest permutacją lewej strony, tzn. są
    w niej te same zdania, ale występujące w innej kolejności.

    Wskazówka: wykorzystaj taktykę [search] z jednego z poprzednich
    ćwiczeń. *)

(* begin hide *)
Ltac solve_or_perm := intros; repeat
match goal with
    | H : _ \/ _ |- _ => destruct H
end; search.
(* end hide *)

Section solve_or_perm.

Hypotheses A B C D E F G H I J : Prop.

Theorem or_perm_0 :
  A \/ B \/ C \/ D \/ E \/ F \/ G \/ H \/ I \/ J ->
  J \/ I \/ H \/ G \/ F \/ E \/ D \/ C \/ B \/ A.
Proof. solve_or_perm. Qed.

Theorem or_perm_1 :
  A \/ B \/ C \/ D \/ E \/ F \/ G \/ H \/ I \/ J ->
  (((((((((A \/ B) \/ C) \/ D) \/ E) \/ F) \/ G) \/ H) \/ I) \/ J).
Proof. solve_or_perm. Qed.

Theorem or_perm_2 :
  (A \/ B) \/ (C \/ (D \/ E)) \/ (((F \/ G) \/ H) \/ I) \/ J ->
  (I \/ H \/ J) \/ ((A \/ B \/ (G \/ B)) \/ J) \/ (C \/ (E \/ (D \/ F \/ F))).
Proof. solve_or_perm. Qed.

Theorem or_perm_3 :
  A \/ B \/ C \/ D \/ E \/ F \/ G \/ H \/ I \/ J ->
  (((((((((A \/ B) \/ C) \/ D) \/ E) \/ F) \/ G) \/ H) \/ I) \/ J).
Proof. solve_or_perm. Qed.

End solve_or_perm.

(** **** Ćwiczenie (negn) *)

Section negn.

Require Import Arith.

(** Napisz funkcję [negn : nat -> Prop -> Prop], gdzie [negn n P] zwraca
    zdanie [P] zanegowane [n] razy. *)

(* begin hide *)
Fixpoint negn (n : nat) (P : Prop) : Prop :=
match n with
    | 0 => P
    | S n' => ~ negn n' P
end.
(* end hide *)

Eval cbn in negn 10 True.
(* ===> = ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ True : Prop *)

(** Udowodnij poniższe lematy. *)

Lemma dbl_neg :
  forall P : Prop, P -> ~ ~ P.
(* begin hide *)
Proof.
  unfold not. auto.
Qed.
(* end hide *)

Lemma double_n :
  forall n : nat, 2 * n = n + n.
(* begin hide *)
Proof.
  cbn. intro. rewrite <- plus_n_O. trivial.
Qed.
(* end hide *)

(** Przydadzą ci się one do pokazania dwóch właściwości fukncji [negn].
    Zanim przystąpisz do dowodzenia drugiego z nich, spróbuj zgadnąć,
    po którym argumencie najprościej będzie przeprowadzić indukcję. *)

Theorem even_neg :
  forall (n : nat) (P : Prop), P -> negn (2 * n) P.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    trivial.
    rewrite <- plus_n_O, Nat.add_comm. cbn. apply dbl_neg.
      rewrite <- double_n. apply IHn'. assumption.
Qed.
(* end hide *)

Theorem even_neg' :
  forall (n k : nat) (P : Prop),
    negn (2 * n) P -> negn (2 * (n + k)) P.
(* begin hide *)
Proof.
  induction k as [| k']; intros.
    rewrite <- plus_n_O. assumption.
    cbn. repeat (rewrite <- (Nat.add_comm (S _)); cbn).
      apply dbl_neg. replace _ with (negn (2 * (n + k')) P).
        apply IHk'. assumption.
        f_equal. cbn. rewrite <- !plus_n_O, (Nat.add_comm n). trivial.
Qed.
(* end hide *)

(** Napisz taktykę [negtac], która będzie potrafiła udowadniać cele postaci
    [forall P : Prop, negn (2 * n) P -> negn (2 * (n + k)) P], gdzie
    [n] oraz [k] są stałymi. Nie używaj twierdzeń, które udowodniłeś wyżej.

    Wskazówka: przydatny może byc konstrukt [match reverse goal]. *)

(* begin hide *)
Ltac negtac := cbn; unfold not; intros;
match reverse goal with
    | H : _ -> False |- False => apply H; clear H; negtac
    | _ => try assumption
end.
(* end hide *)

Theorem neg_2_14 :
  forall P : Prop, negn 2 P -> negn 14 P.
Proof. negtac. Qed.

Theorem neg_100_200 :
  forall P : Prop, negn 100 P -> negn 200 P.
Proof. negtac. Qed.

Theorem neg_42_1000 :
  forall P : Prop, negn 42 P -> negn 200 P.
Proof. negtac. Qed.

End negn.

(** * Wzorce i unifikacja *)

(** Skoro wiemy już jak działa dopasowywanie kontekstu do wzorca, czas
    nauczyć się jak dokładnie działają wzorce oraz czym są zmienne
    unifikacyjne i sama unifikacja.

    Przede wszystkim, jak przekonaliśmy się wyżej, termy są wzorcami.
    Termy nie zawierają zmiennych unifikacyjnych, a wzorce będące
    termami dopasowują się tylko do identycznych termów. Dopasowanie
    takie nie wiąże żadnych nowych zmiennych. Zobaczmy to na przykładzie. *)

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
      Obiekt, który nazywamy [p] w rzeczywistości nie musi nazywać się [p],
      ale jego typem rzeczywiście musi być [P]. W szczególności, wzorzec
      [P] nie pasuje do [Q], gdyż [P] i [Q] nie są konwertowalne.
    - jednocześnie żądamy, by cel był postaci [P \/ Q], gdzie zarówno [P]
      jak i [Q] odnoszą się do obiektów z kontekstu, które rzeczywiście tak
      się nazywają.
    - jeżeli powyższe wzorce zostaną dopasowane, to używamy taktyki [left;
      assumption], która rozwiązuje cel. *)

(** Zobaczmy, co się stanie, jeżeli w powyższym przykładzie zmienimy nazwy
    hipotez. *)

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
Qed.

(** Tutaj zamiast [P] mamy [A], zaś zamiast [Q] jest [B]. [match] identyczny
    jak poprzednio tym razem zawodzi. Dzieje się tak, gdyż [P] odnosi się
    tu do obiektu z kontekstu, który nazywa się [P]. Niestety, w kontekście
    nie ma obiektu o takiej nazwie, o czym Coq skrzętnie nas informuje.

    W [match]u w celu oraz po prawej stronie od [:] w hipotezie nie możemy
    za pomocą nazwy [P] dopasować obiektu, który nazywa się [A]. Dopasować
    [A] możemy jednak używając wzorca [A]. Ale co, gdybyśmy nie wiedzieli,
    jak dokładnie nazywa się poszukiwany obiekt? *)

Goal
  forall A B : Prop, A -> A \/ B.
Proof.
  intros.
  match goal with
      | p : ?P |- ?P \/ ?Q => idtac P; idtac Q; left; assumption
  end.
Qed.

(** Jeżeli chcemy dopasować term o nieznanej nam nazwie (lub term, którego
    podtermy mają nieznane nazwy) musimy użyć zmiennych unifikacyjnych.
    Wizualnie można rozpoznać je po tym, że ich nazwy zaczynają się od
    znaku [?]. Zmienna unifkacyjna [?x] pasuje do dowolnego termu, a
    udane dopasowanie sprawia, że po prawej stronie strzałki [=>] możemy
    do dopasowanego termu odnosić się za pomocą nazwy [x].

    Powyższe dopasowanie działa w następujący sposób:
    - próbujemy dopasować wzorzec [p : ?P] do najświeższej hipotezy w
      kontekście, czyli [H : A]. [p] jest nazwą tymczasową i wobec tego
      pasuje do [H], zaś zmienna unifikacyjna [?P] pasuje do dowolnego
      termu, a zatem pasuje także do [A].
    - dopasowanie hipotezy kończy się sukcesem i wskutek tego zmienna
      unifikacyjna [?P] zostaje związana z termem [A]. Od teraz w dalszych
      wzorcach będzie ona pasować jedynie do termu [A].
    - następuje próba dopasowania celu do wzorca [?P \/ ?Q]. Ponieważ
      [?P] zostało związane z [A], to wzorzec [?P \/ ?Q] oznacza tak
      naprawdę [A \/ ?Q]. Zmienna unifikacyjna [?Q] nie została wcześniej
      związana i wobec tego pasuje do wszystkiego.
    - wobec tego [?Q] w szczególności pasuje do [B], a zatem wzorzec
      [?P \/ ?Q] pasuje do [A \/ B] i całe dopasowanie kończy się
      sukcesem. W jego wyniku [?Q] zostaje związane z [B].
    - zostaje wykonana taktyka [idtac P; idtac Q], która potwierdza, że
      zmienna unifikacyjna [?P] została związana z [A], a [?Q] z [B],
      wobec czego na prawo od [=>] faktycznie możemy do [A] i [B] odwoływać
      się odpowiednio jako [P] i [Q].
    - taktyka [left; assumption] rozwiązuje cel. *)

(** Podkreślmy raz jeszcze, że zmienne unifikacyjne mogą występać tylko we
    wzorcach, a więc w hipotezach po prawej stronie dwukropka [:] oraz w
    celu. Błędem byłoby napisanie w hipotezie [?p : ?P]. Podobnie błędem
    byłoby użycie nazwy [?P] na prawo od strzałki [=>].

    Zauważmy też, że w danej gałęzi [match]a każda zmienna unifikacyjna może
    wystąpić więcej niż jeden raz. Wzorce, w których zmienne unifikacyjne
    występują więcej niż raz to wzorce nieliniowe. Możemy skontrastować je
    ze wzorcami liniowymi, w których każda zmienna może wystąpić co najwyżej
    raz.

    Wzorcami liniowymi są wzorce, których używamy podczas definiowania
    zwykłych funkcji przez dopasowanie do wzorca (zauważmy jednak, że
    tamtejsze zmienne unifikacyjne nie zaczynają się od [?]). Ograniczenie
    do wzorców liniowych jest spowodowane faktem, że nie zawsze możliwe
    jest stwierdzenie, czy dwa dowolne termy do siebie pasują.

    Język termów Coqa w celu uniknięcia sprzeczności musi być zupełnie
    nieskazitelny i musi zakazywać używania wzorców nieliniowych. Język
    Ltac, który nie może sam z siebie wyczarować sprzeczności, może sobie
    pozwolić na więcej i wobec tego wzorce nieliniowe są legalne. *)

Goal
  [2] = [].
Proof.
  match goal with
      | |- ?x = _ => idtac x
  end.
  match goal with
      | |- cons ?h _ = nil => idtac h
  end.
  match goal with
      | |- 2 :: _ = ?l => idtac l
  end.
  match goal with
      | |- [?x] = [] => idtac x
  end.
Abort.

(** Zauważmy, że nie musimy używać zmiennych unifikacyjnych do dopasowywania
    całych termów — w pierwszym z powyższych przykładów używamy zmiennej [?x],
    aby dopasować jedynie lewą stronę równania, które jest celem.

    Ze zmiennych unifikacyjnych oraz stałych, zmiennych i funkcji (a więc
    także konstruktorów) możemy budować wzorce dopasowujące termy o różnych
    fikuśnych kształtach.

    W drugim przykładzie wzorzec [cons ?h _ = nil] dopasowuje równanie,
    którego lewa strona jest listą niepustą o dowolnej głowie, do której
    możemy się odnosić jako [h], oraz dowolnym ogonie, do którego nie
    chcemy móc się odnosić. Prawa strona tego równania jest listą pustą.

    Wzorce radzą sobie bez problemu także z notacjami. Wzorzec [2 :: _ = ?l]
    dopasowuje równanie, którego lewa strona jest listą, której głowa to [2],
    zaś ogon jest dowolny, a prawa strona jest dowolną listą, do której
    będziemy się mogli odwoływać po prawej stronie [=>] jako [l].

    Ostatni wzorzec pasuje do równania, którego lewa strona jest singletonem
    (listą jednoelementową) zawierającym wartość, do której będziemy mogli
    odnosić się za pomocą nazwy [x], zaś prawą stroną jest lista pusta. *)

(** **** Ćwiczenie (my_assumption) *)

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

(** **** Ćwiczenie (forward) *)

(** Napisz taktykę [forward], która wyspecjalizuje wszystkie znalezione w
    kontekście implikacje, o ile oczywiście ich przesłanki również będą
    znajdowały się w kontekście, a następnie rozwiąże cel, jeżeli jest on
    prawdziwy na mocy założenia.

    Dla przykładu, kontekst [H : P -> Q, H0 : Q -> R, H1 : P |- _]
    powinien zostać przekształcony w [H : Q, H0 : R, H1 : P |- _].

    Wskazówka: przydatna będzie taktyka [specialize]. *)

(* begin hide *)
Ltac forward := intros; repeat
match goal with
    | H : ?P -> ?Q, H' : ?P |- _ => specialize (H H')
    | H : ?P |- ?P => assumption
end.
(* end hide *)

Example forward_1 :
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof. forward. Qed.

Example forward_2 :
  forall P Q R S : Prop, (P -> Q -> R) -> (S -> Q -> P -> R).
Proof. forward. Qed.

(** * Narzędzia przydatne przy dopasowywaniu *)

(** Poznawszy już konstrukt [match] i jego warianty oraz sposób dopasowywania
    wzorców i rolę unifikacji oraz zmiennych unifikacyjnych w tym procesie,
    czas rzucić okiem na kilka niezwykle przydatnych narzędzi, które uczynią
    nasze życie dopasowywacza łatwiejszym. *)

(** ** Dopasowanie podtermu *)

(** Pierwszym z nich jest wyrażenie [context ident [term]], dzięki któremu
    możemy tworzyć wzorce dopasowujące podtermy danego termu. Zobaczmy jego
    działanie na przykładzie. *)

Goal
  forall a b c : nat, a = b -> b = c -> a = c.
Proof.
  intros a b c.
  match goal with
      | |- context G [?x = ?y] => idtac G x y
  end.
  repeat multimatch goal with
      | |- context G [?x = ?y] => idtac G x y
  end.
Abort.

(** W powyższym przykładzie naszym celem jest znalezienie wszystkich równań,
    które są podtermami naszego celu. Dopasowanie wzorca [context G [?x = ?y]]
    przebiega w następujący sposób:
    - w celu wyszukiwae są wszystkie podtermy postaci [?x = ?y]. Są trzy
      takie: [a = b], [b = c] oraz [a = c]
    - wzorzec [?x = ?y] zostaje zunifikowany z pierwszym pasującym podtermem,
      czyli [a = b]. W wyniku dopasowania zmienna unifikacyjna [?x] zostaje
      związana z [a], zaś [?y] z [b]
    - cały term, którego podterm został dopasowany do wzorca, zostaje
      związany ze zmienną [G], przy czym jego dopasowany podterm zostaje
      specjalnie zaznaczony (po wypisaniu w jego miejscu widać napis "?M-1")
    - zostaje wykonana taktyka [idtac G x y] *)

(** Druga z powyższych taktyk działa podobnie, ale dzięki zastosowaniu
    [repeat multimatch] ujawnia nam ona wszystkie podtermy pasujące do wzorca
    [?x = ?y]. *)

(** **** Ćwiczenie (podtermy) *)

(** Oblicz ile podtermów ma term [42]. Następnie napisz taktykę [nat_subterm],
    która potrafi wypisać wszystkie podtermy dowolnej liczby naturalnej, która
    znajduje się w celu. Wymyśl odpowiedni cel i przetestuj na nim swoje
    obliczenia. *)

(* begin hide *)
(** Odpowiedź: term [42] ma 42 podtermy, czyli tyle, ile razy występuje w nim
    konstruktor [S]. *)

Ltac nat_subterm :=
  repeat multimatch goal with
      | |- context [S ?x] => idtac x
  end.

Goal @length nat [] = 42.
Proof.
  nat_subterm.
Abort.
(* end hide *)

(** ** Generowanie nieużywanych nazw *)

(** Drugim przydatnym narzędziem jest konstrukt [fresh], który pozwala nam
    wygenerować nazwę, której nie nosi jeszcze żadna zmienna. Dzięki temu
    możemy uniknąć konfliktów nazw, gdy używamy taktyk takich jak [intros]
    czy [destruct], które pozwalają nam nazywać obiekty. Przyjrzyjmy się
    następującemu przykładowi. *)

Goal forall x y : nat, {x = y} + {x <> y}.
Proof.
  intro x. Fail intro x.
  let x := fresh in intro x.
Restart.
  intro x. let x := fresh "y" in intro x.
Restart.
  intro x. let x := fresh x in intro x.
Restart.
  intro x. let x := fresh y in intro x.
Abort.

(** Mamy w kontekście liczbę naturalną [x : nat] i chcielibyśmy wprowadzić
    do niego kolejną. Cóż, nie jest to żaden problem — wystarczy nazwać go
    dowolną nazwą różną od "x". Ale co, jeżeli nie wiemy, jak nazywają się
    obiekty znajdujące się w kontekście?

    Przy intensywnym posługiwaniu się taktykami i automatyzacją jest to nader
    częsta możliwość: gdy dopasujemy kontekst za pomocą [match]a, nie znamy
    oryginalnych nazw dopasowanych termów — możemy odwoływać się do nich
    tylko za pomocą nazw lokalnych, wprowadzonych na potrzeby danego wzorca.

    Z odsięczą przychodzi nam generator świeżych nazw o wdzięcznej nazwie
    [fresh]. Zazwyczaj będziemy się nim posługiwać w następujący sposób:
    [let var := fresh arg_1 ... arg_N in t]. Tutaj [var] jest zmienną
    języka [Ltac], której wartością jest świeżo wygenerowana nazwa, a [t]
    to jakaś taktyka, która w dowolny sposób korzysta z [var].

    Powyższe cztery taktyki działają tak:
    - [let x := fresh in intro x] — [fresh] generuje świeżą nazwę, domyślnie
      jest nią "H". Nazwa ta staje się wartością Ltacowej zmiennej [x]. Owa
      zmienna jest argumentem taktyki [intro], dzięki czemu wprowadzony do
      kontekstu obiekt typu [nat] zostaje nazwany "H".
    - [let x := fresh "y" in intro x] — jeżeli [fresh] dostanie jako argument
      ciąg znaków, to wygeneruje nazwę zaczynającą się od tego ciągu, która
      nie jest jeszcze zajęta. Ponieważ nazwa "y" jest wolna, właśnie tak
      zostaje nazwany wprowadzany obiekt.
    - [let x := fresh x in intro x] — tutaj mamy mały zamęt. Pierwszy i trzeci
      [x] jest zmienną Ltaca, zaś drugi odnosi się do obiektu z kontekstu.
      Jeżeli [arg] jest obiektem z kontekstu, to [fresh arg] tworzy świeżą
      nazwę zaczynającą się od nazwy, jaką [arg] nosi w kontekście. Tutaj
      nie  ma to znaczenia, gdyż [x] nazywa się po prostu "x" i wobec tego
      [fresh] generuje nazwę "x0", ale mechanizm ten działa tak samo w
      przypadku zmiennych unifikacyjnych.
    - [let x := fresh y in intro x] — jak widać, argumentem [fresh] może też
      być nazwa zmiennej nie odnosząca się zupełnie do niczego. W naszym
      przypadku nie ma w kontekście zmiennej [y], a [fresh] generuje na jej
      podstawie świeżą nazwę "y". *)

(** ** [fail] (znowu) *)

(** Taktykę [fail] już poznaliśmy, ale nie w jej pełnej krasie. Czas więc
    odkryć resztę jej możliwości. *)

Goal False.
Proof.
  Fail fail "Hoho, czego się spodziewałeś?" 1.
Abort.

(** Pierwsza z nich nie jest zbyt spektakularna — możemy do [fail] przekazać
    jako argumenty ciągi znaków lub termy, co spowoduje wyświetlenie ich w
    oknie wiadomości.

    Drugą, znacznie ważniejszą możliwością, jaką daje nam taktyka [fail],
    jest kontrola "poziomu porażki". Dzięki niemu zyskujemy władzę nad
    tym, jak "mocno" taktyka [fail] zawodzi. Domyśnie wynosi on 0. Użycie
    taktyki [fail] (która wobec tego oznacza to samo, co [fail 0]) powouje
    przerwanie wykonywania obecnej gałęzi [match]a i przejście do następnej.
    Użycie taktyki [fail n], gdzie n nie jest równe 0, powoduje opuszczenie
    całego obecnego [match]a (tj. wszystkich gałęzi) lub bloku [do]/[repeat]
    i wywołanie [fail (n - 1)].

    Przyjrzyjmy się temu zachowaniu na przykładzie. *)

Goal False.
Proof.
  match goal with
      | _ => idtac "first branch"; fail
      | _ => idtac "second branch"
  end.
  Fail match goal with
      | _ => idtac "first branch"; fail 1
      | _ => idtac "second branch"
  end.
  try match goal with
      | _ => idtac "first branch"; fail 1
      | _ => idtac "second branch"
  end.
  Fail try match goal with
      | _ => idtac "first branch"; fail 2
      | _ => idtac "second branch"
  end.
Abort.

(** Cztery powyższe dopasowania działają następująco:
    - W pierwszym dopasowana jest pierwsza gałąź. Wyświetlona zostaje
      wiadomość, po czym taktyka [fail] zawodzi i następuje przejście
      do kolejnej gałęzi. Tutaj też wypisana zostaje wiadomość i cała
      taktyka [match ...] kończy się sukcesem.
    - W drugim przypadku dopasowana jest pierwsza gałąź, która wypisuje
      wiadomość, ale taktyka [fail 1] powoduje, że cały [match] zawodzi
      i druga gałąź nie jest w ogóle dopasowywana.
    - Trzeci przypadek jest podobny do drugiego. [fail 1] powoduje, że
      cały [match] zawodzi, ale dzięki kombinatorowi [try] cała taktyka
      [try match ...] kończy się sukcesem.
    - Czwarta taktyka jest podobna do trzeciej, ale tym razem po udanym
      dopasowaniu pierwszej gałęzi taktyka [fail 2] powoduje, że cały
      [match] zawodzi. Następnie ma miejsce wywołanie taktyki [fail 1],
      które powoduje, że nawet mimo użycia kombinatora [try] cała taktyka
      [try match ...] zawodzi. *)

(** * Inne (mało) wesołe rzeczy *)

(** Ten podrozdział będzie wesołą zbieraninką różnych niezbyt przydatnych
    (przynajmniej dla mnie) konstruktów języka Ltac, które nie zostały
    dotychczas omówione. *)

Goal False /\ False /\ False.
Proof.
  repeat split.
  let n := numgoals in idtac n.
  all: let n := numgoals in idtac n.
Abort.

(** Ilość celów możemy policzyć za pomocą taktyki [numgoals]. Liczy ona
    wszystkie cele, na które działa, więc jeżeli nie użyjemy żadnego
    selektora, zwróci ona 1. Nie jest ona zbyt użyteczna (poza bardzo
    skomplikowanymi taktykami, które z jakichś powodów nie operują tylko na
    jednym celu, lecz na wszystkich). *)

Goal False /\ False /\ False.
Proof.
  repeat split.
  all: let n := numgoals in guard n > 2.
  Fail all: let n := numgoals in guard n < 2.
Abort.

(** Taktyka [guard cond] pozwala nam dokonywać prostych testów na liczbach
    całkowitych Ltaca. Jeżeli warunek zachodzi, taktyka ta zachowuje się
    jak [idtac], czyli kończy się sukcesem i nie robi nic więcej. Jeżeli
    warunek nie zachodzi, taktyka zawodzi.

    W powyższym przykładzie taktyka [guard n > 2] kończy się sukcesem,
    gdyż są 3 cele, a 3 > 2, zaś taktyka [guard n < 2] zawodzi, bo są
    3 cele, a nie jest prawdą, że 3 < 2. *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

Goal even 42.
Proof.
  try timeout 1 repeat constructor.
Abort.

Goal even 1338.
Proof.
  try timeout 1 repeat constructor.
Abort.

(** Kombinator [timeout n t] pozwala nam sprawić, żeby taktyka t zawiodła,
    jeżeli jej wykonanie będzie zajmowało dłużej, niż n sekund. Nie jest on
    zbyt przydatny, gdyż szybkość wykonania danej taktyki jest kwestią mocno
    zależną on sprzętu. Jak można przeczytać w manualu, kombinator ten bywa
    przydatny głównie przy debugowaniu i nie zaleca się, żeby występował w
    finalnych dowodach, gdyż może powodować problemy z przenośnością.

    W powyższym przykładzie taktyka [timeout 1 repeat constructor] kończy się
    sukcesem, gdyż udowodnienie [even 42] zajmuje jej mniej, niż 1 sekundę
    (przynajmniej na moim komputerze; na twoim taktyka ta może zawieść), ale
    już udowodnienie [even 1338] trwa więcej niż jedną sekundę i wobec tego
    taktyka [timeout 1 repeat constructor] dla tego celu zawodzi (przynajmniej
    u mnie; jeżeli masz mocny komputer, u ciebie może zadziałać).

    Co więcej, kombinator [timeout] może zachowywać się różnie dla tego samego
    celu nawet na tym samym komputerze. Na przykład przed chwilą taktyka ta
    zakończyłą się na moim komputerze sukcesem, mimo że dotychczas zawsze
    zawodziła). *)

Goal even 666.
Proof.
  time repeat constructor.
Restart.
  Time repeat constructor.
Abort.

(** Kolejnym kombinatorem jest [time t], który odpala taktykę [t], a następnie
    wyświetla informację o czasie, jaki zajęło jej wykonanie. Czas ten jest
    czasem rzeczywistym, tzn. zależy od mocy twojego komputera. Nie jest zbyt
    stały — zazwyczaj różni się od jednego mierzenia do drugiego, czasem
    nawet dość znacznie.

    Alternatywą dla taktyki [time] jest komenda [Time], która robi dokładnie
    to samo. Jeżeli stoisz przed wyborem między tymi dwoma — wybierz komendę
    [Time], gdyż komendy zachowują się zazwyczaj w sposób znacznie bardziej
    przewidywalny od taktyk. *)

(** * Konkluzja *)

(** W niniejszym rozdziale zapoznaliśmy się z potężną maszynerią, dzięki
    której możemy zjeść ciastko i mieć ciastko: dzięki własnym taktykom
    jesteśmy w stanie połączyć Coqową pełnię formalnej poprawności oraz
    typowy dla matematyki uprawianej nieformalnie luźny styl dowodzenia,
    w którym mało interesujące szczegóły zostają pominięte. A wszystko to
    okraszone (wystarczającą, mam nadzieję) szczyptą zadań.

    Ale to jeszcze nie wszystko, gdyż póki co pominięte zostały konstrukty
    Ltaca pozwalające dopasowywać termy, dzięki którym jesteśmy w stanie
    np. napisać taktykę, która odróżni [2 + 2] od [4]. Jeżeli odczuwasz
    niedosyt po przeczytaniu tego rozdziału, to uszy do góry — zapoznamy
    się z nimi już niedługo, przy omawianiu dowodu przez reflekcję. Zanim
    to jednak nastąpi, zrobimy przegląd taktyk wbudowanych. *)