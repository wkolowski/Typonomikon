(** * B3minusepsilon: Takie tam [TODO] *)

(** * Kombinatory taktyk *)

(** Przyjrzyjmy się jeszcze raz twierdzeniu [iff_intro] (lekko
    zmodernizowanemu przy pomocy kwantyfikacji uniwersalnej). *)

Lemma iff_intro' :
  forall P Q : Prop,
    (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof.
  intros. split.
    intro. apply H. assumption.
    intro. apply H0. assumption.
Qed.

(** Jego dowód wygląda dość schematycznie. Taktyka [split] generuje
    nam dwa podcele będące implikacjami — na każdym z osobna używamy
    następnie [intro], a kończymy [assumption]. Jedyne, czym różnią
    się dowody podcelów, to nazwa aplikowanej hipotezy.

    A co, gdyby jakaś taktyka wygenerowała nam 100 takich schematycznych
    podcelów? Czy musielibyśmy przechodzić przez mękę ręcznego dowodzenia
    tych niezbyt ciekawych przypadków? Czy da się powyższy dowód jakoś
    skrócić lub zautomatyzować?

    Odpowiedź na szczęście brzmi "tak". Z pomocą przychodzą nam kombinatory
    taktyk (ang. tacticals), czyli taktyki, które mogą przyjmować jako
    argumenty inne
    taktyki. Dzięki temu możemy łączyć proste taktyki w nieco bardziej
    skomplikowane lub jedynie zmieniać niektóre aspekty ich zachowań. *)

(** ** [;] (średnik) *)

Lemma iff_intro'' :
  forall P Q : Prop,
    (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof.
  split; intros; [apply H | apply H0]; assumption.
Qed.

(** Najbardziej podstawowym kombinatorem jest [;] (średnik). Zapis
    [t1; t2] oznacza "użyj na obecnym celu taktyki [t1], a następnie
    na wszystkich podcelach wygenerowanych przez [t1] użyj taktyki
    [t2]".

    Zauważmy, że taktyka [split] działa nie tylko na koniunkcjach i
    równoważnościach, ale także wtedy, gdy są one konkluzją pewnej
    implikacji. W takich przypadkach taktyka [split] przed rozbiciem
    ich wprowadzi do kontekstu przesłanki implikacji (a także zmienne
    związane kwantyfikacją uniwersalną), zaoszczędzając nam użycia
    wcześniej taktyki [intros].

    Wobec tego, zamiast wprowadzać zmienne do kontekstu przy pomocy
    [intros], rozbijać cel [split]em, a potem jeszcze w każdym
    podcelu z osobna wprowadzać do kontekstu przesłankę implikacji,
    możemy to zrobić szybciej pisząc [split; intros].

    Drugie użycie średnika jest uogólnieniem pierwszego. Zapis
    [t; [t1 | t2 | ... | tn]] oznacza "użyj na obecnym podcelu
    taktyki [t]; następnie na pierwszym wygenerowanym przez nią
    podcelu użyj taktyki [t1], na drugim [t2], etc., a na n-tym
    użyj taktyki [tn]". Wobec tego zapis [t1; t2] jest jedynie
    skróconą formą [t1; [t2 | t2 | ... | t2]].

    Użycie tej formy kombinatora [;] jest uzasadnione tym, że
    w pierwszym z naszych podcelów musimy zaaplikować hipotezę
    [H], a w drugim [H0] — w przeciwnym wypadku nasza taktyka
    zawiodłaby (sprawdź to). Ostatnie użycie tego kombinatora
    jest identyczne jak pierwsze — każdy z podcelów kończymy
    taktyką [assumption].

    Dzięki średnikowi dowód naszego twierdzenia skurczył się z
    trzech linijek do jednej, co jest wyśmienitym wynikiem —
    trzy razy mniej linii kodu to trzy razy mniejszy problem
    z jego utrzymaniem. Fakt ten ma jednak również i swoją
    ciemną stronę. Jest nią utrata interaktywności — wykonanie
    taktyki przeprowadza dowód od początku do końca.

    Znalezienie odpowiedniego balansu między automatyzacją i
    interaktywnością nie jest sprawą łatwą. Dowodząc twierdzenia
    twoim pierwszym i podstawowym celem powinno być zawsze jego
    zrozumienie, co oznacza dowód mniej lub bardziej interaktywny,
    nieautomatyczny. Gdy uda ci się już udowodnić i zrozumieć dane
    twierdzenie, możesz przejść do automatyzacji. Proces ten jest
    analogiczny jak w przypadku inżynierii oprogramowania — najpierw
    tworzy się działający prototyp, a potem się go usprawnia.

    Praktyka pokazuje jednak, że naszym ostatecznym
    celem powinna być pełna automatyzacja, tzn. sytuacja, w
    której dowód każdego twierdzenia (poza zupełnie banalnymi)
    będzie się sprowadzał, jak w powyższym przykładzie, do
    użycia jednej, specjalnie dla niego stworzonej taktyki.
    Ma to swoje uzasadnienie:
    - zrozumienie cudzych dowodów jest zazwyczaj dość trudne,
      co ma spore znaczenie w większych projektach, w których
      uczestniczy wiele osób, z których część odchodzi, a na
      ich miejsce przychodzą nowe
    - przebrnięcie przez dowód interaktywny, nawet jeżeli
      ma walory edukacyjne i jest oświecające, jest zazwyczaj
      czasochłonne, a czas to pieniądz
    - skoro zrozumienie dowodu jest trudne i czasochłonne,
      to będziemy chcieli unikać jego zmieniania, co może
      nastąpić np. gdy będziemy chcieli dodać do systemu
      jakąś funkcjonalność i udowodnić, że po jej dodaniu
      system wciąż działa poprawnie *)

(** **** Ćwiczenie (średnik) *)

(** Poniższe twierdzenia udowodnij najpierw z jak największym zrozumieniem,
    a następnie zautomatyzuj tak, aby całość była rozwiązywana w jednym
    kroku przez pojedynczą taktykę. *)

Lemma or_comm_ex :
  forall P Q : Prop, P \/ Q -> Q \/ P.
(* begin hide *)
Proof.
  intros; destruct H; [right | left]; assumption.
Qed.
(* end hide *)

Lemma diamond :
  forall P Q R S : Prop,
    (P -> Q) \/ (P -> R) -> (Q -> S) -> (R -> S) -> P -> S.
(* begin hide *)
Proof.
  intros. destruct H.
    apply H0. apply H. assumption.
    apply H1. apply H. assumption.
Restart.
  intros; destruct H; [apply H0 | apply H1]; apply H; assumption.
Qed.
(* end hide *)

(** ** [||] (alternatywa) *)

Lemma iff_intro''' :
  forall P Q : Prop,
    (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof.
  split; intros; apply H0 || apply H; assumption.
Qed.

(** Innym przydatnym kombinatorem jest [||], który będziemy nazywać
    alternatywą. Żeby wyjaśnić jego działanie, posłużymy się pojęciem
    postępu. Taktyka dokonuje postępu, jeżeli wygenerowany przez nią
    cel różni się od poprzedniego celu. Innymi słowy, taktyka nie
    dokonuje postępu, jeżeli nie zmienia obecnego celu. Za pomocą
    [progress t] możemy sprawdzić, czy taktyka [t] dokona postępu
    na obecnym celu.

    Taktyka [t1 || t2] używa na obecnym celu [t1]. Jeżeli [t1] dokona
    postępu, to [t1 || t2] będzie miało taki efekt jak [t1] i skończy
    się sukcesem. Jeżeli [t1] nie dokona postępu, to na obecnym celu
    zostanie użyte [t2]. Jeżeli [t2] dokona postępu, to [t1 || t2]
    będzie miało taki efekt jak [t2] i skończy się sukcesem. Jeżeli
    [t2] nie dokona postępu, to [t1 || t2] zawiedzie i cel się nie
    zmieni.

    W naszym przypadku w każdym z podcelów wygenerowanych przez
    [split; intros] próbujemy zaaplikować najpierw [H0], a potem
    [H]. Na pierwszym podcelu [apply H0] zawiedzie (a więc nie
    dokona postępu), więc zostanie użyte [apply H], które zmieni
    cel. Wobec tego [apply H0 || apply H] na pierwszym podcelu
    będzie miało taki sam efekt, jak użycie [apply H]. W drugim
    podcelu [apply H0] skończy się sukcesem, więc tu [apply H0 ||
    apply H] będzie miało taki sam efekt, jak [apply H0]. *)

(** ** [idtac], [do] oraz [repeat] *)

Lemma idtac_do_example :
  forall P Q R S : Prop,
    P -> S \/ R \/ Q \/ P.
Proof.
  idtac. intros. do 3 right. assumption.
Qed.

(** [idtac] to taktyka identycznościowa, czyli taka, która nic
    nic robi. Sama w sobie nie jest zbyt użyteczna, ale przydaje
    się do czasem do tworzenia bardziej skomplikowanych taktyk.

    Kombinator [do] pozwala nam użyć danej taktyki określoną ilość
    razy. [do n t] na obecnym celu używa [t]. Jeżeli [t] zawiedzie,
    to [do n t] również zawiedzie. Jeżeli [t] skończy się sukcesem,
    to na każdym podcelu wygenerowanym przez [t] użyte zostanie
    [do (n - 1) t]. W szczególności [do 0 t] działa jak [idtac],
    czyli kończy się sukcesem nic nie robiąc.

    W naszym przypadku użycie taktyki [do 3 right] sprawi, że
    przy wyborze członu dysjunkcji, którego chcemy dowodzić,
    trzykrotnie pójdziemy w prawo. Zauważmy, że taktyka [do 4 right]
    zawiodłaby, gdyż po 3 użyciach [right] cel nie byłby już
    dysjunkcją, więc kolejne użycie [right] zawiodłoby, a wtedy
    cała taktyka [do 4 right] również zawiodłaby. *)

Lemma repeat_example :
  forall P A B C D E F : Prop,
    P -> A \/ B \/ C \/ D \/ E \/ F \/ P.
Proof.
  intros. repeat right. assumption.
Qed.

(** Kombinator [repeat] powtarza daną taktykę, aż ta rozwiąże cel,
    zawiedzie, lub nie zrobi postępu. Formalnie: [repeat t] używa
    na obecnym celu taktyki [t]. Jeżeli [t] rozwiąże cel, to
    [repeat t] kończy się sukcesem. Jeżeli [t] zawiedzie lub nie
    zrobi postępu, to [repeat t] również kończy się sukcesem.
    Jeżeli [t] zrobi jakiś postęp, to na każdym wygenerowaym przez
    nią celu zostanie użyte [repeat t].

    W naszym przypadku [repeat right] ma taki efekt, że przy wyborze
    członu dysjunkcji wybieramy człon będący najbardziej na prawo,
    tzn. dopóki cel jest dysjunkcją, aplikowana jest taktyka [right],
    która wybiera prawy człon. Kiedy nasz cel przestaje być dysjunkcją,
    taktyka [right] zawodzi i wtedy taktyka [repeat right] kończy swoje
    działanie sukcesem. *)

(** ** [try] i [fail] *)

Lemma iff_intro4 :
  forall P Q : Prop,
    (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof.
  split; intros; try (apply H0; assumption; fail);
  try (apply H; assumption; fail).
Qed.

(** [try] jest kombinatorem, który zmienia zachowanie przekazanej mu
    taktyki. Jeżeli [t] zawiedzie, to [try t] zadziała jak [idtac],
    czyli nic nie zrobi i skończy się sukcesem. Jeżeli [t] skończy się
    sukcesem, to [try t] również skończy się sukcesem i będzie miało
    taki sam efekt, jak [t]. Tak więc, podobnie jak [repeat], [try]
    nigdy nie zawodzi.

    [fail] jest przeciwieństwem [idtac] — jest to taktyka, która zawsze
    zawodzi. Sama w sobie jest bezużyteczna, ale w tandemie z [try]
    oraz średnikiem daje nam pełną kontrolę nad tym, czy taktyka
    zakończy się sukcesem, czy zawiedzie, a także czy dokona postępu.

    Częstym sposobem użycia [try] i [fail] jest [try (t; fail)]. Taktyka
    ta na obecnym celu używa [t]. Jeżeli [t]
    rozwiąże cel, to [fail] nie zostanie wywołane i całe [try (t; fail)]
    zadziała tak jak [t], czyli rozwiąże cel. Jeżeli [t] nie rozwiąże celu,
    to na wygenerowanych podcelach wywoływane zostanie [fail], które
    zawiedzie — dzięki temu [t; fail] również zawiedzie, nie dokonując
    żadnych zmian w celu (nie dokona postępu), a całe [try (t; fail)]
    zakończy się sukcesem, również nie dokonując w celu żadnych zmian.
    Wobec tego działanie [try (t; fail)] można podsumować tak: "jeżeli [t]
    rozwiąże cel to użyj jej, a jeżeli nie, to nic nie rób".

    Postaraj się dokładnie zrozumieć, jak opis ten ma się do powyższego
    przykładu — spróbuj usunąć jakieś [try], [fail] lub średnik i zobacz,
    co się stanie.

    Oczywiście przykład ten jest bardzo sztuczny — najlepszym pomysłem
    udowodnienia tego twierdzenia jest użycie ogólnej postaci średnika
    [t; t1 | ... | tn], tak jak w przykładzie [iff_intro'']. Idiom
    [try (t; fail)] najlepiej sprawdza się, gdy użycie średnika w ten
    sposób jest niepraktyczne, czyli gdy celów jest dużo, a rozwiązać
    automatycznie potrafimy tylko część z nich. Możemy użyć go wtedy,
    żeby pozbyć się prostszych przypadków nie zaśmiecając sobie jednak
    kontekstu w pozostałych przypadkach. Idiom ten jest też dużo
    bardziej odporny na przyszłe zmiany w programie, gdyż użycie go
    nie wymaga wiedzy o tym, ile podcelów zostanie wygenerowanych.

    Przedstawione kombinatory są najbardziej użyteczne i stąd
    najpowszechniej używane. Nie są to jednak wszystkie kombinatory
    — jest ich znacznie więcej. Opisy taktyk i kombinatorów
    z biblioteki standardowej znajdziesz tu:
    https://coq.inria.fr/refman/coq-tacindex.html *)

(** * Logika pierwszego rzędu a logika wyższego rzędu (TODO) *)

(** ** Logika pierwszego rzędu (TODO) *)

(** ** Logika wyższego rzędu (TODO) *)

(** ** Taktyka [firstorder] (TODO) *)

(** * Paradoksy autoreferencji *)

(** ** Paradoks Curry'ego *)

Lemma Curry's_paradox :
  forall P Q : Prop,
    (P <-> (P -> Q)) -> Q.
Proof.
  destruct 1.
  apply H.
    apply H0. intro. apply H; assumption.
    apply H0. intro. apply H; assumption.
Qed.

(** **** Ćwiczenie *)

(** TODO: napisać polecenie *)

(* begin hide *)
Lemma mutual_reference :
  forall P Q : Prop,
    (P <-> (Q <-> True)) ->
    (Q <-> (P <-> False)) ->
      False.
Proof.
  firstorder.
Qed.
(* end hide *)

(** ** Paradoks golibrody *)

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

(** ** Inne paradoksy autoreferencji: paradoks Richarda, słowa heterologiczne *)

(** **** Ćwiczenie *)

(** Poniższą zagadkę pozwolę sobie wesoło nazwać "paradoks hetero". Zagadka
    brzmi tak:

    Niektóre słowa opisują same siebie, np. słowo "krótki" jest krótkie,
    a niektóre inne nie, np. słowo "długi" nie jest długie. Podobnie słowo
    "polski" jest słowem polskim, ale słowo "niemiecki" nie jest słowem
    niemieckim. Słowa, które nie opisują samych siebie będziemy nazywać
    słowami heterologicznymi. Pytanie: czy słowo "heterologiczny" jest
    heterologiczne? *)

(** **** Ćwiczenie *)

(** A jak jest z poniższym paradoksem wujka Janusza?

    Wujek Janusz lubi tych (i tylko tych) członków rodziny, którzy sami
    siebie nie lubią oraz nie lubi tych (i tylko tych), którzy sami siebie
    lubią. Czy wujek Janusz lubi sam siebie? *)

(** **** Ćwiczenie *)

(** Powyższe ćwiczenie miało być ostatnim, ale co tam, dam jeszcze trochę.
    Co czuje serce twoje (ewentualnie: co widzisz przed oczyma duszy swojej)
    na widok poniższych wesołych zdań?

    "To zdanie jest fałszywe."

    "Zdanie po prawej jest fałszywe. Zdanie po lewej jest prawdziwe."

    "Zdanie po prawej jest prawdziwe. Zdanie po lewej jest fałszywe."
*)

(** * Predykatywizm (TODO) *)

(* begin hide *)
(* TODO: tutaj opisać impredykatywne definicje spójników *)
(* end hide *)

(** * Spójniki pozytywne i negatywne (TODO) *)

(** TODO:
  - równoważność jest negatywna
  - słaba negacja jest negatywna
  - silna negacja jest pozytywna
  - fałsz jest pozytywny *)

(** * Esencjalizm vs strukturalizm *)

(** * Kodowania impredykatywne (TODO) *)

(* begin hide *)
(*
TODO: Tautologie na kodowaniach impredykatywnych jako ćwiczenia z funkcji anonimowych
*)
(* end hide *)

Definition iand (P Q : Prop) : Prop :=
  forall C : Prop, (P -> Q -> C) -> C.

Definition ior (P Q : Prop) : Prop :=
  forall C : Prop, (P -> C) -> (Q -> C) -> C.

Definition iTrue : Prop :=
  forall C : Prop, C -> C.

Definition iFalse : Prop :=
  forall C : Prop, C.

Lemma iand_spec :
  forall P Q : Prop,
    iand P Q <-> P /\ Q.
(* begin hide *)
Proof.
  unfold iand. split.
    intro H. apply H. intros p q. split.
      assumption.
      assumption.
    intros [p q] C H. apply H.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma ior_spec :
  forall P Q : Prop,
    ior P Q <-> P \/ Q.
(* begin hide *)
Proof.
  unfold ior. split.
    intro H. apply H.
      intro p. left. assumption.
      intro q. right. assumption.
    intros [p | q] C pc qc.
      apply pc. assumption.
      apply qc. assumption.
Qed.
(* end hide *)

Lemma iTrue_spec :
  iTrue <-> True.
(* begin hide *)
Proof.
  unfold iTrue. split.
    intros _. trivial.
    intros _ C c. assumption.
Qed.
(* end hide *)

Lemma iFalse_False :
  iFalse <-> False.
(* begin hide *)
Proof.
  unfold iFalse. split.
    intro H. apply H.
    contradiction.
Qed.
(* end hide *)

Definition iexists (A : Type) (P : A -> Prop) : Prop :=
  forall C : Prop, (forall x : A, P x -> C) -> C.

Lemma iexists_spec :
  forall (A : Type) (P : A -> Prop),
    iexists A P <-> exists x : A, P x.
(* begin hide *)
Proof.
  unfold iexists. split.
    intro H. apply H. intros x p. exists x. assumption.
    intros [x p] C H. apply (H x). assumption.
Qed.
(* end hide *)

Definition ieq {A : Type} (x y : A) : Prop :=
  forall C : Prop, ((x = y) -> C) -> C.

Definition ieq' {A : Type} (x : A) : A -> Prop :=
  fun y : A =>
    forall P : A -> Prop, P x -> P y.

Lemma ieq_spec :
  forall (A : Type) (x y : A),
    ieq x y <-> x = y.
(* begin hide *)
Proof.
  unfold ieq. split.
    intro H. apply H. trivial.
    intros [] C H. apply H. reflexivity.
Qed.
(* end hide *)

Lemma ieq'_spec :
  forall (A : Type) (x y : A),
    ieq' x y <-> x = y.
(* begin hide *)
Proof.
  unfold ieq'. split.
    intro H. apply H. reflexivity.
    intros [] P px. assumption.
Qed.
(* end hide *)

(** * Harmonia logiki konstruktywnej (TODO) *)

(** * Logika intuicjonistyczna jako logika certyfikatów (TODO) *)

(** * Aksjomaty i pojęcie "tabu" (TODO) *)

(** * Klasyfikacja zdań (TODO) *)

(** Tutaj drobna klasyfikacja na coś w stylu:
    - zdania prawdziwe ([P] zachodzi)
    - zdania fałszywe ([~ P] zachodzi)
    - zdania niezaprzeczalne ([~ ~ P] zachodzi)
    - zdania kontyngentne ([P] jest fałszywym zdaniem postaci
      [forall x : A, Q x] i zachodzi [exists x : A, Q x]. Inne
      podejście: tylko w kontekście, w którym zdanie [P] składa
      się z nieznanych części, np. [P -> Q] jest kontyngentne,
      bo [P -> P] zachodzi, zaś [True -> False] nie zachodzi.
    - zdania klasycznie prawdziwe ([P] zachodzi w logice klasycznej)
    - zdania tabu ([P] implikuje jakieś inne tabu, np. [LEM])

    TODO: być może dać to do podrozdziału o [WLEM] *)