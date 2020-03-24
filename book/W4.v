(** * W4: Inne logiki [schowane na końcu dla niepoznaki] *)

(** * Porównanie logiki konstruktywnej i klasycznej *)

(** * Pluralizm logiczny *)

(** * Inne logiki? *)

(** * Logika de Morgana *)

(** jako coś pomiędzy logiką konstruktywną i klasyczną *)

(** * Dziwne aksjomaty i płynące z nich logiki *)

Definition ProofIrrelevance : Prop :=
  forall (P : Prop) (p q : P), p = q.

Definition UIP : Prop :=
  forall (A : Type) (x y : A) (p q : x = y), p = q.

Definition K : Prop :=
  forall (A : Type) (x : A) (p : x = x), p = eq_refl x.

Definition PropositionalExtensionality : Prop :=
  forall P Q : Prop, (P <-> Q) -> P = Q.

(** * Logika modalna *)

(** Logiki modalne to logiki, w których oprócz znanych nam już spójników
    czy kwantyfikatorów występują też modalności. Czym jest modalność?
    Najpierw trochę etymologii.

    Łacińskie słowo "modus" oznacza "sposób". Występuje ono w takich
    frazach jak "modus operandi" ("sposób działania") czy "modus vivendi"
    ("sposób życia"; po dzisiejszemu powiedzielibyśmy "styl życia",
    a amerykańce - "way of life"). Od niego pochodzi przymiotnik
    "modalis", który oznacza "dotyczący sposobu", a od niego pochodzą
    francuskie "modalité" czy angielskie "modality", które znaczą
    mniej więcej to samo co oryginalne łacińskie "modus", czyli
    "sposób", ale już w nieco innym kontekście.

    W językach naturalnych modalności często występują pod postacią
    czasowników zwanych na ich cześć modalnymi, takich jak "móc" czy
    "musieć" - o ile nie mieszkasz na pustyni pod kamieniem, to pewnie
    spotkałeś się z nimi ucząc się języków obcych.

    Jednak nas bardziej będzie interesować inna forma, pod którą
    modalności występują, a są to przysłówki. Porównajmy poniższe
    zdania:
    - Pada deszcz.
    - Być może pada deszcz.
    - Na pewno pada deszcz.

    Wszystkie mówią o tym samym zjawisku, czyli deszczu, ale robią to
    w różny sposób (i ten sposób to właśnie modalność!) - pierwszy
    sposób jest neutralny, drugi wyraża możliwość, a trzeci pewność.

    Najpopularniejsze logiki modalne skupiają się na próbie formalizacji
    właśnie tych dwóch sposobów - możliwości i konieczności. Nie będziemy
    ich jednak tutaj omawiać, gdyż, z punktu widzenia zarówno matematyki
    jako i informatyki, tego typu logiki są zupełnie bezużyteczne.

    Zamiast tego spojrzymy jeszcze raz na rzeczy, które już znamy, a
    których nawet nie podejrzewamy o bycie modalnościami. Najpierw
    jednak pół-formalna definicja modalności:

    [M] jest modalnością, gdy:
    - [M : Prop -> Prop], czyli [M] przekształca zdania w zdania
    - [forall P Q : Prop, (P -> Q) -> (M P -> M Q)]
    - [forall P : Prop, P -> M P]
    - [forall P : Prop, M (M P) -> M P]

    Cóż to wszystko oznacza? Jeżeli [P] jest zdaniem, to [M P] również
    jest zdaniem, które możemy rozumieć jako "P zachodzi w sposób M".
    Dla przykładu, jeżeli [P] znaczy "pada deszcz", a [M] wyraża
    możliwość, to wtedy [M P] znaczy "być może pada deszcz".

    Pierwsze prawo mówi, że modalność jest kompatybilna z konsekwencjami
    danego zdania. Niech [Q] znaczy "jest mokro". Wtedy [P -> Q] znaczy
    "jeżeli pada deszcz, to jest mokro". Kompatybilność znaczy, że możemy
    stąd wywnioskować [M P -> M Q], czyli "jeżeli być może pada deszcz,
    to być może jest mokro".

    Drugie prawo mówi, że jeżeli zdanie [P] po prostu zachodzi, to
    zachodzi też w sposób [M]: "jeżeli pada deszcz, to być może pada
    deszcz". Można to interpretować tak, że modalność modyfikuje
    znaczenie danego zdania, ale nie wywraca go do góry nogami. Dla
    przykładu modalnością NIE JEST negacja, gdyż nie spełnia ona tego
    warunku. Poetycko można by powiedzieć, że zaprzeczenie nie jest
    sposobem twierdzenia, a nieistnienie nie jest sposobem istnienia.

    Trzecie prawo mówi, że potworki w rodzaju "może może może może
    pada deszcz" znaczą to samo, co "może pada deszcz" (ale już
    niekoniecznie to samo, co po prostu "pada deszcz"). Jest to
    dość rozsądne, gdyż w językach naturalnych zazwyczaj tak nie
    mówimy. A jeżeli już mówimy, np. "bardzo bardzo boli mnie dupa" -
    to znaczy, że słowo "bardzo" w tym wypadku nie wyraża sposobu
    bolenia dupy, lecz raczej stopień/intensywność bólu, a zatem
    "bardzo" NIE JEST modalnością.

    Zanim zobaczymy, jak ta definicja ma się do tego, co już wiemy
    i potrafimy, zadanie: *)

(** **** Ćwiczenie *)

(** Udowodnij, że negacja nie jest modalnością. Parafrazując:
    - napisz, jak wyglądałyby prawa bycia modalnością dla negacji
    - zdecyduj, które z praw negacja łamie, a których nie
    - udowodnij, że prawa te faktycznie nie zachodzą *)

(* begin hide *)
Lemma neg_law1_fails :
  ~ forall P Q : Prop, (P -> Q) -> (~ P -> ~ Q).
Proof.
  intro H.
  apply (H False True).
    trivial.
    intro. assumption.
    trivial.
Qed.

Lemma neg_law2_fails :
  ~ forall P : Prop, P -> ~ P.
Proof.
  intro H.
  apply (H True); trivial.
Qed.
(* end hide *)

(** ** Niespodziewana modalność - niezaprzeczalność *)

(** Wiemy już, że negacja nie jest modalnością. Świetnie, ale w takim
    razie, co nią jest? Otóż przykładem modalności jest... podwójna
    negacja!

    Ha, nie spodziewałeś się podwójnej negacji w tym miejscu, co?
    Nie ma się czemu dziwić - w języku polskim podwójna negacja w
    stylu "nikt nic nie wie" wyraża tak naprawdę pojedynczą negację
    (choć nazwa "podwójna negacja" jest tu niezbyt trafna - bo słowo
    "nie" występuje tylko raz, a słowa takie jak "nikt" czy "nic"
    mają wprawdzie znaczenie negatywne, ale formą negacji nie są),
    w angielskim natomiast zdanie podwójnie zanegowane ("it's not
    uncommon") znaczy to samo, co zdanie oznajmiające bez żadnej
    negacji ("it's common").

    Odstawmy jednak na bok języki naturalne i zastanówmy się, jakąż to
    modalność wyraża podwójna negacja w naszej Coqowej logice. W tym
    celu przyjrzyjmy się poniższym zdaniom:
    - [P] - po prostu stwierdzamy [P], modalność neutralna
    - [~ P] - zaprzeczamy/obalamy [P]. Można zatem powiedzieć, że [P]
      jest zaprzeczalne.
    - [~ ~ P] - zaprzeczamy/obalamy [~ P], czyli zaprzeczamy zaprzeczeniu
      [P]. Można zatem powiedzieć, że [P] jest niezaprzeczalne.

    I bum, dokonaliśmy naszego odkrycia: podwójna negacja wyraża
    bardzo subtelną modalność, jaką jest niezaprzeczalność. [~ ~ P]
    możemy zatem odczytywać jako "niezaprzeczalnie P".

    Czym różni się samo "P" od "niezaprzeczalnie P"? Dla lepszego
    zrozumienia prześledźmy to na znanym nam już przykładzie, czyli
    aksjomacie wyłączonego środka.

    Weźmy dowolne zdanie [P]. Nie jesteśmy w stanie udowodnić [P \/ ~ P],
    gdyż bez żadnej wiedzy o zdaniu [P] nie jesteśmy w stanie zdecydować,
    czy iść w lewo czy w prawo. Jeśli jednak jakiś cwaniak będzie chciał
    wcisnąć nam kit, że [~ (P \/ ~ P)], to możemy wziąć jego dowód i
    wyprowadzić z niego [False], czyli po prostu udowodnić, że
    [~ ~ (P \/ ~ P)]. Na tym właśnie polega modalność niezaprzeczalności:
    nawet jeżeli nie da się zdania pokazać wprost, to można obalić jego
    zaprzeczenie. *)

(** **** Ćwiczenie *)

(** Pokaż, że podwójna negacja jest modalnością. *)

Lemma not_not_law1 :
  forall P Q : Prop, (P -> Q) -> (~ ~ P -> ~ ~ Q).
(* begin hide *)
Proof.
  intros P Q H nnp nq.
  apply nnp. intro p.
  apply nq. apply H.
  assumption.
Qed.
(* end hide *)

Lemma not_not_law2 :
  forall P : Prop, P -> ~ ~ P.
(* begin hide *)
Proof.
  intros P p np.
  apply np, p.
Qed.
(* end hide *)

Lemma not_not_law3 :
  forall P : Prop, ~ ~ ~ ~ P -> ~ ~ P.
(* begin hide *)
Proof.
  intros P n4p np.
  apply n4p. intro n2p.
  apply n2p, np.
Qed.
(* end hide *)

(** ** Logika klasyczna jako logika modalna *)

Require Import W3.

(** Kolejny przykład modalności jest jeszcze bardziej zaskakujący
    od poprzedniego. Jest to modalność, którą można wyrazić za
    pomocą słowa "klasycznie". Wyrażenie "klasycznie P" znaczy,
    że [P] zachodzi pod warunkiem, że mamy do dyspozycji prawa
    logiki klasycznej (jak np. prawo wyłączonego środka).

    Formalnie modalność tę możemy zrealizować za pomocą implikacji
    oraz dowolnego z poznanych przez nas dotychczas aksjomatów, które
    dają nam pełną moc logiki klasyczne. Dla przykładu: "klasycznie P"
    możemy wyrazić równoważnie jako [LEM -> P], [DNE -> P], [Contra -> P]
    i tak dalej.

    Modalność ta jest bardzo wygodnym sposobem na posługiwanie się
    logiką klasyczną bez brudzenia sobie rączek aksjomatami, a mimo
    to nie jest zbyt powszechnie znana czy używana. Cóż...

    Oczywiście modalności można użyć nie tylko do wygodnego użytkowania
    aksjomatów logiki klasycznej, ale również wszystkich innych
    aksjomatów, jakie sobie zażyczymy. *)

(** **** Ćwiczenie *)

(** Udowodnij, że "klasycznie" (wyrażone za pomocą [LEM]) faktycznie
    jest modalnością. *)

Lemma classically_law1 :
  forall P Q : Prop, (P -> Q) -> ((LEM -> P) -> (LEM -> Q)).
(* begin hide *)
Proof.
  intros P Q H lemp lem.
  apply H, lemp, lem.
Qed.
(* end hide *)

Lemma classically_law2 :
  forall P : Prop, P -> (LEM -> P).
(* begin hide *)
Proof.
  intros P p lem.
  assumption.
Qed.
(* end hide *)

Lemma classically_law3 :
  forall P : Prop, (LEM -> (LEM -> P)) -> (LEM -> P).
(* begin hide *)
Proof.
  intros P H lem.
  apply H; assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Dwie z pozoru różne modalności mogą tak naprawdę wyrażać to samo.
    Dla przykładu, modalność "klasycznie P" możemy wyrazić nie tylko
    jako [LEM -> P], ale również jako [DNE -> P].

    Pokaż, że obydwie definicje tej modalności są równoważne. *)

Lemma classicallies :
  forall P : Prop, (LEM -> P) <-> (DNE -> P).
(* begin hide *)
Proof.
  split.
    intros H dne. apply H, DNE_LEM. assumption.
    intros H lem. apply H. exact (LEM_DNE lem).
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Gdyby powyższe ćwiczenie okazało się zbyt oczywiste, to wiedz, że
    naprawdę pozornie różne modalności mogą ostatecznie okazać się tym
    samym. Może się też okazać, że modalność [M] jest silniejsza niż
    modalność [N], czyli że [forall P : Prop, M P -> N P].

    Zastanów się, jaki jest związek między modalnościmi
    "niezaprzeczalnie" i "klasycznie". Czy są one tym samym, czy czymś
    innym? Czy któraś z nich jest mocniejsza od drugiej? *)

(* begin hide *)

Lemma irrefutably_classically :
  forall P : Prop,
    (~ ~ P) -> (LEM -> P).
Proof.
  intros P nnp LEM. destruct (LEM P).
    assumption.
    contradiction.
Qed.

(** O ile mnie rozum nie myli, to w drugą stronę się nie da. Nie da się
    też rzecz jasna zaprzeczyć, a zatem zdaje się, że podwójna negacja
    jest mocniejsza od modalności klasycznej. *)

(* end hide *)

(** ** Modalność pośrednia *)

(** Poznawszy dwie najważniejsze dla nas modalności, możemy zająć się
    takimi, które będą miały co najwyżej charakter ciekawostki. Jeżeli
    nie lubisz ciekawostek i jesteś ogólnie smutnym człowiekiem, to
    resztę omawianych modalności możesz pominąć.

    Modalność pośrednia to... zamiast gadać, przekonaj się sam. *)

(** **** Ćwiczenie *)

(** Udowodnij, że modalność pośrednia jest modalnością. *)

Lemma indirect_law1 :
  forall P Q : Prop,
    (P -> Q) -> ((forall R : Prop, (P -> R) -> R) ->
                 (forall R : Prop, (Q -> R) -> R)).
(* begin hide *)
Proof.
  intros P Q PQ mp R QR.
  apply QR, mp.
  assumption.
Qed.
(* end hide *)

Lemma indirect_law2 :
  forall P : Prop,
    P -> (forall R : Prop, (P -> R) -> R).
(* begin hide *)
Proof.
  intros P p R PR.
  apply PR.
  assumption.
Qed.
(* end hide *)

Lemma indirect_law3 :
  forall P : Prop,
    (forall R : Prop, ((forall R' : Prop, (P -> R') -> R') -> R) -> R) ->
      (forall R : Prop, (P -> R) -> R).
(* begin hide *)
Proof.
  intros P H R PR.
  apply H.
  intro H'.
  apply H'.
  assumption.
Qed.
(* end hide *)

(** No dobra, dowody dowodami, ćwiczenia ćwiczeniami, ale o co tak
    naprawdę chodzi z tą modalnością pośrednią? Jaki sposób wyraża?
    Skąd nazwa?

    Przyjrzyjmy się jeszcze raz definicji. Zdanie "pośrednio P"
    formalnie wygląda tak: [forall R : Prop, (P -> R) -> R].

    Jak odczytać tę definicję? Zacznijmy od tego, że [R] jest dowolnym
    zdaniem. Dalsza część mówi, że jeżeli [P] implikuje [R], to [R].
    Oczywiście [P -> R] możemy odczytać także jako "R jest konsekwencją
    P", a zatem całą definicję możemy odczytać: zachodzi każda
    konsekwencja [P].

    Zachodzi każda konsekwencja [P]... ciekawe, co? Zastanówmy się, w
    jakich sytuacjach mogą zachodzi wszystkie konsekwencje [P]:
    - [P] zachodzi - najprostszy przypadek. Skoro [P] zachodzi, to
      jego konsekwencje też. Wszystkie. Bez wyjątku.
    - zachodzi coś mocniejszego od [P], tzn. zachodzi [Q] i [Q -> P].
      Zachodzą wszystkie konsekwencje [P] i być może różne rzeczy,
      które konsekwencjami [P] nie są (bo są np. konsekwencjami [Q])

    Widzimy więc, że by zaszły wszystkie konsekwencje [P], to zachodzić
    musi [P] lub coś od [P] mocniejszego. Jednak rzeczy mocniejsze od
    [P] nas tutaj nie interesują - liczy się dla nas najsłabsza z tych
    wszystkich możliwości, czyli samo [P].

    Widać więc (albo i nie, być może moje tłumaczenie jest zagmatwane),
    że z punktu widzenia konsekwencji danego zdania, zdanie [P] oraz
    zdanie "zachodzą wszystkie konsekwencje P" są równoważne. Wobec
    tego możemy stwierdzić, że zdanie "zachodzą wszystkie konsekwencje
    P" to pewien sposób powiedzenia [P], tylko w bardzo pośredni sposób.
    Stąd też nazwa (swoją drogą, wymyślona autorsko przeze mnie) -
    modalność pośrednia. *)

(** **** Ćwiczenie *)

(** Pokaż, że jeżeli zachodzą wszystkie konsekwencje [P], to [P] też
    zachodzi. Wskazówka: każde zdanie wynika samo z siebie. *)

Lemma all_consequences :
  forall P : Prop,
    (forall R : Prop, (P -> R) -> R) -> P.
(* begin hide *)
Proof.
  intros P H.
  apply H.
  trivial.
Qed.
(* end hide *)

(** Jakiż wniosek płynie z ćwiczenia? Ano, ponieważ udało nam się
    pokazać zarówno [P -> (forall R : Prop, (P -> R) -> R)] (prawo
    [indirect_law2], wymagane przez definicję modalności) jak i
    [(forall R : Prop, (P -> R) -> R) -> P] (powyższe ćwiczenie),
    wniosek może być tylko jeden: modalność pośrednia jest dokładnie
    tym samym, co modalność bezpośrednia, czyli neutralna! Ha! Nie
    tego się spodziewałeś, co? *)

(** ** Modalność "... albo i nie" *)

(** ** Modalność banalna *)

(** ** Pies zjadł mi dowód... :( *)

(** Wyobraźmy sobie następujący dialog, odbywający się na lekcji
    języka polskiego w jakiejś zapomnianej przez Boga szkole w
    Pcimiu Dolnym:
    - (N)auczycielka: Jasiu, zrobiłeś zadanie?
    - (J)asiu: tak, psze pani.
    - N: pokaż.
    - J: Hmmm, yhm, uhm, eeee...
    - N: czyli nie zrobiłeś.
    - J: zrobiłem, ale pies mi zjadł.

    Z dialogu jasno wynika, że Jasiu nie zrobił zadania, co jednak nie
    przeszkadza mu w pokrętny sposób twierdzić, że zrobił. Ten pokrętny
    sposób jest powszechnie znany jako "wymówka".

    Słowem kluczowym jest tutaj słowo "sposób", które już na pierwszy
    rzut oka pachnie modalnością. Coś jest na rzeczy, wszakże podanie
    wymówki jest całkiem sprytnym sposobem na uzasadnienie każdego
    zdania:
    - Mam dowód fałszu!
    - Pokaż.
    - Pies mi zjadł.

    Musimy pamiętać tylko o dwóch ważnych szczegółach całego procederu.
    Po pierwsze, nasza wymówka musi być uniwersalna, czyli musimy się
    jej trzymać jak rzep psiego ogona - nie możemy w trakcie rozumowania
    zmienić wymówki, bo rozumowanie może się zawalić.

    Drugi, nieco bardziej subtelny detal jest taki, że nie mamy tutaj
    do czynienia po prostu z "modalnością wymówkową". Zamiast tego,
    każdej jednej wymówce odpowiada osobna modalność. A zatem mamy
    modalność "Pies mi zjadł", ale także modalność "Nie mogę teraz
    dowodzić, bo państwo Izrael bezprawnie okupuje Palestynę"... i
    wiele innych.

    Jak można tę modalność zareprezentować formalnie w Coqu? Jeżeli
    [E] jest naszą wymówką, np. "Pies zjadł mi dowód", zaś [P]
    właściwym zdaniem, np. "Pada deszcz", to możemy połączyć je za
    pomocą dysjunkcji, otrzymując [P \/ E], czyli "Pada deszcz lub
    pies zjadł mi dowód". *)

(** **** Ćwiczenie *)

(** Udowodnij, że dla każdej wymówki [E] faktycznie mamy do czynienia
    z modalnością. *)

Lemma excuse_law1 :
  forall E P Q : Prop,
    (P -> Q) -> (E \/ P -> E \/ Q).
(* begin hide *)
Proof.
  intros E P Q pq [e | p].
    left. assumption.
    right. apply pq. assumption.
Qed.
(* end hide *)

Lemma excuse_law2 :
  forall E P : Prop, P -> E \/ P.
(* begin hide *)
Proof.
  intros E P p.
  right.
  assumption.
Qed.
(* end hide *)

Lemma excuse_law3 :
  forall E P : Prop,
    E \/ (E \/ P) -> E \/ P.
(* begin hide *)
Proof.
  intros E P [e | [e | p]].
    left. assumption.
    left. assumption.
    right. assumption.
Qed.
(* end hide *)

(** * Inne logiki - podsumowanie *)

(** krótkie, acz realistyczne (logiki parakonsystentne to guwno) *)

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

(** * Zadania *)

(** rozwiąż wszystkie zadania jeszcze raz, ale tym razem bez używania
    Module/Section/Hypothesis oraz z jak najkrótszymi dowodami *)

(** * Jakieś podsumowanie *)

(** - taktyka firstorder
    - zrobić test diagnostyczny tak/nie
    - fiszki do nauki nazw praw *)