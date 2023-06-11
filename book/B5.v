(** * B5: Logika modalna *)

From Typonomikon Require Export B4z.

(** Jako się rzekło, modalności takie jak możliwość, konieczność, czas,
    wiedza czy dowodliwość nie będą nas w tej książce interesować, lecz
    nie znaczy to, że nie będą interesować nas modalności w ogóle.

    W niniejszym podrozdziale spojrzymy jeszcze raz na rzeczy, które już
    znamy, a których nawet nie podejrzewamy o bycie modalnościami. Zanim
    to jednak nastąpi, zobaczmy pół-formalną definicję modalności:

    [M] jest modalnością, gdy:
    - [M : Prop -> Prop], czyli [M] przekształca zdania w zdania
    - [forall P Q : Prop, (P -> Q) -> (M P -> M Q)]
    - [forall P : Prop, P -> M P]
    - [forall P : Prop, M (M P) -> M P]

    Cóż to wszystko oznacza? Jeżeli [P] jest zdaniem, to [M P] również
    jest zdaniem, które możemy rozumieć jako "P zachodzi w sposób M".
    Dla przykładu, jeżeli [P] znaczy "pada deszcz", a [M] wyraża
    możliwość, to wtedy [M P] znaczy "być może pada deszcz".

    Pierwsze prawo mówi, że modalność jest kompatybilna z konsekwencjami
    danego zdania. Niech [Q] znaczy "jest mokro". Wtedy [P -> Q] znaczy
    "jeżeli pada deszcz, to jest mokro". Kompatybilność znaczy, że możemy
    stąd wywnioskować [M P -> M Q], czyli "jeżeli być może pada deszcz,
    to być może jest mokro".

    Drugie prawo mówi, że jeżeli zdanie [P] po prostu zachodzi, to
    zachodzi też w sposób [M]: "jeżeli pada deszcz, to być może pada
    deszcz". Można to interpretować tak, że modalność modyfikuje
    znaczenie danego zdania, ale nie wywraca go do góry nogami. Dla
    przykładu modalnością NIE JEST negacja, gdyż nie spełnia ona tego
    warunku. Poetycko można by powiedzieć, że zaprzeczenie nie jest
    sposobem twierdzenia, a nieistnienie nie jest sposobem istnienia.

    Trzecie prawo mówi, że potworki w rodzaju "może może może może
    pada deszcz" znaczą to samo, co "może pada deszcz" (ale już
    niekoniecznie to samo, co po prostu "pada deszcz"). Jest to
    dość rozsądne, gdyż w językach naturalnych zazwyczaj tak nie
    mówimy. A jeżeli już mówimy, np. "bardzo bardzo boli mnie dupa" -
    to znaczy, że słowo "bardzo" w tym wypadku nie wyraża sposobu
    bolenia dupy, lecz raczej stopień/intensywność bólu, a zatem
    "bardzo" NIE JEST modalnością.

    Zanim zobaczymy, jak ta definicja ma się do tego, co już wiemy
    i potrafimy, ćwiczenie: *)

(** **** Ćwiczenie *)

(** Zaczniemy od antyprzykładu.

    Udowodnij, że negacja nie jest modalnością. Parafrazując:
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

(** * Modalność neutralna: nasza ulubiona *)

(** Jako już się rzekło w jednym z przykładów, zdanie "Pada deszcz"
    również jest zdaniem modalnym. Modalność występująca w tym zdaniu
    to modalność neutralna (zwana też modalnością identycznościową), a
    wyrażany przez nią sposób to sposób zwykły, domyślny, neutralny,
    czyli w sumie żaden.

    Modalność ta nie ma raczej większego znaczenia (oczywiście o ile
    przemilczymy fakt, że większość wszystkich zdań, jakie napotkamy,
    będzie wyrażać właśnie tę modalność), ale warto ją odnotować dla
    kompletności teorii - zwykli śmiertelnicy zazwyczaj zapominają o
    takich banalnych rzeczach, więc trzeba im o tym przypominać. Nie
    wspominając już o tym, że jest to idealna modalność na rozgrzewkę
    ... *)

(** **** Ćwiczenie *)

(** Pokaż, że modalność neutralna faktycznie jest modalnością. *)

Lemma neutrally_law1 :
  forall P Q : Prop, (P -> Q) -> (P -> Q).
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma neutrally_law2 :
  forall P : Prop, P -> P.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma neutrally_law3 :
  forall P : Prop, P -> P.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

(** * Modalność trywialna: meh... *)

(** Jest taka jedna modalność, o której aż wstyd wspominać, a którą na
    nasze potrzeby nazwiemy modalnością trywialną. Polega ona na tym, że
    chcąc w trywialny sposób powiedzieć [P], wypieprzamy zdanie [P] w
    diabły i zamiast tego mówimy [True]. Wot, modalność jak znalazł. *)

(** **** Ćwiczenie *)

(** Pokaż, że modalność trywialna faktycznie jest modalnością. *)

Lemma trivially_law1 :
  forall P Q : Prop, (P -> Q) -> (True -> True).
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma trivially_law2 :
  forall P : Prop, P -> True.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma trivially_law3 :
  forall P : Prop, True -> True.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Skoro [True] to modalność trywialna, to może [False] to modalność
    antytrywialna? Albo nietrywialna... albo jakaś inna, nieważne jak
    nazwana? Sprawdź to!

    Jeżeli jest to modalność, udowodnij odpowiednie prawa. Jeżeli
    nie, udowodnij zaprzeczenia odopwiednich praw. A może sytuacja
    jest patowa i nie da się udowodnić ani w jedną, ani w drugą
    stronę? *)

(* begin hide *)
Lemma antitrivial_law1 :
  forall P Q : Prop, (P -> Q) -> (False -> False).
Proof.
  trivial.
Qed.

Lemma antitrivial_law2 :
  ~ forall P : Prop, P -> False.
Proof.
  intro H.
  apply (H True).
  trivial.
Qed.

Lemma antitrivial_law3 :
  forall P : Prop, False -> False.
Proof.
  trivial.
Qed.
(* end hide *)

(** * Modalność wymówkowa: pies zjadł mi dowód... :( *)

(** To już ostatnia głupia i bezużyteczna modalność, obiecuję! Wszystkie
    następne będą już praktyczne i przydatne.

    Wyobraźmy sobie następujący dialog, odbywający się na lekcji
    dowodzenia w Coqu w jakiejś zapomnianej przez Boga szkole w
    Pcimiu Dolnym:
    - (N)auczycielka: Jasiu, zrobiłeś zadanie domowe?
    - (J)asiu: Tak, psze pani.
    - N: Pokaż.
    - J: Hmmm, yhm, uhm, eeee...
    - N: Czyli nie zrobiłeś.
    - J: Zrobiłem, ale pies mi zjadł.

    Z dialogu jasno wynika, że Jasiu nie zrobił zadania, co jednak nie
    przeszkadza mu w pokrętny sposób twierdzić, że zrobił. Ten pokrętny
    sposób jest powszechnie znany jako "wymówka".

    Słowem kluczowym jest tutaj słowo "sposób", które już na pierwszy
    rzut oka pachnie modalnością. Coś jest na rzeczy, wszakże podanie
    wymówki jest całkiem sprytnym sposobem na uzasadnienie każdego
    zdania:
    - Prawdziwy wyznawca: Mam dowód fałszu!
    - Sceptyk: Pokaż.
    - Prawdziwy wyznawca: Sorry, pies mi zjadł.

    Musimy pamiętać tylko o dwóch ważnych szczegółach całego procederu.
    Po pierwsze, nasza wymówka musi być uniwersalna, czyli musimy się
    jej trzymać jak rzep psiego ogona - nie możemy w trakcie rozumowania
    zmienić wymówki, bo rozumowanie może się zawalić.

    Drugi, nieco bardziej subtelny detal jest taki, że nie mamy tutaj
    do czynienia po prostu z "modalnością wymówkową". Zamiast tego,
    każdej jednej wymówce odpowiada osobna modalność. A zatem mamy
    modalność "Pies mi zjadł", ale także modalność "Nie mogę teraz
    dowodzić, bo państwo Izrael bezprawnie okupuje Palestynę"... i
    wiele innych.

    Jak można tę modalność zareprezentować formalnie w Coqu? Jeżeli [E] jest
    naszą wymówką, np. "Pies zjadł mi dowód", zaś [P] właściwym zdaniem, np.
    "Pada deszcz", to możemy połączyć je za pomocą dysjunkcji, otrzymując
    [P \/ E], czyli "Pada deszcz lub pies zjadł mi dowód". Jednak ze względu
    na pewne głęboko zakorzenione tradycje kulturowe modalność tę będziemy
    reprezentować jako [E \/ P], czyli "Pies zjadł mi dowód lub pada deszcz". *)

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

(** * Modalność klasyczna: logika klasyczna jako logika modalna *)

(** Poznana w poprzednim podrozdziale modalność mogła być dla ciebie
    dość zaskakująca, wszakże w języku naturalnym nieczęsto robienie
    wymówek jest wyrażane przez czasowniki modalne czy przysłówki. Co
    więcej, nie zobaczymy jej już nigdy więcej, bo jest mocno
    bezużyteczna.

    W niniejszym podrozdziale poznamy zaś modalność nawet bardziej
    zaskakującą, a do tego całkiem przydatną. Jest to modalność,
    którą można wyrazić za pomocą słowa "klasycznie". Wyrażenie
    "klasycznie P" znaczy, że [P] zachodzi w logice klasycznej,
    czyli zachodzi pod warunkiem, że mamy do dyspozycji poznane w
    poprzednich rozdziałach aksjomaty logiki klasycznej.

    Formalnie modalność tę możemy zrealizować za pomocą implikacji
    jako [LEM -> P]. Jest to bardzo wygodny sposób na posługiwanie
    się logiką klasyczną bez brudzenia sobie rączek komendami [Axiom]
    czy [Hypothesis], a mimo to nie jest zbyt powszechnie znany czy
    używany. Cóż... ci głupcy nie wiedzą, co tracą. *)

(** **** Ćwiczenie *)

(** Udowodnij, że modalność klasyczna faktycznie jest modalnością. *)

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

(** Dwie modalności zdefiniowane na różne (na pierwszym rzut oka)
    sposoby mogą mogą tak naprawdę wyrażać to samo. Dla przykładu,
    modalność "klasycznie P" możemy wyrazić nie tylko jako [LEM -> P],
    ale również jako [DNE -> P], [Contra -> P] i tak dalej - dowolny 
    z poznanych przez nas dotychczas aksjomatów, które dają nam pełną
    moc logiki klasycznej, zadziała tutaj tak samo.

    Pokaż, że definicja korzystająca z [LEM] jest równoważna tej, w
    której występuje [DNE]. *)

Lemma classicallyLEM_classicallyDNE :
  forall P : Prop, (LEM -> P) <-> (DNE -> P).
(* begin hide *)
Proof.
  split.
    intros H dne. apply H, DNE_LEM. assumption.
    intros H lem. apply H. exact (LEM_DNE lem).
Qed.
(* end hide *)

(** * Modalność aksjomatyczna *)

(** W poprzednim podrozdziale widzieliśmy, że użycie logiki klasycznej
    możemy wyrazić jako [LEM -> P], [DNE -> P] czy nawet [Contra -> P].
    A co z innymi aksjomatami, które dotychczas poznaliśmy? Czy ich
    użycie również możemy zareprezentować za pomocą jakiejś modalności?

    Ależ oczywiście, że tak. Skoro zamiast [LEM -> P] możemy napisać
    [DNE -> P], to możemy również napisać [UIP -> P], [PropExt -> P]
    czy po prostu [A -> P] dla dowolnego zdania [A].

    Okazuje się więc, że modalność klasyczna jest jedynie wcieleniem
    pewnej ogólniejszej modalności, którą na nasze potrzeby nazwiemy
    modalnością aksjomatyczną. Zdanie [A -> P] możemy odczytać jako
    "P, pod warunkiem że A". Widać jak na dłoni, że jest to pewien
    sposób na wyrażenie [P], a zatem pozostaje tylko sprawdzić, czy
    zachodzą wszystkie potrzebne prawa. *)

(** **** Ćwiczenie *)

(** Udowodnij, że modalność aksjomatyczna jest modalnością. *)

Lemma axiomatically_law1 :
  forall A P Q : Prop,
    (P -> Q) -> ((A -> P) -> (A -> Q)).
(* begin hide *)
Proof.
  intros A P Q pq ap a.
  apply pq, ap, a.
Qed.
(* end hide *)

Lemma axiomatically_law2 :
  forall A P : Prop,
    P -> (A -> P).
(* begin hide *)
Proof.
  intros A P p a.
  assumption.
Qed.
(* end hide *)

Lemma axiomatically_law3 :
  forall A P : Prop,
    (A -> (A -> P)) -> (A -> P).
(* begin hide *)
Proof.
  intros A P aap a.
  apply aap; assumption.
Qed.
(* end hide *)

(** Wypadałoby jeszcze wyjaśnić, dlaczego modalność aksjomatyczną
    nazwałem właśnie "aksjomatyczną", a nie na przykład "warunkową",
    "założeniową" albo coś w tym stylu.

    Powód tego jest prosty: dawanie jako dodatkowej przesłanki zdania,
    które nie jest potrzebne w dowodzie, jest dość kretyńskie. Ba!
    Jeżeli potrafimy udowodnić [A] bez aksjomatów, to [A -> P] jest
    równoważne [P]. *)

(** **** Ćwiczenie *)

(** Sprawdź to! *)

Lemma nonaxiomatically :
  forall A P : Prop,
    A -> ((A -> P) <-> P).
(* begin hide *)
Proof.
  intros A P a. split.
    intro ap. apply ap. assumption.
    intros p _. assumption.
Qed.
(* end hide *)

(** * Modalność niezaprzeczalna *)

(** Wiemy już, że negacja nie jest modalnością. Zaskoczy cię pewnie
    zatem fakt, że modalnością jest... podwójna negacja!

    Ha, nie spodziewałeś się podwójnej negacji w tym miejscu, co?
    Nie ma się czemu dziwić - w języku polskim podwójna negacja w
    stylu "nikt nic nie wie" wyraża tak naprawdę pojedynczą negację
    (choć nazwa "podwójna negacja" jest tu niezbyt trafna - bo słowo
    "nie" występuje tylko raz, a słowa takie jak "nikt" czy "nic"
    mają wprawdzie znaczenie negatywne, ale formą negacji nie są),
    w angielskim natomiast zdanie podwójnie zanegowane ("it's not
    uncommon") znaczy to samo, co zdanie oznajmiające bez żadnej
    negacji ("it's common").

    Odstawmy jednak na bok języki naturalne i zastanówmy się, jakąż to
    modalność wyraża podwójna negacja w naszej Coqowej logice. W tym
    celu przyjrzyjmy się poniższym zdaniom:
    - [P] - po prostu stwierdzamy [P], modalność neutralna
    - [~ P] - zaprzeczamy/obalamy [P]. Można zatem powiedzieć, że [P]
      jest zaprzeczalne. Pamiętajmy jednak, że negacja nie jest modalnością.
    - [~ ~ P] - zaprzeczamy/obalamy [~ P], czyli zaprzeczamy zaprzeczeniu
      [P]. Można zatem powiedzieć, że [P] jest niezaprzeczalne.

    I bum, dokonaliśmy naszego odkrycia: podwójna negacja wyraża
    bardzo subtelną modalność, jaką jest niezaprzeczalność. [~ ~ P]
    możemy zatem odczytywać jako "niezaprzeczalnie P".

    Czym różni się samo "P" od "niezaprzeczalnie P"? Dla lepszego
    zrozumienia prześledźmy to na znanym nam już przykładzie, czyli
    aksjomacie wyłączonego środka.

    Weźmy dowolne zdanie [P]. Nie jesteśmy w stanie udowodnić [P \/ ~ P],
    gdyż bez żadnej wiedzy o zdaniu [P] nie jesteśmy w stanie zdecydować
    czy iść w lewo, czy w prawo. Jeśli jednak jakiś cwaniak będzie chciał
    wcisnąć nam kit, że [~ (P \/ ~ P)], to możemy wziąć jego dowód i
    wyprowadzić z niego [False], czyli po prostu udowodnić, że
    [~ ~ (P \/ ~ P)]. Na tym właśnie polega modalność niezaprzeczalna:
    nawet jeżeli nie da się zdania pokazać wprost, to można obalić jego
    zaprzeczenie. *)

(** **** Ćwiczenie *)

(** Pokaż, że podwójna negacja jest modalnością. *)

Lemma irrefutably_law1 :
  forall P Q : Prop, (P -> Q) -> (~ ~ P -> ~ ~ Q).
(* begin hide *)
Proof.
  intros P Q H nnp nq.
  apply nnp. intro p.
  apply nq. apply H.
  assumption.
Qed.
(* end hide *)

Lemma irrefutably_law2 :
  forall P : Prop, P -> ~ ~ P.
(* begin hide *)
Proof.
  intros P p np.
  apply np, p.
Qed.
(* end hide *)

Lemma irrefutably_law3 :
  forall P : Prop, ~ ~ ~ ~ P -> ~ ~ P.
(* begin hide *)
Proof.
  intros P n4p np.
  apply n4p. intro n2p.
  apply n2p, np.
Qed.
(* end hide *)

(** * Modalność pośrednia *)

(** Obawiam się, że być może obawiasz się, że tłumaczenia z poprzedniego
    podrozdziału niczego tak naprawdę nie tłumaczą. Przyjrzyjmy się więc
    modalności niezaprzeczalnej jeszcze raz, tym razem pod nieco innym
    kątem.

    Zacznijmy od zapisania zdania "niezaprzeczalnie P" nie jako [~ ~ P],
    lecz jako [(P -> False) -> False]. Jak możemy skonstruować dowód
    takiego zdania? Cóż, jeżeli ktoś pokaże nam, że [P] prowadzi do
    sprzeczności, to my musimy pokazać mu dowód fałszu.

    Najłatwiej mamy, gdy dysponujemy dowodem [P] - wtedy sprzeczność jest
    natychmiastowa. Jeżeli nie mamy dowodu [P], musimy kombinować - jak
    pamiętamy, dla [~ ~ LEM] kombinacje te polegały na tym, że najpierw
    idziemy w prawo, a potem w lewo. Te kombinacje są istotą spososbu
    wyrażanego przez modalność niezaprzeczalną.

    Zauważmy, że powyższe tłumaczenia nie mają tak naprawdę zbyt wiele
    wspólnego z [False] - gdyby zastąpić je dowolnym zdaniem [C], efekt
    byłby bardzo podobny. Tadam! I tak właśnie na scenę wkracza modalność
    pośrednia - zastępując [False] przez jakieś wybrane [C].

    Zdanie [(P -> C) -> C] możemy odczytywać jako "C zachodzi, o ile
    wynika z P". Podobnie jak dla [~ ~ P], najprościej udowodnić to
    zdanie, gdy mamy dowód [P]. Trudniej jest, gdy go nie mamy - wtedy
    musimy kombinować. Jak dokładnie przebiega kombinowanie zależy od
    zdań [C] i [P].

    Zauważmy, że skoro każde [C] to inne kombinowanie, to każde [C]
    oznacza inny sposób, czyli inną modalność. Sytuacja jest podobna
    do tej z modalnością wymówkową czy modalnością aksjomatyczną -
    dla każdego zdania [C] mamy do czynienia z osobną modalnością.

    Na koniec pozostaje nam jeszcze zapytać: po cholerę nam w ogóle
    taka modalność?

    Specjalny przypadek modalności pośredniej, jakim jest modalność
    niezaprzeczalna, pozwala nam na jeszcze delikatniejsze i bardziej
    precyzyjne posługiwanie się logiką klasyczną: powiedzieć, że
    aksjomat wyłączonego środka klasycznie zachodzi, to nie powiedzieć
    nic, ale powiedzieć, że jest on niezaprzeczalny, to już nad wyraz
    głęboka mądrość.

    Niestety w ogólności (czyli dla [C] innych niż [False]) modalność
    pośrednia sama w sobie jest w praktyce raczej bezużyteczna. Czas
    poświęciliśmy jej zaś głównie z dwóch powodów:
    - w bliższej perspektywie przyczyni się do lepszego zrozumienia
      podstawowych spójników logicznych
    - w dalszej perspektywie przyzwyczai nas do różnych dziwnych rzeczy,
      takich jak kontynuacje, kodowanie Scotta czy lemat Yonedy (nie
      bój się tych nazw, one nie gryzą!) *)

(** **** Ćwiczenie *)

(** Udowodnij, że modalność pośrednia jest modalnością. *)

Lemma indirectly_law1 :
  forall C P Q : Prop,
    (P -> Q) -> (((P -> C) -> C) -> ((Q -> C) -> C)).
(* begin hide *)
Proof.
  intros C P Q pq pcc qc.
  apply pcc. intro p.
  apply qc, pq. assumption.
Qed.
(* end hide *)

Lemma indirectly_law2 :
  forall C P : Prop, P -> ((P -> C) -> C).
(* begin hide *)
Proof.
  intros C P p pc.
  apply pc.
  assumption.
Qed.
(* end hide *)

Lemma indirectly_law3 :
  forall C P : Prop,
    ((((P -> C) -> C) -> C) -> C) -> ((P -> C) -> C).
(* begin hide *)
Proof.
  intros C P p4c pc.
  apply p4c. intro pcc.
  apply pcc.
  assumption.
Qed.
(* end hide *)

(** * Modalność wszechpośrednia *)

(** Poznaliśmy dotychczas całkiem sporo modalności, w tym wszystkie
    przydatne w praktyce oraz kilka bezużytecznych, a także prawie
    wszystkie ważne. Zostało nam jeszcze trochę bezużytecznych, ale
    szkoda o nich gadać, więc zostały relegowane do ćwiczeń na końcu
    niniejszego podrozdziału.

    Podrozdziału, którego tematem jest modalność zupełnie bezużyteczna,
    ale bardzo ważna dla głębszego zrozumienia wielu rzeczy: modalności
    pośredniej, natury spójników logicznych, a nawet wiary w Boga tak
    jak ją rozumie pewien amerykański filozof polityczny, który, zupełnym
    przypadkiem, jest też programistą funkcyjnym.

    Zanim jednak ją zobaczymy, wróćmy do modalności pośredniej, której
    definicja wyglądała tak: [(P -> C) -> C], co odczytać możemy jako
    "C zachodzi, o ile wynika z P" lub "pośrednio P" (jeśli [C] umiemy
    wywnioskować z kontekstu). W całej modalności chodzi zaś o to, żeby
    powiedzieć [P], ale w zawoalowany sposób, wykorzystując do tego [C],
    które wydaje nam się jakąś ważną konsekwencją [P].

    Czas odpalić tryb dociekliwego matematyka i zacząć się zastanawiać.
    Na pierwszy ogień: jaki jest związek między [(P -> C) -> C] oraz
    [(P -> D) -> D] w zależności od związku między [C] i [D]? Pisząc
    po ludzku: czy jeśli powiemy [P] na dwa różne, zawoalowane sposoby,
    to mówimy to samo, czy coś innego? *)

(** **** Ćwiczenie *)

(** Na rozgrzewkę coś prostego: jeżeli [C] i [D] są równoważne, to
    wyrażają tę samą modalność pośrednią. *)

Lemma indirectly_iff :
  forall C D P : Prop,
    (C <-> D) -> ((P -> C) -> C) <-> ((P -> D) -> D).
(* begin hide *)
Proof.
  intros C D P cd. split.
    intros pcc pd. apply cd, pcc. intro p. apply cd, pd. assumption.
    intros pdd pc. apply cd, pdd. intro p. apply cd, pc. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Na drugi ogień zaś coś nieco trudniejszego: czy odwrotność
    powyższego zdania zachodzi?

    Wskazówka: jeżeli po dłuższym namyśle nie umiesz czegoś udowodnić,
    to szanse na to, że się nie da, są wprost proporcjonalne do twoich
    umiejętności w dowodzeniu. *)

Lemma is_this_true :
  forall C D P : Prop,
    (((P -> C) -> C) <-> ((P -> D) -> D)) -> (C <-> D).
(* begin hide *)
Proof.
Abort.
(* end hide *)

(** Wniosek płynący z powyższych ćwiczeń jest prosty (zrobiłeś je,
    prawda? Jeśli nie - do ćwiczeń MARSZ!): równoważne konsekwencje
    dają równoważne modalności pośrednie, ale nawet jeżeli [P]
    zapośredniczone przez [C] i [P] zapośredniczone przez [D] są
    równoważne, to nie ma żadnego oczywistego sposobu na udowodnienie,
    że [C] i [D] są równoważne.

    Nie jest to nic dziwnego: prawie każde znane człowiekowi zjawisko
    ma wiele różnych współwystępujących ze sobą konsekwencji, ale nie
    znaczy to wcale, że konsekwencje te są równoważne nawet bez zajścia
    tego zjawiska. Przykład: jeżeli pada deszcz to jest mokro i są
    chmury, ale nawet jeżeli [((deszcz -> mokro) -> mokro) <->
    ((deszcz -> chmury) -> chmury)], to przecież wcale nie oznacza, że
    [chmury <-> mokro].

    Powyższy przykład może (a nawet powinien, jeśliś dociekliwy)
    podsunąć ci pewną myśl: a co by było, gdybyśmy zamiast o danym
    zjawisku [P], mówili o wszystkich jego konsekwencjach? Zdanie
    takie możemy zapisać jako [forall C : Prop, (P -> C) -> C]. Na
    pierwszy rzut oka widać, że jest to jakiś sposób na powiedzenie
    [P], całkiem podobny do modalności pośredniej. Czy tutaj też mamy
    do czynienia z modalnością? Odpowiem bez owijania w bawełnę: tak,
    a modalność tę będziemy nazywać modalnością wszechpośrednią. *)

(** **** Ćwiczenie *)

(** Udowodnij, że modalność wszechpośrednia jest modalnością. *)

Lemma omnidirectly_law1 :
  forall P Q : Prop,
    (P -> Q) ->
      ((forall C : Prop, (P -> C) -> C) ->
       (forall C : Prop, (Q -> C) -> C)).
(* begin hide *)
Proof.
  intros P Q PQ mp C QC.
  apply QC, mp.
  assumption.
Qed.
(* end hide *)

Lemma omnidirectly_law2 :
  forall P : Prop,
    P -> (forall C : Prop, (P -> C) -> C).
(* begin hide *)
Proof.
  intros P p C PC.
  apply PC.
  assumption.
Qed.
(* end hide *)

Lemma omnidirectly_law3 :
  forall P : Prop,
    (forall C : Prop,
      ((forall C' : Prop, (P -> C') -> C') -> C) -> C) ->
        (forall C : Prop, (P -> C) -> C).
(* begin hide *)
Proof.
  intros P H C PC.
  apply H.
  intro H'.
  apply H'.
  assumption.
Qed.
(* end hide *)

(** No dobra, dowody dowodami, ćwiczenia ćwiczeniami, ale o co tak
    naprawdę chodzi z tą modalnością wszechpośrednią? Jaki sposób
    wyraża? Skąd nazwa?

    Zacznijmy od nazwy: skoro [P] zapośredniczone przez jedną
    konsekwencję [C] (czyli [(P -> C) -> C]) czytaliśmy za pomocą
    przysłówka "pośrednio", to zapośredniczenie przez wszystkie
    konsekwencje możemy odczytać dodając przedrostek "wszech-".
    Do kupy daje nam to więc modalność "wszechpośrednią".

    (Raczy waszmość przyznać, iż polszczyzna jest językiem tak pięknym
    jak i giętkim, czyż nie?)

    Wracając do definicji: "wszechpośrednio P" to formalnie
    [forall C : Prop, (P -> C) -> C]. Jak rozumieć tę definicję?
    Zacznijmy od tego, że [C] jest dowolnym zdaniem. Dalsza część
    mówi, że jeżeli [P] implikuje [C], to [C]. Oczywiście [P -> C]
    możemy odczytać także jako "C jest konsekwencją P", a zatem całą
    definicję możemy odczytać: zachodzi każda konsekwencja [P].

    Zachodzi każda konsekwencja [P]... ciekawe, co? Zastanówmy się, w
    jakich sytuacjach mogą zachodzić wszystkie konsekwencje [P]:
    - [P] zachodzi - najprostszy przypadek. Skoro [P] zachodzi, to
      jego konsekwencje też. Wszystkie. Bez wyjątku.
    - zachodzi coś mocniejszego od [P], tzn. zachodzi [Q] i [Q -> P].
      Zachodzą wszystkie konsekwencje [P] i być może różne rzeczy,
      które konsekwencjami [P] nie są (bo są np. konsekwencjami [Q])

    Widzimy więc, że by zaszły wszystkie konsekwencje [P], to zachodzić
    musi [P] (samo w sobie lub na mocy czegoś mocniejszego). Powinno to
    być dla ciebie oczywiste, bo to właśnie głosi prawo
    [omnidirectly_law2].

    A jak z implikacją w drugą stronę? Jeżeli zachodzą wszystkie
    konsekwencje [P], to co tak naprawdę wiemy na temat [P]? Okazuje
    się, że całkiem sporo, ale z innych powodów, niż mogłoby się na
    pierwszy rzut oka wydawać. *)

(** **** Ćwiczenie *)

(** Pokaż, że jeżeli zachodzą wszystkie konsekwencje [P], to [P] też
    zachodzi.

    Wskazówka: każde zdanie wynika samo z siebie. *)

Lemma omnidirectly_law2_conv :
  forall P : Prop,
    (forall C : Prop, (P -> C) -> C) -> P.
(* begin hide *)
Proof.
  intros P H.
  apply H.
  trivial.
Qed.
(* end hide *)

(** Jakiż wniosek płynie z ćwiczenia? Ano, ponieważ udało nam się
    pokazać zarówno [P -> (forall C : Prop, (P -> C) -> C)] (prawo
    [omnidirectly_law2], wymagane przez definicję modalności) jak i
    [(forall C : Prop, (P -> C) -> C) -> P] (powyższe ćwiczenie),
    wniosek może być tylko jeden: modalność wszechpośrednia jest
    dokładnie tym samym, co modalność neutralna. Ha! Nie tego się
    spodziewałeś, co? *)

(** ** Strukturalizm matematyczny *)

(** Powoli zbliżamy się do końca tego podrozdziału, więc czas
    na morał. Po co nam była modalność wszechpośrednia? Mimo,
    że technicznie rzecz biorąc jest ona bezużyteczna w praktyce
    (wszakże jest tym samym, co modalność neutralna), to daje nam
    ona coś dużo ważniejszego: nową ideę, pozwalającą nam inaczej
    (co czasem oznacza "lepiej") patrzeć na świat.

    Ideą tą jest... hmmm, ma ona wiele nazw w różnych kontekstach.
    W naszym moglibyśmy nazwać ją "konsekwencjalizm", gdyż w tym
    przypadku mówi ona po prostu, że każde zdanie jest dokładnie
    tym samym, co wszystkie jego konsekwencje. Ta nazwa jest jednak
    rzadko spotykana, gdyż jest zarezerwowana dla różnych teorii
    etycznych.

    Inną nazwą na to samo jest ekstensjonalność, od łacińskiego
    słowa "extendere", które znaczy "rozciągać (się)". Ekstensja
    danej fizycznej rzeczy to miejsce, która zajmuje ona w przestrzeni,
    w kontraście do intensji, czyli po prostu jakiejś nazwy lub sposobu
    na nazwanie rzeczy. Użycie tych słów wobec pojęć czy ogólniej bytów
    abstrakcyjnych jest analogiczne. W naszym wypadku intensją zdania
    [P] jest sposób, w jaki zostało zdefiniowane zaś jego ekstensją są
    wszystkie zdania, które z niego wynikają. Przykład: zdania [A /\ B],
    [B /\ A] oraz [A /\ B /\ A /\ B] to różne sposoby na zdefiniowanie
    zdania [P] (różne intensje), ale mają one takie same konsekwencje,
    czyli taką samą ekstensję.

    Jeszcze inną nazwą na to samo, z którą zapoznamy się w przyszłości,
    jest strukturalizm: w przypadku każdego obiektu matematycznego nie
    jest istotne, jak dokładnie został zdefiniowany, ale jaki jest jego
    związek z innymi obiektami i ten właśnie związek obiektu z innymi
    nazywamy jego "strukturą". W naszym przypadku obiekty to zdania, a
    związki obiektu z innymi obiektami są określane przez zachodzące (i
    niezachodzące) między nimi implikacje. Parafrazując: strukturą zdania
    są jego konsekwencje.

    Na koniec spróbujmy zastosować naszą nowo zdobytą ideę do filozofii
    religii. Amerykański myśliciel Mencjusz Moldbug zauważył (pewnie nie
    jako pierwszy, ale ja dowiedziałem się tego od niego) w swoim poście
    #<a class='link'
        href='https://www.unqualified-reservations.org/2007/04/why-do-atheists-believe-in-religion/'>
    Dlaczego ateiści wierzą w religię?</a>#,
    że wiara i ogólniej poglądy religijne mają (przynajmniej z punktu
    widzenia ateisty) znaczenie jedynie pośrednie, wyrażające się w
    działaniach ludzi je wyznających w rzeczywistym świecie (świat
    bytów nadprzyrodzonych, jak bogowie, anioły, demony etc. uznał
    on za nieistotny).

    Można tego spostrzeżenia użyć na całe multum różnych sposobów. Dla
    przykładu, niektórzy zwolennicy ekumenizmu twierdzą, jakoby
    chrześcijanie i muzułmanie tak naprawdę wierzyli w tego samego Boga.
    Czy tak jest w istocie? Nie, bo ich wiara objawia się w diametralnie
    różny sposób: muzułmanie wysadzają się w powietrze w samobójczych
    zamachach, a chrześcijanie nie. Inne działania = inna wiara, a zatem
    inny Bóg.

    TODO: zastanowić się, czy te pierdoły o filozofii religii faktycznie
    są tutaj potrzebne.
    TODO 2: esencjalizm vs strukturalizm *)

(** **** Ćwiczenie *)

(** A co, gdyby tak skwantyfikować [E : Prop] i otrzymać w wyniku
    [forall E : Prop, E \/ P]? Zdanie to znaczy coś w stylu "P
    zachodzi albo i nie, wymówkę wybierz sobie sam". W sumie można
    by powstały tutaj twór nazwać modalnością wszechwymówkową...

    Udowodnij, że modalność wszechwymówkowa faktycznie jest
    modalnością. *)

Lemma anyexcuse_law1 :
  forall P Q : Prop,
    (P -> Q) ->
      ((forall E : Prop, E \/ P) -> (forall E : Prop, E \/ Q)).
(* begin hide *)
Proof.
  intros P Q pq H E.
  destruct (H False).
    contradiction.
    right. apply pq. assumption.
Qed.
(* end hide *)

Lemma anyexcuse_law2 :
  forall P : Prop,
    P -> (forall E : Prop, E \/ P).
(* begin hide *)
Proof.
  intros P p E.
  right.
  assumption.
Qed.
(* end hide *)

Lemma anyexcuse_law3 :
  forall P : Prop,
    (forall E1 : Prop, E1 \/ (forall E2 : Prop, E2 \/ P)) ->
      (forall E : Prop, E \/ P).
(* begin hide *)
Proof.
  intros P eep E.
  destruct (eep False).
    contradiction.
    destruct (H False).
      contradiction.
      right. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij, że modalność wszechwymówkowa jest równoważna modalności
    neutralnej.

    Wskazówka: można wybrać wymówkę, która nijak nie może zachodzić. *)

Lemma anyexcuse_spec :
  forall P : Prop,
    (forall E : Prop, E \/ P) <-> P.
(* begin hide *)
Proof.
  split.
    intro H. destruct (H False).
      contradiction.
      assumption.
    intros p E. right. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Zastanówmy się nad następującą konstrukcją: zdanie [P] wynika ze
    wszystkich możliwych aksjomatów.

    Czy taki twór jest modalnością? Sprawdź to! (Jeżeli jest, to
    będziemy tę modalność nazywać modalnością wszechaksjomatyczną). *)

Lemma allaxioms_law1 :
  forall P Q : Prop,
    (P -> Q) -> ((forall A : Prop, A -> P) -> (forall A : Prop, A -> Q)).
(* begin hide *)
Proof.
  intros P Q pq H A a.
  apply pq, (H _ a).
Qed.
(* end hide *)

Lemma allaxioms_law2 :
  forall P : Prop,
    P -> (forall A : Prop, A -> P).
(* begin hide *)
Proof.
  intros P p A a.
  assumption.
Qed.
(* end hide *)

Lemma allaxioms_law3 :
  forall P : Prop,
    (forall A : Prop, A -> (forall B : Prop, B -> P)) ->
      (forall A : Prop, A -> P).
(* begin hide *)
Proof.
  intros P H A a.
  apply (H A a A a).
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Skoro [P] wynika ze wszystkich aksjomatów, to wynika także z mało
    informatywnego aksjomatu [True]... czyli w sumie po prostu zachodzi,
    ot tak bez żadnych ceregieli.

    Udowodnij, że modalność wszechaksjomatyczna to tak naprawdę to samo,
    co modalność neutralna. *)

Lemma allaxioms_spec :
  forall P : Prop,
    P <-> (forall A : Prop, A -> P).
(* begin hide *)
Proof.
  split.
    intros p A a. assumption.
    intro H. apply (H True). trivial.
Qed.
(* end hide *)

(** * Dodatkowe prawa modalności *)

(* begin hide *)
(* TODO: napisać coś o [bind] i [compM] dla modalności. *)
(* end hide *)

Lemma neutrally_bind :
  forall P Q : Prop,
    P -> (P -> Q) -> Q.
(* begin hide *)
Proof.
  intros.
  apply H0.
  assumption.
Qed.
(* end hide *)

Lemma neutrally_compM :
  forall P Q R : Prop,
    (P -> Q) -> (Q -> R) -> (P -> R).
(* begin hide *)
Proof.
  intros.
  apply H0, H, H1.
Qed.
(* end hide *)

Lemma trivially_bind :
  forall P Q : Prop,
    True -> (P -> True) -> True.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma trivially_compM :
  forall P Q R : Prop,
    (P -> True) -> (Q -> True) -> (P -> True).
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma excuse_bind :
  forall E P Q : Prop,
    (E \/ P) -> (P -> E \/ Q) -> E \/ Q.
(* begin hide *)
Proof.
  intros E P Q [e | p] H.
    left. assumption.
    destruct (H p).
      left. assumption.
      right. assumption.
Qed.
(* end hide *)

Lemma excuse_compM :
  forall E P Q R : Prop,
    (P -> E \/ Q) -> (Q -> E \/ R) -> (P -> E \/ R).
(* begin hide *)
Proof.
  intros E P Q R peq qer p.
  destruct (peq p) as [e | q].
    left. assumption.
    destruct (qer q).
      left. assumption.
      right. assumption.
Qed.

Lemma classically_bind :
  forall P Q : Prop,
    (LEM -> P) -> (P -> (LEM -> Q)) -> (LEM -> Q).
(* begin hide *)
Proof.
  intros P Q p pq lem.
  apply pq.
    apply p. assumption.
    assumption.
Qed.
(* end hide *)

Lemma classically_compM :
  forall P Q R : Prop,
    (P -> (LEM -> Q)) -> (Q -> (LEM -> R)) -> (P -> (LEM -> R)).
(* begin hide *)
Proof.
  intros P Q R pq qr pr lem.
  apply qr.
    apply pq; assumption.
    assumption.
Qed.
(* end hide *)

Lemma axiomatically_bind :
  forall A P Q : Prop,
    (A -> P) -> (P -> (A -> Q)) -> (A -> Q).
(* begin hide *)
Proof.
  intros A P Q p pq a.
  apply pq.
    apply p. assumption.
    assumption.
Qed.
(* end hide *)

Lemma axiomatically_compM :
  forall A P Q R : Prop,
    (P -> (A -> Q)) -> (Q -> (A -> R)) -> (P -> (A -> R)).
(* begin hide *)
Proof.
  intros A P Q R pq qr p a.
  apply qr.
    apply pq; assumption.
    assumption.
Qed.
(* end hide *)

Lemma irrefutably_bind :
  forall P Q : Prop,
    ~ ~ P -> (P -> ~ ~ Q) -> ~ ~ Q.
(* begin hide *)
Proof.
  intros P Q p pq nq.
  apply p. intro pure_p.
  apply pq.
    assumption.
    assumption.
Qed.
(* end hide *)

Lemma irrefutably_compM :
  forall P Q R : Prop,
    (P -> ~ ~ Q) -> (Q -> ~ ~ R) -> (P -> ~ ~ R).
(* begin hide *)
Proof.
  intros P Q R pq qr p nr.
  apply pq.
    assumption.
    intro q. apply qr.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma indirectly_bind :
  forall C P Q : Prop,
    ((P -> C) -> C) -> (P -> ((Q -> C) -> C)) -> ((Q -> C) -> C).
(* begin hide *)
Proof.
  intros C P Q p pq qc.
  apply p. intro pure_p.
  apply pq.
    assumption.
    assumption.
Qed.
(* end hide *)

Lemma indirectly_compM :
  forall C P Q R : Prop,
    (P -> ((Q -> C) -> C)) -> (Q -> ((R -> C) -> C)) ->
      (P -> ((R -> C) -> C)).
(* begin hide *)
Proof.
  intros C P Q R pq qr p rc.
  apply pq.
    assumption.
    intro q. apply qr.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma omnidirectly_bind :
  forall P Q : Prop,
    (forall C : Prop, (P -> C) -> C) ->
    (P -> (forall C : Prop, (Q -> C) -> C)) ->
      (forall C : Prop, (Q -> C) -> C).
(* begin hide *)
Proof.
  intros P Q p pq C qc.
  apply p. intro pure_p.
  apply pq; assumption.
Qed.
(* end hide *)

Lemma omnidirectly_compM :
  forall P Q R : Prop,
    (P -> (forall C : Prop, (Q -> C) -> C)) ->
    (Q -> (forall C : Prop, (R -> C) -> C)) ->
      (P -> (forall C : Prop, (R -> C) -> C)).
(* begin hide *)
Proof.
  intros P Q R pq qr p C rc.
  apply pq.
    assumption.
    intro q. apply qr; assumption.
Qed.
(* end hide *)

(** * Związki między modalnościami *)

(** Przekonaliśmy się już, że dwie pozornie różne definicje mogą tak
    naprawdę definiować tę samą modalność, np. [LEM -> P] i [DNE -> P]
    to dwie definicje modalności klasycznej. Widzieliśmy też, że niektóre
    modalności są specjalnymi przypadkami innych (niezaprzeczalność
    jest specjalnym przypadkiem pośredniości, a modalność trywialna
    to modalność wymówkowa z bardzo ogólną i niesamowicie przekonującą
    wymówką).

    Czy to jednak wszystko, co potrafimy powiedzieć o modalnościach i
    ich wzajemnych związkach? Oczywiście nie. Wiemy przecież choćby, że
    [P -> ~ ~ P]. Można ten fakt zinterpretować następująco: modalność
    neutralna jest silniejsza niż modalność niezaprzeczalna, czyli
    równoważnie: modalność niezaprzeczalna jest słabsza niż modalność
    neutralna. *)

(** **** Ćwiczenie *)

(** Formalnie powiemy, że modalność [M] jest silniejsza niż modalność
    [N], gdy [forall P : Prop, M P -> N P].

    Zastanów się, jaki jest związek między modalnością niezaprzeczalną
    i modalnością klasyczną. Czy są one tym samym, czy czymś innym? Czy
    któraś z nich jest mocniejsza od drugiej? *)

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

(** **** Ćwiczenie *)

(** Najbanalniejsze i najnaturalniejsze pytanie, które powinno było
    przyjść ci do głowy po zapoznaniu się z faktem, że niektóre
    modalności mogą być "silniejsze" od innych, to: która modalność
    jest najsilniejsza (a która najsłabsza)?

    No, skoro już takie pytanie przyszło ci do głowy, to znajdź na nie
    odpowiedź!

    Uwaga: nie musisz formalnie dowodzić w Coqu, że masz rację. Prawdę
    powiedziawszy, gdybyśmy uparli się na pełną formalność, to nie
    umiemy jeszcze wyrazić odpowiednich twierdzeń.

    Wskazówka: sformułuj najpierw, co znaczą słowa "najsilniejszy"
    oraz "najsłabszy". Następnie przyjrzyj się definicji modalności
    oraz poszczególnym modalnościom i udowodnionym dotychczas przez
    nas twierdzeniom. Powinno cię to oświecić. *)

(* begin hide *)

(** [M] jest najsilniejszą modalnością, gdy pociąga za sobą wszystkie
    inne, czyli dla każdej modalności [N] i zdania [P] mamy [M P -> N P].

    Analogicznie [M] jest najsłabszą modalnością, gdy wynika ona ze
    wszystkich innych modalności [N]: dla każdego zdania [P] mamy
    [N P -> M P].

    Najsilniejsza modalność to modalność neutralna - wynika to z prawa
    numer 2. Najsłabszą modalnością jest modalność trywialna, co też
    jest raczej oczywiste. *)

(* end hide *)

(** **** Ćwiczenie *)

(** Uwaga: to ćwiczenie jest mocno opcjonalne, przeznaczone dla tych
    bardziej dociekliwych.

    Skoro wiesz już (z poprzedniego ćwiczenia), która modalność jest
    najsilniejsza, a która najsłabsza, to najoczywistszym pytaniem,
    na które powinieneś wpaść, jest: które modalności są pomiędzy?

    Zrób tabelkę, której wiersze i kolumny indeksowane są modalnościami.
    Kratka w wierszu [M] i kolumnie [N] oznacza twierdzenie "modalność
    M jest silniejsza niż modalność N".

    Wypełnij tabelkę. W każdą kratkę wstaw:
    - ptaszek, jeżeli twierdzenie zachodzi
    - krzyżyk, gdy zachodzi jego negacja
    - znak zapytania, jeżeli nie da się udowodnić żadnego z powyższych

    Następnie narysuj obrazek, który obrazuje zależności z tabelki.
    Każdą modalność zaznacza jako kropkę z odpowiednią nazwą. Połącz
    kropki [M] i [N], gdy modalność [M] jest silniejsza niż modalność
    [N] i nie ma między nimi żadnej modalności o pośredniej sile. *)

(* begin hide *)

(* Zobacz obrazek: txt/modalności.jpg *)

(* end hide *)

(** * Składanie modalności *)

(** Skoro modalności mamy w małym palcu, to czas na... ale czekaj! Czy
    aby napewno wiemy o modalnościach już wszystko? I tak i nie. Wiemy
    wszystko co powinniśmy o modalnościach, które na nasze potrzeby
    nazwiemy "modalnościami prostymi" - nie będę tego pojęcia definiował.

    Czy znaczy to zatem, że są też jakieś inne modalności, zwane pewnie
    "złożonymi", o których jeszcze nic nie wiemy? Tutaj również odpowiedź
    brzmi "tak".

    O cóż więc chodzi z tymi złożonymi modalnościami? Otóż czasami
    (ale nie zawsze) możemy wziąć dwie modalności i złożyć je w
    jedną, uzyskując takie cudaczne twory jak na przykład modalność
    pośrednia z wymówką albo modalność wymówkowa z aksjomatem.

    Coby nie przynudzać, zobaczmy jak wygląda to w praktyce. *)

(** **** Ćwiczenie *)

(** Pokaż, że złożenie modalności klasycznej oraz modalności
    niezaprzeczalnej daje modalność. *)

Lemma irrclassly_law1 :
  forall P Q : Prop,
    (P -> Q) -> ((LEM -> ~ ~ P) -> (LEM -> ~ ~ Q)).
(* begin hide *)
Proof.
  intros P Q pq p' lem nq.
  apply p'.
    assumption.
    intro p. apply nq, pq, p.
Qed.
(* end hide *)

Lemma irrclassly_law2 :
  forall P : Prop,
    P -> (LEM -> ~ ~ P).
(* begin hide *)
Proof.
  intros P p lem np. contradiction.
Qed.
(* end hide *)

Lemma irrclassly_law3 :
  forall P : Prop,
    (LEM -> ~ ~ (LEM -> ~ ~ P)) -> (LEM -> ~ ~ P).
(* begin hide *)
Proof.
  intros P H lem np.
  specialize (H lem).
  apply H. intro H'.
  apply H'; assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Pokaż, że złożenie modalności niezaprzeczalnej oraz modalności
    klasycznej daje modalność. *)

Lemma classirrly_law1 :
  forall P Q : Prop,
    (P -> Q) -> (~ ~ (LEM -> P) -> ~ ~ (LEM -> Q)).
(* begin hide *)
Proof.
  intros P Q pq nnp nq.
  apply nnp. intro p.
  apply nq. intro lem.
  apply pq, p, lem.
Qed.
(* end hide *)

Lemma classirrly_law2 :
  forall P : Prop,
    P -> ~ ~ (LEM -> P).
(* begin hide *)
Proof.
  intros P p nnp.
  apply nnp. intros _.
  assumption.
Qed.
(* end hide *)

Lemma classirrly_law3 :
  forall P : Prop,
    ~ ~ (LEM -> ~ ~ (LEM -> P)) -> ~ ~ (LEM -> P).
(* begin hide *)
Proof.
  intros P H H'.
  apply H. intro H''.
  apply H'. intro lem.
  specialize (H'' lem).
  contradiction.
Qed.
(* end hide *)

(** Twór z pierwszego ćwiczenia możemy nazwać modalnością klasycznie
    niezaprzeczalną, bo [LEM -> ~ ~ P] znaczy, że w logice klasycznej
    zdanie [P] jest niezaprzeczalne. Jak więc widać, złożenie modalności
    klasycznej i niezaprzeczalnej daje w efekcie modalność.

    Twór z drugiego ćwiczenia możemy nazwać modalnością niezaprzeczalnie
    klasyczną, bo [~ ~ (LEM -> P)] znaczy, że jest niezaprzeczalnie, że
    [P] zachodzi w logice klasycznej. Jak więc widać, złożenie modalności
    niezaprzeczalnej i klasycznej daje w efekcie modalność.

    Twoje podejrzenia może (a nawet powinno) wzbudzić drugie z ćwiczeń.
    Czyż nie każe ci ono zrobić drugi raz tego samego, co poprzednie
    ćwiczenie? Otóż nie, a przynajmniej niekoniecznie: a priori wynik
    składania modalności zależy od kolejności, czyli złożenie modalności
    [M] i [N] nie musi być tym samym, co złożenie modalności [N] i [M]. *)

(** **** Ćwiczenie *)

(** Skoro tak, to powinno ci teraz przyjść do głowy pytanie: a jak jest
    w przypadku modalności niezaprzeczalnej i klasycznej? Czy złożenia
    w obu kolejnościach dają to samo, czy coś innego?

    Żeby trochę ułatwić ci życie, odpowiem za ciebie: oba złożenia dają
    tę samą modalność. *)

Lemma irrclassly_classirrly :
  forall P : Prop,
    (LEM -> ~ ~ P) <-> (~ ~ (LEM -> P)).
(* begin hide *)
Proof.
  split.
    intros H1 H2. apply H2. intro lem. destruct (lem P).
      assumption.
      contradiction H1.
    intros nnp lem np. apply nnp. intro. contradiction np.
      apply H, lem.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Skoro oba złożenia dają tę samą modalność, to natychmiast powinno
    przyjść ci do głowy kolejne oczywiste pytanie: co to za modalność?
    Czy jest ona dla nas nowością, czy kiedyś już się z nią zetknęliśmy?

    Odpowiedzią na to pytanie jest niniejsza ćwiczenie: pokaż, że
    modalności niezaprzeczalnie klasyczna i klasycznie niezaprzeczalna
    to tak naprawdę dwa wcielenia modalności klasycznej. *)

Lemma classirrly_classically :
  forall P : Prop,
    (~ ~ (LEM -> P)) <-> (LEM -> P).
(* begin hide *)
Proof.
  split.
    intros nnp lem. destruct (lem (LEM -> P)).
      apply H, lem.
      contradiction.
    intros p np. apply np. intro lem. apply p. assumption.
Qed.
(* end hide *)

Lemma irrclassly_classically :
  forall P : Prop,
    (LEM -> ~ ~ P) <-> (LEM -> P).
(* begin hide *)
Proof.
  split.
    intros nnp lem. destruct (lem P).
      assumption.
      contradiction nnp.
    intros p lem np. contradiction np. apply p, lem.
Qed.
(* end hide *)

(** Czas zakończyć niniejszy podrozdział, albowiem składanie modalności
    nie będzie dla nas zbyt istotną operacją. Dlaczego tak? Odpowiedź w
    zasadzie już poznaliśmy.

    Z naszego punktu widzenia jedynymi modalnościami przydatnymi
    w praktyce są modalność niezaprzeczalna i modalność klasyczna.
    Z poprzedniego podrozdziału wiemy, że modalność niezaprzeczalna
    jest silniejsza niż modalność klasyczna, co w efekcie prowadzi
    do tego, że oba ich złożenia dają modalność klasyczną.

    Słowem: złożenia jedynych ważnych dla nas modalności dają w wyniku
    modalność już nam znaną. Złożenia modalności mniej istotnych, jak
    modalność pośrednia czy modalność wymówkowa, również nie będą nas
    zbytno interesować. *)

(** * Podsumowanie *)

(** W niniejszym (długaśnym, trzeba przyznać) podrozdziale zapoznaliśmy
    się z modalnościami.

    Intuicyjnie zdanie modalne to takie, które jest wyrażone w jakiś
    niebanalny sposób, np. z użyciem podwójnej negacji, wymówki czy
    aksjomatu. Modalność to właśnie ten "sposób" wyrażania. Każda
    modalność spełnia parę warunków:
    - jest kompatybilna z konsekwencjami danego zdania
    - nie przeinacza znaczenia zdania, a jedynie je modyfikuje
    - nie można "spamować" daną modalnością w celu uzyskania cudacznych
      zdań

    Najbardziej istotne dla nas modalności to modalność niezaprzeczalna,
    która pozwala na bardzo subtelne poruszanie się na obrzeżach logiki
    klasycznej, oraz modalność klasyczna, pozwalająca elegancko zanurzyć
    logikę klasyczną w logice konstruktywnej. Poznaliśmy też modalność
    wszechpośrednią, która wyposażyła nas w ciekawą filozoficznie ideę:
    zdania logiczne są zdeterminowane przez to, co z nich wynika.

    Dowiedzieliśmy się też, że niektóre modalności wyrażają zdania w dużo
    bardziej dobitny (czyli silniejszy) sposób niż inne. Najsilniejszą
    modalnością jest ta domyślna, czyli neutralna. Najsłabsza zaś jest
    modalność trywialna, która nie wyraża w sumie niczego.

    Modalności można też ze sobą składać, żeby otrzymywać (potencjalnie)
    nowe, wyrażające jeszcze bardziej zagmatwane czy subtelne sposoby.
    Niestety okazało się też, że złożenia najistotniejszych z naszego
    punktu widzenia modalności nie wnoszą niczego ciekawego.

    Jeśliś pogubił się w tym modalnościowym zoo, nie lękaj się! Zrobiłem
    #<a class='link'
        href='https://github.com/wkolowski/Typonomikon/blob/master/txt/ściągi/modalności.md'>
    ściągę</a>#. *)

