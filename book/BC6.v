(** * BC6: Inne logiki [TODO] *)

From Typonomikon Require Export BC5a.

(** * Inne aksjomaty? (TODO) *)

Definition PropExt : Prop :=
  forall P Q : Prop, (P <-> Q) -> P = Q.

Definition ProofIrrelevance : Prop :=
  forall (P : Prop) (p1 p2 : P), p1 = p2.

Definition UIP : Prop :=
  forall (A : Type) (x y : A) (p q : x = y), p = q.

Definition K : Prop :=
  forall (A : Type) (x : A) (p : x = x), p = eq_refl x.

(** * Inne systemy dowodzenia? (TODO) *)

(** ** Systemy w stylu Hilberta *)

(** ** Rachunek sekwentów *)

(** * Inne logiki? *)

(** Słowo "logika" zazwyczaj występuje w liczbie pojedynczej i nie bez
    przyczyny - zazwyczaj naucza się jednej (a nawet jedynej słusznej)
    logiki. Porównawszy logiki konstruktywną i klasyczną nie pozostaje
    nam nic innego jak tylko skonstatować, że jesteśmy bardzo wyjątkowymi
    płatkami śniegu, bo znamy już dwie logiki. Do głowy powinno nam zatem
    przyjść jedyne słuszne w tej sytuacji pytanie: czy są jeszcze jakieś
    inne logiki? Odpowiedź brzmi: tak, i to nawet nieskończenie wiele.

    W niniejszym podrozdziale zapoznamy się z krótką klasyfikacją innych
    logik wraz z ich opisami i oceną ideologicznej słuszności (tak żebyś
    wiedział, za czym nie warto gonić - za dużo swojego cennego czasu
    zmarnowałem na rozmyślanie o bezużytecznych logikach i chciałbym,
    aby przyszłe pokolenia nie musiały tyle cierpieć), zaś w dalszej
    części niniejszego rozdziału poznamy te z owych innych logik, które
    znać warto. *)

(** ** Logiki (sub- i super-)intuicjonistyczne oraz logiki pośrednie *)

(** Na wstępie przypomnijmy, że "logika intuicjonistyczna" to inna
    nazwa na logikę konstruktywną, ale ja unikam tej nazwy, bo jest
    mało obrazowa (nie mówiąc już o tym, że jest upiornie przydługa).

    Są dwa podstawowe sposoby, żeby uzyskać logikę inną od logiki
    konstruktywnej:
    - weź logikę konstruktywną i coś z niej zabierz
    - weź logikę konstruktywną i coś do niej dodaj

    Logiki z pierwszego przypadku to logiki subintuicjonistyczne (po
    łacinie "sub" znaczy "poniżej"), bo można w nich udowodnić mniej
    twierdzeń, niż w logice intuicjonistycznej. To co zabieramy to
    zazwyczaj spójniki logiczne lub jakieś aspekty ich działania. I
    tak możemy mieć logikę z samą implikacją albo logikę, w której
    są wszystkie spójniki, ale nie zachodzi _ex falso quodlibet_
    (czyli nie jest prawdą, że z fałszu wynika wszystko).

    Logiki subintuicjonistyczne są głupie (bo po co się ograniczać?),
    więc nie będziemy się nimi zajmować. Zresztą już je trochę znasz.
    Spróbuj przypomnieć sobie jakieś twierdzenie, które udowodniłeś,
    a w którym nie było np. koniunkcji - jest to twierdzenie w
    subintuicjonistycznej logice bez koniunkcji. Jeżeli w jakimś
    dowodzie nie użyłeś _ex falso_ (ani wprost, ani pośrednio, np.
    przez użycie lematu, którego dowód używał _ex falso_) to znaczy,
    że to twierdzenie zachodzi w subintuicjonistycznej logice bez
    _ex falso_... widzisz do czego to zmierza, prawda?

    Logiki z drugiego przypadku to logiki superintuicjonistyczne (po
    łacinie "super" znaczy "powyżej"), bo można w nich udowodnić
    więcej twierdzeń, niż w logice intuicjonistycznej. To co dodajemy
    to zazwyczaj aksjomaty. Wesołym przykładem superintuicjonistycznej
    logiki jest logika sprzeczna - jest to logika, w której aksjomatem
    jest fałsz. Można w niej udowodnić wszystko, a więc istotnie więcej,
    niż w zwykłej logice konstruktywnej.

    Znanym ci już przykładem superintuicjonistycznej logiki jest logika
    klasyczna, która powstaje z dodania do logiki konstruktywnej jako
    aksjomatu prawa wyłączonego środka (albo jakiegoś jego zamiennika).
    Logika klasyczna jest
    maksymalną logiką superintuicjonistyczną, bo można w niej udowodnić
    najwięcej twierdzeń ze wszystkich logik superintuicjonistycznych
    (oczywiście pomijając logikę sprzeczną). Oznacza to, że dodanie do
    logiki klasycznej jako aksjomatu jakiegoś zdania, którego nie można
    w niej udowodnić, daje w efekcie logikę sprzeczną.

    Ponieważ logika intuicjonistyczna jest naszym punktem wyjściowym
    (jest "najsłabsza"), a logika klasyczna docelowym (maksimum pod
    względem liczby twierdzeń, które można udowodnić), wszystkie
    logiki będące pomiędzy tymi dwoma nazywa się często logikami
    pośrednimi.

    Ciekawym przykładem logiki pośredniej, który poznamy, jest logika
    de Morgana (a przynajmniej ja ją tak nazwałem - nie wiem, jak zwie
    się ona w poważnej literaturze). Powstaje ona poprzez dorzucenie
    do logiki konstruktywnej dodatkowego aksjomatu, którym jest prawo
    de Morgana.

    Oczywiście świat jest nieco skomplikowańszy niż go przedstawiłem.
    Jakiś zwichrowany umysł mógłby bez problemu wymyślić sobie logikę
    subsuperintuicjonistyczną. Wystarczy z logiki konstruktywnej zabrać
    np. koniunkcję, a dodać np. prawo wyłączonego środka. Nie muszę
    chyba nadmieniać, że tego typu zabawy przypominają budowę potwora
    Frankensteina, co? *)

(** ** Logiki modalne *)

(** Logiki modalne to logiki, w których oprócz znanych nam już spójników
    czy kwantyfikatorów występują też modalności. Czym jest modalność?
    Najpierw trochę etymologii.

    Łacińskie słowo "modus" oznacza "sposób". Występuje ono w takich
    wyrażeniach jak "modus operandi" ("sposób działania") czy "modus
    vivendi" ("sposób życia"; po dzisiejszemu powiedzielibyśmy "styl
    życia", a amerykańce - "way of life" albo "lifestyle"). Od niego
    w średniowiecznej
    łacinie powstał przymiotnik "modalis", który oznacza "dotyczący
    sposobu". Przymiotnik ten przedostał się do języków narodowych,
    dając polskie "modalny" czy angielskie "modal", od których potem
    utworzono rzeczowniki (pol. "modalność", ang. "modality") znaczące
    mniej więcej to samo, co oryginalne łacińskie "modus" - "sposób".
    Historia słów bywa pokręcona...

    W językach naturalnych modalności często występują pod postacią
    czasowników zwanych na ich cześć modalnymi, takich jak "móc" czy
    "musieć" - o ile nie mieszkasz pod kamieniem na pustyni, to pewnie
    spotkałeś się z nimi ucząc się języków obcych. Jednak nas bardziej
    będzie interesować inna forma, pod którą modalności występują, a są
    nią przysłówki. Porównajmy poniższe zdania:
    - Pada deszcz.
    - Być może pada deszcz.
    - Na pewno pada deszcz.

    Wszystkie mówią o tym samym zjawisku, czyli deszczu, ale robią to
    w różny sposób (i ten sposób to właśnie modalność!) - pierwszy
    sposób jest neutralny, drugi wyraża niepewność (czyli możliwość),
    a trzeci pewność (czyli konieczność).

    Najpopularniejsze logiki modalne skupiają się na próbie formalizacji
    właśnie tych dwóch sposobów - możliwości i konieczności. Rozważa się
    różne reguły i/lub aksjomaty, np. "jeśli P zachodzi, to jest możliwe"
    czy "jeżeli P jest konieczne, to zachodzi" oraz próbuje sformalizować
    znaczenie zdań modalnych za pomocą tworu zwanego "możliwymi światami"
    (ang. possible worlds). Idea jest taka, że światów jest bardzo wiele
    i zwykłe zdania mówią o naszym świecie, a zdania modalne o światach
    innych niż nasz. Coś jest możliwe, gdy zachodzi w jednym ze światów,
    zaś konieczne, jeżeli zachodzi we wszystkich światach.

    Modalności z powyższej logiki (możliwość i konieczność) nazywane
    bywają aletycznymi (od greckiego "ἀλήθεια" / "aletheia" - "prawda"),
    gdyż modyfikują prawdziwość zdań. Inne warianty logiki modalnej to:
    - logika deontyczna (od gr. "δέον" / "déon" - "to co jest wiążące"),
      w której występują takie modalności jak "trzeba", "należy", "wolno",
      "nie wolno", "powinno się", "wypadałoby" etc.
    - logika epistemiczna (od gr. "ἐπιστήμη" / "epistēmē" - "wiedza"),
      w której modalności reprezentują stan wiedzy różnych osób
    - logika doksastyczna (od gr. "δόξα" / "dόxa" - "wiara", "opinia"),
      w której modalności reprezentują, w jakie zdania wierzą osoby

    Jak nietrudno domyślić się po dużej liczbie greckich słów, które
    się nagle pojawiły, wszystkie powyższe logiki modalne mają raczej
    charakter filozoficzny, co sprawia, że z punktu widzenia zarówno
    matematyki jak i informatyki są zupełnie bezużyteczne. Szczególnie
    bolesne jest to, że każdy z powyższych wariantów logiki modalnej
    sam ma ogrom wariantów, gdyż filozofowie za cholerę nie mogą się
    zgodzić co do tego, czym tak naprawdę jest możliwość, konieczność,
    wiedza, wiara, etc. To powoduje, że wszystkie te logiki są mocno
    niejasne. Z tego powodu nie będziemy się nimi zajmować.

    Na szczęście nie wszystkie logiki modalne są mętne. Dość ciekawą
    logiką modalną jest logika dowodliwości (ang. provability logic),
    w której występuje operator modalny oznaczający "da się udowodnić,
    że...".

    Wróćmy po raz kolejny do prawa wyłączonego środka. W Coqu nie
    umiemy udowodnić, że [forall P : Prop, P \/ ~ P], ale czy to
    znaczy, że zdanie to jest fałszywe? Gdyby spróbować udowodnić
    [~ forall P : Prop, P \/ ~ P], to okaże się, że... też raczej
    nie potrafimy, ale czy to znaczy, że prawo wyłączonego środka
    jest prawdziwe?

    Widzimy więc, że prawo wyłączonego środka jest niejako zawieszone
    w próżni: nie umiemy go udowodnić ani obalić. Jak fakt ten wpływa
    na jego prawdziwość? Możemy przyjąć prawo wyłączonego środka jako
    aksjomat, ale możemy też jako aksjomat przyjąć jego zaprzeczenie.
    Oba te aksjomaty po dodaniu do Coqowej logiki nie doprowadzą nas
    do sprzeczności... ale czy na pewno? Skąd niby wiesz, że cię nie
    okłamałem? Czy to, że po dodaniu aksjomatu nie natrafiliśmy na
    żadną sprzeczność znaczy, że nie da się na nią natrafić?

    Jak widzisz, pytania te są dość mocno pogmatwane, a co gorsza,
    nie możemy użyć Coqa, żeby upewnić się, że nasze odpowiedzi na
    nie są poprawne. Cobyś nie czuł nadmiarowego niepokoju, zapewnię
    cię tylko, że aksjomat wyłączonego środka faktycznie może zostać
    dodany do Coqa bez popadania w sprzeczność. Jednak żeby być tego
    faktu pewnym, paru kolesi, znacznie mądrzejszych od nas, musiało
    zakasać rękawy, kupić 100 kilo kredy i parę ryz papieru, i ostro
    się napracować, nie mając tej błogiej pewności, że poprawny dowód
    zaświeci się na zielono.

    Logika dowodliwości to logika, która teoretycznie próbuje zaradzić
    tego typu sytuacjom i dlatego jest intrygująca... ale ponieważ nas
    bardziej interesuje praktyczne dowodzenie poprawności programów (w
    przyszłych rozdziałach, kiedy już nauczymy się programować), a nie
    zamartwianie się aksjomatami, to logika dowodliwości jest dla nas
    zupełnie bezużyteczna i z tego powodu nie będziemy się nią zajmować.

    Ostatnią rodziną logik modalnych wartych wspomnienia są logiki
    temporalne (z łac. "tempus" - "czas"). Występują tam modalności
    wyrażające czas, np. "teraz", "zawsze w przeszłości", "zawsze w
    przyszłości", "kiedyś w przeszłości", "kiedyś w przyszłości" i
    tak dalej.

    Napisałem "logiki temporalne" w liczbie mnogiej, bo jest ich wiele,
    a główne różnice dotyczą struktury czasu, która jest wyrażana przez
    prawa rządzące modalnościami, jak np. te dwa:
    - "jeżeli P zachodzi, to w przyszłości zawsze będzie prawdą, że P
      zaszło kiedyś w przeszłości" - brzmi całkiem rozsądnie
    - "jeżeli P zachodzi, to w przeszłości zawsze było prawdą, że P
      zajdzie kiedyś w przyszłości" - brzmi mega deterministycznie i
      niektórzy mogą się przeciw niemu zbuntować.

    Tego typu filozoficzne dywagacje prowadzą nas do pytania o naturę
    czasu: czy czas jest liniowy (istnieje jedna możliwa przyszłość,
    czyli świat jest zdeterminowany), czy raczej rozgałęziony (jest
    wiele możliwych przyszłości, czyli świat nie jest zdeterminowany),
    co w praktyce oznacza kolejne wcielenie idei możliwych światów.

    Mimo filozoficznego smrodku, który dobywa się z powyższego opisu,
    niektóre logiki temporalne są całkiem użyteczne i to do czegoś,
    na czym i nam zależy: weryfikacji poprawności programów (a także
    sprzętu, ale o tym ja sam nic nie wiem). Idea jest taka, że możemy robić
    zdania wyrażające różne pożądane właściwości programów, na przykład:
    - bezpieczeństwo (and. safety) - program NIGDY nie zrobi niczego złego
    - żywotność (ang. liveness) - na każde żądanie serwer KIEDYŚ udzieli odpowiedzi

    Mimo tego powiewu przydatności, nie będzie zajmować się logikami
    temporalnymi, ponieważ ich podejście do weryfikacji poprawności
    programów jest diametralnie różne i niekompatybilne z naszym.

    Na koniec krótka przestroga. Przeczytawszy niniejszy podrozdział
    mógłbyś dojść do wniosku, że logiki modalne są bezużyteczne, ale
    wcale tak nie jest. Modalności to nie tylko możliwość, czas albo
    wiedza, których w Coqowej logice brak. Modalności stanowią także
    bardzo ogólny i elegancki sposób patrzenia na rzeczy dobrze nam
    znane, jak logika klasyczna czy podwójna negacja. *)

(** ** Paradoks pieniądza i kebaba (TODO) *)

(** Przestrzegłem cię już przed nieopatrznym interpretowaniem zdań języka
    naturalnego za pomocą zdań logiki formalnej. Gdybyś jednak wciąż
    był skłonny to robić, przyjrzyjmy się kolejnemu "paradoksowi". *)

Lemma copy :
  forall P : Prop, P -> P /\ P.
(* begin hide *)
Proof.
  split; assumption.
Qed.
(* end hide *)

(** Powyższe niewinnie wyglądające twierdzenie mówi nam, że [P] implikuje
    [P] i [P]. Spróbujmy przerobić je na paradoks, wymyślając jakąś wesołą
    interpretację dla [P].

    Niech zdanie [P] znaczy "mam złotówkę". Wtedy powyższe twierdzenie mówi,
    że jeżeli mam złotówkę, to mam dwa złote. Widać, że jeżeli jedną z tych
    dwóch złotówek znów wrzucimy do twierdzenia, to będziemy mieli już trzy
    złote. Tak więc jeżeli mam złotówkę, to mam dowolną ilość pieniędzy.

    Dla jeszcze lepszego efektu powiedzmy, że za 10 złotych możemy kupić
    kebaba. W ostatecznej formie nasze twierdzenie brzmi więc: jeżeli mam
    złotówkę, to mogę kupić nieograniczoną ilość kebabów.

    Jak widać, logika formalna (przynajmniej w takiej postaci, w jakiej ją
    poznajemy) nie nadaje się do rozumowania na temat zasobów. Zasobów, bo
    tym właśnie są pieniądze i kebaby. Zasoby to byty, które można
    przetwarzać, przemieszczać i zużywać, ale nie można ich kopiować i
    tworzyć z niczego. Powyższe twierdzenie dobitnie pokazuje, że zdania
    logiczne nie mają nic wspólnego z zasobami, gdyż ich dowody mogą być
    bez ograniczeń kopiowane. *)

(* begin hide *)
Fixpoint andn (n : nat) (P : Prop) : Prop :=
match n with
| 0 => True
| S n' => P /\ andn n' P
end.

Lemma one_to_many :
  forall (n : nat) (P : Prop),
    P -> andn n P.
Proof.
  induction n as [| n']; cbn; intros.
    trivial.
    split; try apply IHn'; assumption.
Qed.

Lemma buy_all_kebabs :
  forall P Q : Prop,
    (andn 10 P -> Q) -> P -> forall n : nat, andn n Q.
Proof.
  intros P Q H p n. revert P Q H p.
  induction n as [| n']; cbn; intros.
    trivial.
    split.
      apply H. apply (one_to_many 10 P). assumption.
      apply (IHn' P Q H p).
Qed.
(* end hide *)

(** **** Ćwiczenie (formalizacja paradoksu) *)

(** UWAGA TODO: to ćwiczenie wymaga znajomości rozdziału 2, w szczególności
    indukcji i rekursji na liczbach naturalnych.

    Zdefiniuj funkcję [andn : nat -> Prop -> Prop], taką, że [andn n P]
    to n-krotna koniunkcja zdania [P], np. [andn 5 P] to
    [P /\ P /\ P /\ P /\ P]. Następnie pokaż, że [P] implikuje [andn n P]
    dla dowolnego [n].

    Na końcu sformalizuj resztę paradoksu, tzn. zapisz jakoś, co to znaczy
    mieć złotówkę i że za 10 złotych można kupić kebaba. Wywnioskuj stąd,
    że mając złotówkę, możemy kupić dowolną liczbę kebabów.

    Szach mat, Turcjo bankrutuj! *)

(** ** Logiki substrukturalne - kwantowa teoria relewantnego hajsu *)

(** W jednym z poprzednich podrozdziałów dowiedzieliśmy się, że łatwym
    sposobem na uzyskanie nowej logiki jest wziąć logikę konstruktywną
    i coś z niej wyrzucić (spójniki lub ich aspekty, jak np. _ex falso
    quodlibet_). Tak powstałe logiki nazywaliśmy subintuicjonistycznymi.

    Logiki substrukturalne opierają się na podobnym pomyśle: weź
    logikę konstruktywną i coś z niej wyrzuć. O ile jednak większość
    logik subintuicjonistycznych jest mało ciekawa, a wyrzucanie ma
    na celu jedynie upozorowanie uzyskania nowej logiki, o tyle w
    przypadku logik substrukturalnych jest inaczej. Dzieje się tak,
    gdyż tym, co wyrzucamy, są reguły strukturalne. Stąd też nazwa:
    logiki substrukturalne.

    Czym są reguły strukturalne? Sa to reguły, które mówią, jakie
    operacje wolno wykonywać na hipotezach, które mamy w kontekście:
    - reguła zamiany (ang. exchange) pozwala zamieniać hipotezy
      miejscami
    - reguła kontrakcji (ang. contraction) pozwala kopiować hipotezy
    - reguła osłabiania (ang. weakening) pozwala kasować hipotezy

    W Coqu objawiają się one tak: *)

Lemma structural_rules_test :
  forall P Q R : Prop, (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros P Q R H q p.

  (* reguła zamiany - zamieniamy [p] i [q] miejscami *)
  move p after q.

  (* reguła kontrakcji - kopiujemy [p] i nazywamy kopię [p'] *)
  pose proof p as p'.

  (* reguła osłabiania - kasujemy [p'] *)
  clear p'.

  (* Zauważ, że nie trzeba tych reguł używać explicite -
     taktyki same potrafią znajdować hipotezy w kontekście. *)
  apply H.
    exact p.
    exact q.
Qed.

(** Jako, że kontekst jest rzeczą absolutnie podstawową przy dowodzeniu
    czegokolwiek, (nie)obecność tych reguł ma absolutnie kluczowy wpływ
    na to, co da się w danej logice udowodnić, a w związku z tym także
    na to, jak możemy daną logikę interpretować.

    Jeżeli zastanawiasz się, dlaczego nie spotkaliśmy się dotychczas z
    tymi regułami, skoro są one tak ważne, to powód tego jest prosty:
    ręczne ich używanie byłoby upierdliwe, więc są one wbudowane w
    działanie Coqowych kontekstów oraz taktyk i z tego powodu zazwyczaj
    są zupełnie niewidzialne. Nie musimy zamieniać hipotez miejscami, bo
    taktyki [exact] czy [assumption] same potrafią znaleźć odpowiednią
    hipotezę. Dzięki temu dowodzenie jest bardzo wygodne.

    Dobra, czas najwyższy poznać poszczególne logiki substrukturalne i
    dowiedzieć się, do czego można ich użyć. Na dobry początek rzućmy
    okiem na poniższe twierdzenia: *)

Lemma yes_deleting :
  forall P : Prop, P -> True.
(* begin hide *)
Proof.
  intros P _. trivial.
Qed.
(* end hide *)

Lemma yes_cloning :
  forall P : Prop, P -> P /\ P.
(* begin hide *)
Proof.
  intros P p. split; assumption.
Qed.
(* end hide *)

(** Ich nazwy mają z założenia przywodzić na myśl twierdzenia znane
    z kwantowej teorii informacji:
    - twierdzenie o nieusuwaniu (ang. no-deleting theorem)
    - twierdzenie o nieklonowaniu (ang. no-cloning theorem).

    Twierdzenia te w uproszczeniu (sorry, nie jestem fizykiem) mówią,
    że kwantowa informacja nie może ot tak sobie pojawiać się i znikać
    (w przeciwieństwie do pewnego polskiego rapera).
    Bardziej poetycko można powiedzieć, że zachodzi prawo
    zachowania kwantowej informacji. Ponieważ w Coqu udało nam się
    bez problemu udowodnić przeczące im twierdzenia o usuwaniu
    ([yes_deleting]) oraz klonowaniu ([yes_cloning]), Coqowa logika
    nie nadaje się do rozumowania na temat kwantowej teorii informacji.

    Nadaje się za to do tego logika zwana liniową, czyli taka, w której
    nie ma reguły osłabiania ani reguły kontrakcji. W logice tej musimy
    dokładnie jeden raz użyć każdej hipotezy, którą mamy w kontekście.
    Hipotezy w logice liniowej mogą płynąć przez nasz dowód w dowolnej
    kolejności, ale nie mogą pojawiać się ani znikać, niczym kwantowa
    informacja. To sprawia, że logika liniowa jest dobrym kandydatem
    na logikę kwantową.

    Ale zejdźmy na ziemię - można tutaj znaleźć wystarczająco dużo
    rzeczy, których nie ima się zwyczajna logika, jak na przykład
    wungiel. Wungiel jest znacznie bardziej podobny do kwantowej
    informacji niż do zdań znanych z logiki konstruktywnej czy
    klasycznej:
    - Elektrownia może wungiel spalić (wywołując tym sposobem globalne
      ocieplenie... albo i nie - zależy w co kto wierzy), ale nie może
      go skasować tak, żeby zniknął ze wszechświata bez śladu.
    - Podobnie górnik może wungiel wykopać z ziemii, ale nijak nie
      może go skopiować, tak żeby za darmo uzyskać więcej.

    A więc logika liniowa to nie tylko logika kwantowej informacji, ale
    także logika wungla i w ogólności logika zasobów. Jej zdania możemy
    interpretować jako zasoby (np. [P] może oznaczać 5 kilo wungla, a
    [Q] - ilość energii potrzebną do zasilania twojego komputera przez
    godzinę), zaś spójniki możemy interpretować jako operacje na tych
    zasobach, np. liniową implikację [P -> Q] można interpretować jako
    "z 5 kilo wungla da się  wyprodukować tyle energii, żeby zasilić
    twój komputer przez godzinę". Dowody w logice liniowej oznaczają
    w takim wypadku sposoby na przekształcenie zasobów reprezentowanych
    przez hipotezy w zasoby reprezentowane przez konkluzję.

    Z deczka odmienne spojrzenie na zasoby ma logika afiniczna: jest
    to logika substrukturalna, w której są reguły zamiany i osłabiania,
    ale nie ma reguły kontrakcji. Parafrazując: logika afiniczna wymusza
    użycie każdej hipotezy znajdującej się w kontekście co najwyżej raz.

    Rodzajem zasobów, o których można rozumować za pomocą tej logiki,
    są na przykład pieniądze (pomijając kwestie związane z fałszowaniem):
    jeżeli masz banknot o nominale 100 zł, nie możesz go skopiować żeby
    uzyskać 200 zł, ale możesz go zniszczyć (np. pociąć), żeby uzyskać
    0 zł.

    Jednak rodzajem zasobów, do rozumowania o których logika afiniczna
    nadaje się najlepiej, są zasoby abstrakcyjne, takie jak uchwyty do
    plików czy połączenia z bazą danych. Pisząc program możemy chcieć
    otworzyć plik lub nie (co najwyżej jedno użycie uchwytu), ale jak
    ognia unikać chcemy sytuacji, kiedy dwa programy na raz otworzą
    ten sam plik i zaczną coś do niego zapisywać, niwecząc nawzajem
    swoje starania (dwa użycia uchwytu). Logika afiniczna pozwala łatwo
    rozumować o tego typu sytuacjach i dlatego jest ona raczej domeną
    informatyków niż fizyków kwantowych czy filozofów.

    Podobną logiką substrukturalną, która tym razem najbliższa jest
    sercu filozofów, jest logika relewantna (słowo "relewantny" znaczy
    mniej więcej "istotny" albo "związany z czymś") . To logika, która
    ma reguły zamiany i kontrakcji, ale brak reguły osłabiania. W efekcie
    każdej hipotezy znajdującej się w kontekście musimy użyć co najmniej
    raz. Filozofowie (przynajmniej niektórzy) kochają tę logikę, gdyż to
    ograniczenie sprawia, że przesłanki implikacji muszą być powiązane z
    konkluzją (czyli właśnie relewantne).

    Typowym przykładem implikacji z irrelewantną przesłanką jest zdanie
    w stylu "jeżeli księżyc jest zrobiony z sera, to 2 + 2 = 4". Zdanie
    to jest prawdziwe w logice konstruktywnej i klasycznej, gdyż jego
    konkluzja, [2 + 2 = 4], jest słuszna (jak w Coqu działają liczby,
    dowiemy się już niedługo!). Jednak tego typu implikacje
    są mocno nieintuicyjne i często sprawiają problem niematematycznym
    osobom, a także studentom pierwszego roku i co po niektórym filozofom
    właśnie.

    Powód tego jest prosty: co ma piernik do wiatraka? W języku polskim
    (i każdym innym) mowiąc "jeżeli ..., to ..." zazwyczaj mamy na myśli
    jakiś rodzaj związku przyczynowo-skutkowego ("jeżeli pada deszcz to
    jest mokro"), którego w powyższym zdaniu z serowym księżycem brakuje.
    Z tego powodu laikom wydaje się ono nienaturalne i mylą się oni w
    ocenie jego matematycznej słuszności. Logika relewantna rozwiązuje
    problem, który filozofowie mają z takimi zdaniami, gdyż nie można
    ich w tej logice udowodnić: każdej hipotezy musimy użyć co najmniej
    raz, ale ponieważ hipoteza "księżyc jest zrobiony z sera" nie została
    użyta, dowód implikacji nie przechodzi.

    Czy to już wszystkie logiki substrukturalne? Niezupełnie: unikalną
    logikę substrukturalną daje każda kombinacja reguł strukturalnych
    (poza sytuacją, gdy mamy wszystkie - wtedy logika jest "normalna",
    czyli po prostu strukturalna). Niektóre kombinacje reguł nie są
    jednak zbyt popularne - wszystkie omówione wyżej logiki miały regułę
    zamiany. Wynika to z faktu, że brak tej reguły jest naprawdę srogo
    upierdliwy, a pozostałe reguły mają w przypadku jej nieobecności dużo
    mniejszą moc i znaczenie.

    Mimo to nic nie stoi na przeszkodzie, by rozważać logiki bez żadnych
    reguł strukturalnych. W logikach takich jesteśmy zmuszeni użyć
    wszystkich hipotez z kontekstu dokładnie raz w kolejności, w której
    je wprowadzono. Mogłoby się wydawać, że w tak ograniczonej logice
    nie da się udowodnić niczego ciekawego. Dla przykładu, zastosowanie
    reguły modus ponens może być niemożliwe, jeżeli hipotezy są ułożone
    w kontekście w niesprzyjającej kolejności.

    Tego typu rozważania prowadzą jednak do konkluzji: jeżeli nasza
    implikacja ma przesłanki nie po kolei, to... wprowadźmy drugą
    implikację, która bierze przesłanki w odwrotnej kolejności. To
    rozwiązanie może się wydawać dziwne (i jest!), ale okazuje się,
    że co najmniej jeden człowiek próbował takiej poczwarnej logiki
    użyć do reprezentowania języka naturalnego, i to z niemałym sukcesem.

    Zresztą, język naturalny ze swoimi ograniczeniami na szyk zdania
    i kolejność słów zdaje się być dobrym kandydatem do spożytkowania
    takiej logiki: zdanie "otworzyłem drzwi i wszedłem do środka"
    wygląda całkiem normalnie, ale "wszedłem do środka i otworzyłem
    drzwi" jest już nieco podejrzane. Może to sugerować, że w języku
    naturalnym koniunkcja (czyli "i") nie jest przemienna, a zatem
    pozbycie się reguły zamiany (co uniemożliwia udowodnienie prawa
    [P /\ Q <-> Q /\ P]) sprawia, że [/\] lepiej wyraża znaczenie "i".

    Jednak dużo ważniejsza od całej tej powyższej logiki była uwaga
    o wprowadzeniu dodatkowej implikacji. Odkrywanie dodatkowych
    spójników, które potrafią wyrażać rzeczy niemożliwe do wyrażenia
    w logice konstruktywnej, albo rozkładają znaczenia spójników tej
    logiki na kawałki, jest jednym z głównych powodów zainteresowania
    logikami substrukturalnymi.

    Dla przykładu, określenie "logika liniowa", którego użyłem wcześniej
    jako nazwy logiki bez reguł kontrakcji i osłabiania, w poważnej
    literaturze oznacza wprawdzie logikę bez tych reguł, ale mającą też
    parę dodatkowych spójników. Pojawia się między innymi jednoargumentowy
    spójnik [!] (wykrzyknik), który wyraża kopiowanie: jeżeli [A] oznacza
    "wungiel", to [!A] oznacza "dowolna ilość wungla". Dzięki niemu można
    w logice liniowej rozumować nie tylko o zasobach (albo kwantowej
    informacji, co kto lubi), ale także przeprowadzać rozumowania znane
    z logiki konstruktywnej - wystarczy w odpowiednie miejsca powstawiać
    wykrzykniki. Daje nam to nowy obraz konstruktywnych spójników jako
    połączenia operacji na zasobach oraz operacji kopiowania zasobów w
    nieskończoność.

    Podsumowując, logiki substrukturalne bywają użyteczne w całej
    gamie różnych zastosowań, od fizyki kwantowej, przez filozofię
    i lingwistykę, a na informatyce teoretycznej kończąc. W tej
    książce nie będziemy się jednak nimi zajmować, gdyż nie ma do
    tego wystarczających możliwości technicznych: logika Coqa jest
    z gruntu strukturalna i nic nie możemy na to poradzić (badania
    nad połączeniem języków pokroju Coqa z logiką substrukturalną
    trwają, ale nie przyniosły jeszcze zadowalających rezultatów).

    Na samiuśki koniec koło ratunkowe: jeżeli pogubiłeś się w tych
    wszystkich nazwach, regułach, warunkach, etc., to tutaj jest
    #<a class='link'
        href='https://github.com/wkolowski/Typonomikon/blob/master/txt/ściągi/substrukturalne.md'>
    ściąga</a>#. *)

(** ** Logiki wielowartościowe *)

(** Innym sposobem klasyfikacji logik jest liczba wartości logicznych,
    które w nich występują. Ponieważ wartości logiczne nie występują
    we wszystkich logikach, a w szczególności nie ma ich w logice
    konstruktywnej, zacznijmy od wytłumaczenia, czym są.

    W skrócie: wartości logiczne mówią, jaki może być "status" danego
    zdania. Dwiema wartościami logicznymi, które występują praktycznie
    zawsze, są "prawda" i "fałsz". Odpowiadają one stwierdzeniom takim
    jak "zdanie P jest prawdziwe" oraz "zdanie P jest fałszywe".

    Najpopularniejszą logiką, którą można zaprezentować za pomocą
    wartości logicznych (i prawie zawsze się tak robi - my oczywiście
    jesteśmy wyjątkiem) jest logika klasyczna. Logika klasyczna to
    logika, w której każde zdanie jest albo prawdziwe, albo fałszywe
    i nie ma żadnych innych możliwości.

    Nie powinno cię to dziwić - jeżeli przyjrzeć się mu bliżej, to
    właśnie mówi aksjomat wyłączonego środka: dla każdego zdania
    albo mamy jego dowód (co odpowiada wartości logicznej "prawda"),
    albo mamy dowód jego zaprzeczenia (co odpowiada wartości logicznej
    "fałsz").

    Skoro już wiemy, czym są wartości logiczne, czas powiedzieć, czym
    są logiki wielowartościowe. Otóż są to logiki, w których są więcej
    niż dwie wartości logiczne. Zazwyczaj są to "prawda", "fałsz" i
    jakieś dodatkowe, np. "być może", "jednocześnie prawda i fałsz",
    "nie obchodzi mnie to nic a nic", "brak danych", "twoja stara", etc. -
    każdy może sobie wymyślić własną logikę z własną paletą wartości logicznych.

    Przykładem ciekawej logiki wielowartościowej jest logika sygnałów
    w obwodach elektronicznych, ustandaryzowana przez IEEE. Jest to
    logika czterowartościowa, w której są następujące wartości logiczne:
    - 1, interpretowane jako "prawda"
    - 0, interpretowane jako "fałsz"
    - X, interpretowane jako "nieważne" - może zostać uznana za
      1 albo 0 w zależności od tego, co jest wygodniejsze w danej
      sytuacji (w praktyce wybiera się to, co daje szybsze obliczenia)
    - Z, interpretowane jako "wysoka impedancja" - reprezentuje sytuację,
      w której prąd w obwodzie nie płynie tak jak powinien, czyli pewien
      rodzaj błędu

    Przykładem nieciekawej logiki wielowartościowej jest logika rozmyta.
    Motywacją dla tej logiki są pytania w stylu "Czy koleś o wzroście
    180 cm jest wysoki?". Żeby móc na nie odpowiadać, jako wartości
    logiczne bierzemy liczby rzeczywiste z przedziału [[0; 1]], gdzie 0
    reprezentuje fałsz, 1 prawdę, a wszystkie inne liczby - pewne
    pośrednie stopnie pewności. I tak odpowiedzią na pytanie "Czy 180
    cm to wysoki wzrost?" może być np. 0.9, czyli raczej tak, ale nie
    do końca, zaś na pytanie "Czy 140 cm to wysoki wzrost?" odpowiedź
    może brzmieć 0.1, czyli raczej niski, ale przecież dzieci i karły
    są niższe.

    Powiązanym przykładem nieciekawej logiki jest logika probabilistyczna.
    Pomysł jest taki, że większość rzeczy w prawdziwym świecie jest dość
    niepewna, więc zamiast przypisywać zdaniom wartości logiczne w stylu
    "prawda" czy "fałsz", należy zastąpić je ocenami prawdopodobieństwa,
    czyli podobnie jak w logice rozmytej, liczbami z przedziału [[0; 1]].

    O ile teoria prawdopodobieństwa jest bardzo mądra i użyteczna, to
    dwie powyższe logiki (i wszelkie ich warianty) są zupełnie do dupy
    i bezużyteczne właśnie dlatego, że są próbami wsadzenia
    prawdopodobieństwa do logiki na siłę, czego efekt jest marny.

    Ogólnie logiki wielowartościowe nie są zbyt ciekawe ani przydatne,
    więc nie będziemy ich zgłębiać.

    Na koniec wypadałoby jeszcze wspomnieć w ramach ciekawostki, że
    wbrew temu, co napisałem na samym początku, logika konstruktywna
    również może być uznana za logikę wielowartościową, jednak bardzo
    nietypową: wartości logicznych jest nieskończenie wiele (a nawet
    nieprzeliczalnie wiele, czyli tyle co liczb rzeczywistych). Nie
    będziemy jednak drążyć tego tematu. *)

(** ** Logika szalonego Gruzina *)

(** Logika szalonego Gruzina, oficjalnie zwana logiką obliczeń
    (ang. Computability Logic, w skrócie CoL), jest szalenie
    ciekawa i właśnie dlatego się tutaj znalazła. Żeby jednak
    nie odciągać cię od jakże wartościowego zajęcia, jakim jest
    czytanie niniejszej książki, nie podam tu żadnych linków do
    źródeł na temat tej logiki.

    Czym jest CoL? Zdania w CoL reprezentują problemy obliczeniowe,
    (czyli zagadnienia w stylu "czy da się napisać program, który
    robi cośtam"), zaś dowody to rozwiązania tych problemów. Żeby
    było ciekawiej, problemy są interaktywne i przybierają formę
    gier, w której naprzeciw siebie staje dwóch graczy: maszyna
    (nasz faworyt) i środowisko (diabeł wcielony). Maszyna musi
    w tych grach posługiwać się strategiami obliczalnymi (czyli,
    krótko mówiąc, nie może brać swoich ruchów z sufitu), jednak
    środowisko już niekoniecznie. Skoro zdania to interaktywne gry,
    dowody zdań reprezentują strategie wygrywające w tych grach.

    Spójników logicznych jest tu cała masa i są naprawdę fikuśne,
    np. negacja zamienia graczy stronami. Jeżeli zdanie [Chess]
    reprezentuje partię szachów gdzie maszyna gra białymi (lub,
    precyzyjniej pisząc, problem "czy istnieje niezawodny sposób
    na wygranie partii szachów białymi?"), to zdanie [~ Chess] to
    partia szachów, w której maszyna gra czarnymi (lub, precyzyjniej
    pisząc, problem "czy istnieje niezawodny sposób na wygranie partii
    szachów czarnymi?").

    Dalej mamy takie cuda jak równoległa koniunkcja i dysjunkcja
    gier, które polegają na tym, że toczą się na raz dwie gry i
    żeby wygrać, trzeba wygrać w obu (koniunkcja) lub co najmniej
    jednej z nich (dysjunkcja).

    Spójniki równoległe zachowują się tak jak spójniki w logice
    klasycznej, w szczególności zachodzi prawo wyłączonego środka.
    W ramach przykładu rozważmy zdanie [Chess \/ ~ Chess]. Jest to
    gra, która składa się z dwóch partii szachów rozgrywanych w tym
    samym czasie. W pierwszej partii maszyna gra białymi, a środowisko
    czarnymi, a w drugiej na odwrót. Wygrywa ten, kto wygra choć jedną
    partię.

    Istnieje bardzo prosta strategia, żeby wygrać [Chess \/ ~ Chess]:
    wystarczy w jednej z partii małpować ruchy, które przeciwnik robi
    w drugiej partii. Wtedy jedna gra jest przegrana a druga wygrana,
    czyli zwycięzcą całej równoległodysjunkcjowej gry jest maszyna.

    Są też spójniki wyborowe: wyborowa koniunkcja i wyborowa dysjunkcja.
    Polegają one na tym, że na początku są dwie gry i w pierwszym ruchu
    wybiera się, w którą grę będzie się grać (w przypadku dysjunkcji
    wybiera maszyna, w przypadku koniunkcji - środowisko). Tutaj prawo
    wyłączonego środka już nie zachodzi - jeżeli maszyna jest kiepska w
    szachy, to przegra niezależnie od tego, czy będzie grać białymi czy
    czarnymi. Spójniki wyborowe zachowują się tak, jak spójniki znane z
    logiki konstruktywnej.

    Wesoło, prawda? A to nie wszystko, bo rodzajów spójników jest co
    najmniej dwa razy więcej. Jakby tego było mało, spójniki uogólniają
    się potem na kwantyfikatory i dzięki temu mamy różne wesołe zdania,
    które reprezentują np. rozgrywanie nieskończenie wielu partii szachów
    na raz. Brzmi dobrze? Jasne, a jak jeszcze zauważysz, że nawet słowem
    nie zająknąłem się dotychczas o implikacji... oj, w logice szalonego
    Gruzina zabawy jest co nie miara. Na koniec dodam jeszcze tylko, że
    fragmentami CoL są nie tylko logika klasyczna (spójniki równoległe)
    oraz logika konstruktywna (spójniki wyborowe), ale też logika liniowa
    (jedna z tych opisanych w podrozdziale o logikach substrukturalnych)
    i jeszcze kilka innych, których nie ogarniają nawet najstarsi górale. *)

(** * Pluralizm logiczny *)

(** Celem niniejszego rozdziału było zapoznanie się z logikami innymi
    niż nasza ulubiona i domyślna logika konstruktywna, tak na wypadek
    gdybyś się zastanawiał, czy są jakieś.

    Obraz, który się z niego wyłania, jest niesamowicie ciekawy oraz
    zaskakujący, gdyż mocno kontrastuje z tradycyjnym postrzeganiem
    i zwyczajem nauczania logiki:
    - nie ma jednej logiki, lecz wiele (i to nieskończenie wiele)
    - każda z wielu logik opisuje nieco inny świat, choć można też
      patrzeć na to w ten sposób, że każda logika opisuje nasz świat
      w nieco inny sposób
    - logiki nie są równoprawne - najlepsza jest logika konstruktywna,
      najpopularniejsza wśród matematyków jest logika klasyczna, ale
      jest też cała (nieskończona) masa logik niewartych nawet splunięcia
    - różne logiki nie są sobie wrogie, nieprzyjazne czy sprzeczne ze
      sobą, lecz harmonijnie współistnieją dzięki modalnościom, za pomocą
      których można je wyrażać

    Powyższy pogląd możemy nazwać pluralizmem logicznym. Jego podstawowe
    wcielenie zostało wymyślone i nazwane przez filozofów i w związku z
    tym dotyczyło raczej logiki filozoficznej niż logiki matematycznej
    (a już na pewno nie miało nic wspólnego z informatyką). Niektórzy
    filozofowie wyznają go pewnie do dziś, inni zaś są jego zawziętymi
    przeciwnikami. Filozofowie jednak są mało ważni i nikt nie traktuje
    ich poważnie, więc to nie im należy zawdzięczać rozprzestrzenianie
    się tego poglądu.

    Nie należy go też zawdzięczać matematykom. Nie jest on wśród nich
    zbyt popularny, gdyż w zasadzie wszyscy matematycy są fanatykami
    logiki klasycznej. Nie żeby matematycy znali się na logice - co
    to, to nie. Typowy matematyk nie ma bladego pojęcia o logice.
    Matematycy po prostu robią swoje, a tym, co naturalnie im z tego
    wychodzi, jest logika klasyczna. Nawet matematycy zajmujący się
    stricte logiką (a może w szczególności oni) posługują się na codzień
    logiką klasyczną, a inne logiki są co najwyżej przedmiotem ich badań,
    niczym zwierzątka w cyrku, zoo czy na safari.

    Pragmatycznymi zwolennikami tego poglądu są z pewnością olbrzymie
    masy informatyków (teoretycznych, nie kolesi od podłączania kabli).
    W dziedzinie tej wymyślono tabuny przeróżnych logik, które służą
    do jakiegoś konkretnego celu, zazwyczaj do rozumowania o jednym
    rodzaju obiektów czy sytuacji. Dla przykładu, logika temporalna
    (z takimi operatorami jak "zawsze", "nigdy", "kiedyś" etc.) bywa
    używana w formalnej weryfikacji sprzętu... albo czegoś tam innego,
    nie wiem, nie znam się na tym.

    Poparcie dla pluralizmu logicznego jest w
    informatyce uniwersalne i nieświadome. Przyczyną tego jest fakt, że
    logiki są tu traktowane jak narzędzia - logika temporalna ma ten sam
    status co młotek lub wiertarka. Jeżeli ktoś powie ci, że twój młotek
    jest sprzeczny, a jego narzędzie jest najlepsze do wszystkiego, nie
    będziesz przecież traktował go poważnie, prawda? W ostateczności
    jednak, to również nie informatycy są powodem tego, że w tej właśnie
    chwili czytasz o pluralizmie logicznym.

    Prawdziwą przyczyną popularności tego poglądu jest bardzo wąski krąg,
    wręcz sekta, dziwacznych ezoteryków (do których i ja należę) żyjących
    gdzieś w otchłani pomiędzy matematyką i informatyką, a takżę trochę
    fizyką i filozofią. Ludzie ci nie mają jednej nazwy, a zajmują się
    wieloma dziedzinami - teorią typów, teorią kategorii, teorią języków
    programowania, podstawami matematyki (ang. foundations), matematyką
    konstruktywną, matematyką syntetyczną, etc. - mniejsza o to.

    Podstawowym filarem naszej
    wiary (nieopartym jednak na dogmatach, ani nawet na aksjomatach, lecz
    raczej na twierdzeniach i obserwacjach) jest pewna konstatacja: każdy
    rodzaj (abstrakcyjnych) obiektów ma swój własny język, w którym mówi
    się o nich najlepiej - można je łatwo opisywać, konstruować, a także
    dowodzić ich właściwości. Każdy rodzaj bytów to osobny abstrakcyjny
    świat, a każdy taki świat ma swój język.

    Ponieważ światów jest wiele,
    to i języków jest wiele. Ponieważ światy są ze sobą związane różnymi
    ciekawymi relacjami, języki również są powiązane. Niektóre obiekty
    są bardziej ogólne od innych, więc w niektórych językach można
    powiedzieć więcej, a w innych mniej. Niektóre obiekty są tak ogólne,
    że można ich użyć do reprezentowania wszystkich innych obiektów, a
    zatem niektóre języki mają status uniwersalny i umożliwiają
    powiedzenie wszystkiego.

    Logika konstruktywna oczywiście nie jest takim uniwersalnym językiem.
    Prawdę mówiąc, jest ona bardzo biedna i prymitywna, gdyż jest jedynie
    przejawem dużo potężniejszego języka, a mianowicie teorii typów, którą
    implementuje Coq. Naszym celem w tej książce (a szczególnie poczynając
    od następnego rozdziału) będzie dogłębnie poznać tę teorię i nauczyć
    się nią posługiwać. *)

(** ** Pluralizm w praktyce: płytkie zanurzenie *)

(** Tutaj nie wiem o czym, może o omówionej już logice modalnej? *)

(** ** Pluralizm w praktyce: uniwersum [SProp] i logika klasyczno-konstruktywna (TODO) *)

(* TODO: Tutaj można opisać świat, w którym [SProp] ma logikę klasyczną, a
   TODO: [Prop] konstruktywną. *)

(** Przemyślenia: w uniwersum [SProp] prawo wyłączonego środka jest w sumie
    słuszne, ponieważ mimo bycia aksjomatem normalnie się oblicza. *)

Inductive sor (P Q : SProp) : SProp :=
| sinl : P -> sor P Q
| sinr : Q -> sor P Q.

Inductive Empty : SProp := .

Definition snot (P : SProp) : SProp := P -> Empty.

Axiom sLEM : forall P : SProp, sor P (snot P).

Lemma jedziemy_na_sor : sor Empty (snot Empty).
Proof.
  right. intro. assumption.
Qed.

Inductive seqs {A : SProp} (x : A) : A -> SProp :=
| refl : seqs x x.

Lemma lem_sie_oblicza :
  seqs (sLEM Empty) jedziemy_na_sor.
Proof.
  reflexivity.
Qed.

Inductive Unit : SProp :=
| stt : Unit.

Definition b2sp (b : bool) : SProp :=
match b with
| true  => Unit
| false => Empty
end.

(** * Zadania: logiki pośrednie (TODO) *)

(** ** Logika słabego wyłączonego środka *)

Definition WLEM : Prop :=
  forall P : Prop, ~ P \/ ~ ~ P.

Lemma WLEM_hard :
  forall P : Prop, ~ P \/ ~ ~ P.
(* begin hide *)
Proof.
  intro P. left. intro p.
Restart.
  intro P. right. intro np. apply np.
Abort.
(* end hide *)

Lemma Irrefutable_WLEM :
  forall P : Prop, ~ ~ (~ P \/ ~ ~ P).
(* begin hide *)
Proof.
  intros P H.
  apply H. left. intro p.
  apply H. right. intro np.
  contradiction.
Qed.
(* end hide *)

Lemma LEM_WLEM :
  LEM -> WLEM.
(* begin hide *)
Proof.
  unfold LEM, WLEM.
  intros LEM P.
  destruct (LEM P) as [p | np].
    right. intro np. contradiction.
    left. assumption.
Qed.
(* end hide *)

Lemma MI_WLEM :
  MI -> WLEM.
(* begin hide *)
Proof.
  unfold MI, WLEM.
  intros MI P.
  destruct (MI P P) as [np | p].
    trivial.
    left. assumption.
    right. intro np. contradiction.
Qed.
(* end hide *)

Lemma ME_WLEM :
  ME -> WLEM.
(* begin hide *)
Proof.
  unfold ME, WLEM.
  intros ME P.
  destruct (ME P P) as [[p _] | [np _]].
    split; trivial.
    right. intro np. contradiction.
    left. assumption.
Qed.
(* end hide *)

Lemma DNE_WLEM :
  DNE -> WLEM.
(* begin hide *)
Proof.
  unfold DNE, WLEM.
  intros DNE P.
  apply DNE.
  intro H. apply H.
  right. intro np.
  apply H.
  left. assumption.
Qed.
(* end hide *)

Lemma CM_WLEM :
  CM -> WLEM.
(* begin hide *)
Proof.
  unfold CM, WLEM.
  intros CM P.
  apply CM. intro H.
  right. intro np.
  apply H.
  left. assumption.
Qed.
(* end hide *)

Lemma Peirce_WLEM :
  Peirce -> WLEM.
(* begin hide *)
Proof.
  unfold Peirce, WLEM.
  intros Peirce P.
  apply (Peirce _ False).
  intro H.
  right. intro np.
  apply H.
  left. assumption.
Qed.
(* end hide *)

Lemma Contra_WLEM :
  Contra -> WLEM.
(* begin hide *)
Proof.
  unfold Contra, WLEM.
  intros Contra P.
  apply (Contra True).
    intros H _. apply H. right. intro np. apply H. left. assumption.
    trivial.
Qed.
(* end hide *)

Definition LEM3 : Prop :=
  forall P : Prop, P \/ ~ P \/ ~ ~ P.

Lemma LEM3_WLEM :
  LEM3 -> WLEM.
(* begin hide *)
Proof.
  unfold LEM3, WLEM.
  intros LEM3 P.
  destruct (LEM3 P) as [p | [np | nnp]].
    right. intro np. contradiction.
    left. assumption.
    right. assumption.
Qed.
(* end hide *)

Lemma WLEM_LEM3 :
  WLEM -> LEM3.
(* begin hide *)
Proof.
  unfold WLEM, LEM3.
  intros WLEM P.
  destruct (WLEM P) as [np | nnp].
    right. left. assumption.
    right. right. assumption.
Qed.
(* end hide *)

Lemma LEM_LEM3 :
  LEM -> LEM3.
(* begin hide *)
Proof.
  unfold LEM, LEM3.
  intros LEM P.
  destruct (LEM P) as [p | np].
    left. assumption.
    right. left. assumption.
Qed.
(* end hide *)

(** *** Logika zdań słabo określonych *)

Definition WeaklyDefinite (P : Prop) : Prop :=
  ~ P \/ ~ ~ P.

Lemma WeaklyDefinite_True :
  WeaklyDefinite True.
(* begin hide *)
Proof.
  unfold WeaklyDefinite.
  now right.
Qed.
(* end hide *)

Lemma WeaklyDefinite_False :
  WeaklyDefinite False.
(* begin hide *)
Proof.
  unfold WeaklyDefinite.
  now left.
Qed.
(* end hide *)

Lemma WeaklyDefinite_impl :
  forall P Q : Prop,
    WeaklyDefinite P -> WeaklyDefinite Q -> WeaklyDefinite (P -> Q).
(* begin hide *)
Proof.
  unfold WeaklyDefinite.
  intros P Q pnp [q | nq].
  - destruct pnp as [np | nnp].
    + right; intros npq.
      apply npq; intros p.
      contradiction.
    + left; intros pq.
      apply nnp; intros p.
      apply q, pq, p.
  - right; intros npq.
    apply nq; intros q.
    apply npq; intros p.
    assumption.
Qed.
(* end hide *)

Lemma WeaklyDefinite_or :
  forall P Q : Prop,
    WeaklyDefinite P -> WeaklyDefinite Q -> WeaklyDefinite (P \/ Q).
(* begin hide *)
Proof.
  unfold WeaklyDefinite.
  intros P Q [np | nnp] WDQ; cycle 1.
  - right; intros npq.
    apply nnp; intros p.
    apply npq; left; assumption.
  - destruct WDQ as [nq | nnq].
    + left; intros [p | q]; contradiction.
    + right; intros npq.
    apply nnq; intros q.
    apply npq; right; assumption.
Qed.
(* end hide *)

Lemma WeaklyDefinite_and :
  forall P Q : Prop,
    WeaklyDefinite P -> WeaklyDefinite Q -> WeaklyDefinite (P /\ Q).
(* begin hide *)
Proof.
  unfold WeaklyDefinite.
  intros P Q [np | nnp] WDQ.
  - left; intros [p q]; contradiction.
  - destruct WDQ as [nq | nnq].
    + left; intros [p q]; contradiction.
    + right; intros npq.
      apply nnp; intros p.
      apply nnq; intros q.
      apply npq; split; assumption.
Qed.
(* end hide *)

Lemma WeaklyDefinite_iff :
  forall P Q : Prop,
    WeaklyDefinite P -> WeaklyDefinite Q -> WeaklyDefinite (P <-> Q).
(* begin hide *)
Proof.
  now intros; apply WeaklyDefinite_and; apply WeaklyDefinite_impl.
Qed.
(* end hide *)

Lemma WeaklyDefinite_not :
  forall P : Prop,
    WeaklyDefinite P -> WeaklyDefinite (~ P).
(* begin hide *)
Proof.
  now intros; apply WeaklyDefinite_impl, WeaklyDefinite_False.
Qed.
(* end hide *)

Lemma WeaklyDefinite_forall_failed :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, WeaklyDefinite (P x)) -> WeaklyDefinite (forall x : A, P x).
Proof.
  unfold WeaklyDefinite.
  intros A P WDP.
  right; intros np.
  apply np; intros x.
Abort.

Lemma WeaklyDefinite_exists_failed :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, WeaklyDefinite (P x)) -> WeaklyDefinite (exists x : A, P x).
Proof.
  unfold WeaklyDefinite.
  intros A P WDP.
  right; intros np.
Abort.

(** ** Silna negacja koniunkcji i logika de Morgana *)

Definition nand' (P Q : Prop) : Prop := ~ P \/ ~ Q.

Lemma nand_nand' :
  forall P Q : Prop,
    nand' P Q -> nand P Q.
(* begin hide *)
Proof.
  unfold nand, nand'.
  intros P Q [np | nq] [p q]; contradiction.
Qed.
(* end hide *)

Lemma nand'_nand_classically :
  (forall P : Prop, P \/ ~ P) ->
    forall P Q : Prop,
      nand P Q -> nand' P Q.
(* begin hide *)
Proof.
  unfold nand, nand'.
  intros lem P Q npq.
  destruct (lem P) as [p | np].
  - right. intros q. apply npq. split; assumption.
  - left. assumption.
Qed.
(* end hide *)

Lemma nand'_nand_tabu :
  (forall P Q : Prop, nand P Q -> nand' P Q)
    ->
  (forall P : Prop, P \/ ~ P).
(* begin hide *)
Proof.
  unfold nand, nand'.
  intros nand'_nand P.
Abort.
(* end hide *)

(* begin hide *)
Lemma and_true_irref :
  forall P Q : Prop,
    P -> ~ ~ Q -> ~ ~ (P /\ Q).
Proof.
  intros P Q p nnq nnpq.
  apply nnq. intro q.
  apply nnpq.
  split; assumption.
Qed.

Lemma or_false_irref :
  forall P Q : Prop,
    ~ P -> ~ ~ Q -> ~ ~ (P \/ Q).
Proof.
  intros P Q np nnq npq.
  apply nnq. intro q.
  apply npq.
  right. assumption.
Qed.

Lemma or_irref_irref :
  forall P Q : Prop,
    ~ ~ P -> ~ ~ (P \/ Q).
Proof.
  intros P Q nnp npq.
  apply nnp. intro p.
  apply npq.
  left. assumption.
Qed.

Lemma impl_true_irref :
  forall P Q : Prop,
    ~ ~ Q -> ~ ~ (P -> Q).
Proof.
  intros P Q nnq npq.
  apply nnq. intro q.
  apply npq.
  intros _. assumption.
Qed.

Lemma impl_irref_false :
  forall P Q : Prop,
    ~ ~ P -> ~ Q -> ~ (P -> Q).
Proof.
  intros P Q nnp nq pq.
  apply nnp. intro p.
  apply nq, pq.
  assumption.
Qed.
(* end hide *)

Lemma Irrefutable_deMorgan :
  forall P Q : Prop, ~ ~ (~ (P /\ Q) -> ~ P \/ ~ Q).
(* begin hide *)
Proof.
  intros P Q H.
  apply H. intro npq.
  left. intro p.
  apply H. intros _.
  right. intro q.
  apply npq. split.
    assumption.
    assumption.
Qed.
(* end hide *)

Lemma deMorgan_WLEM :
  (forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q)
    <->
  (forall P : Prop, ~ P \/ ~ ~ P).
(* begin hide *)
Proof.
  split.
    intros deMorgan P. apply deMorgan. apply noncontradiction.
    intros WLEM P Q H. destruct (WLEM P) as [np | nnp].
      left. assumption.
      destruct (WLEM Q) as [nq | nnq].
        right. assumption.
        left. intro p. apply nnq. intro. apply H. split; assumption.
Qed.
(* end hide *)

Lemma LEM_deMorgan_big :
  (forall P : Prop, P \/ ~ P) ->
    (forall (A : Type) (P : A -> Prop),
       (~ forall x : A, P x) -> exists x : A, ~ P x).
(* begin hide *)
Proof.
  intros LEM A P H. destruct (LEM (exists x : A, ~ P x)).
    assumption.
    contradiction H. intro x. destruct (LEM (P x)).
      assumption.
      contradiction H0. exists x. assumption.
Qed.
(* end hide *)

Lemma deMorgan_big_WLEM :
  (forall (A : Type) (P : A -> Prop),
     (~ forall x : A, P x) -> exists x : A, ~ P x) ->
  (forall P : Prop, ~ P \/ ~ ~ P).
(* begin hide *)
Proof.
  intros DM P.
  specialize (DM bool (fun b => if b then P else ~ P)).
  cbn in DM. destruct DM as [b H].
    intro H. apply (H false). apply (H true).
    destruct b.
      left. assumption.
      right. assumption.
Qed.
(* end hide *)

(** ** Inne mało ważne logiki pośrednie *)

(** *** [IOR] *)

Definition IOR : Prop :=
  forall P Q R : Prop, (P -> Q \/ R) -> (P -> Q) \/ (P -> R).

Lemma Irrefutable_IOR :
  forall P Q R : Prop,
    ~ ~ ((P -> Q \/ R) -> (P -> Q) \/ (P -> R)).
(* begin hide *)
Proof.
  intros P Q R H.
  apply H.
  intro pqr.
  left. intro p.
  cut False.
    destruct 1.
  apply H. intros _.
  destruct (pqr p).
    left. intros _. assumption.
    right. intros _. assumption.
Qed.
(* end hide *)

Lemma IOR_LEM :
  LEM -> IOR.
(* begin hide *)
Proof.
  unfold IOR, LEM.
  intros lem P Q R f.
  destruct (lem Q) as [q | nq].
  - left. intros _. assumption.
  - right. intros p. destruct (f p) as [q | r].
    + contradiction.
    + assumption.
Qed.
(* end hide *)

(** *** Logika zdań IORowych *)

Definition IORable (P : Prop) : Prop :=
  forall Q R : Prop, (P -> Q \/ R) -> (P -> Q) \/ (P -> R).

Lemma IORable_True :
  IORable True.
(* begin hide *)
Proof.
  unfold IORable.
  intros Q R [q | r]; [trivial | ..].
  - left; intros _; assumption.
  - right; intros _; assumption.
Qed.
(* end hide *)

Lemma IORable_False :
  IORable False.
(* begin hide *)
Proof.
  unfold IORable; firstorder.
Qed.
(* end hide *)

Lemma IORable_impl_failed :
  forall P Q : Prop,
    IORable P -> IORable Q -> IORable (P -> Q).
Proof.
  unfold IORable.
  intros P1 P2 I1 I2 Q R qr.
Abort.

Lemma IORable_or_failed :
  forall P Q : Prop,
    IORable P -> IORable Q -> IORable (P \/ Q).
Proof.
  unfold IORable.
  intros P1 P2 I1 I2 Q R qr.
Abort.

Lemma IORable_and_failed :
  forall P Q : Prop,
    IORable P -> IORable Q -> IORable (P /\ Q).
Proof.
  unfold IORable.
  intros P1 P2 I1 I2 Q R qr.
  left; intros [p1 p2].
  destruct qr as [q | r]; [easy | assumption |].
Abort.

Lemma IORable_iff :
  forall P Q : Prop,
    IORable P -> IORable Q -> IORable (P <-> Q).
Proof.
  unfold IORable.
  intros P1 P2 I1 I2 Q R qr.
Abort.

Lemma IORable_not :
  forall P : Prop,
    IORable P -> IORable (~ P).
Proof.
  unfold IORable.
  intros P I Q R qr.
Abort.

Lemma IORable_forall_failed :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, IORable (P x)) -> IORable (forall x : A, P x).
Proof.
  unfold IORable.
  intros A P HD.
Abort.

Lemma IORable_exists_failed :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, IORable (P x)) -> IORable (exists x : A, P x).
Proof.
  unfold IORable.
  intros A P HD.
Abort.

(** *** Gödel-Dummet *)

Definition GD : Prop :=
  forall P Q : Prop, (P -> Q) \/ (Q -> P).

Lemma Irrefutable_GD :
  forall P Q : Prop, ~ ~ ((P -> Q) \/ (Q -> P)).
(* begin hide *)
Proof.
  intros P Q H.
  apply H. left. intro p.
  exfalso.
  apply H. right. intro q.
  assumption.
Qed.
(* end hide *)

Lemma LEM_GD :
  LEM -> GD.
(* begin hide *)
Proof.
  unfold LEM, GD. intros LEM P Q.
  destruct (LEM P) as [p | np].
    right. intros _. assumption.
    left. intro p. contradiction.
Qed.
(* end hide *)

Lemma MI_GD :
  MI -> GD.
(* begin hide *)
Proof.
  unfold MI, GD.
  intros MI P Q.
  destruct (MI P P) as [np | p].
    trivial.
    left. intro p. contradiction.
    right. intros _. assumption.
Qed.
(* end hide *)

Lemma ME_GD :
  ME -> GD.
(* begin hide *)
Proof.
  unfold ME, GD.
  intros ME P Q.
  destruct (ME P P) as [[p _] | [np _]].
    split; trivial.
    right. intros _. assumption.
    left. intro p. contradiction.
Qed.
(* end hide *)

Lemma DNE_GD :
  DNE -> GD.
(* begin hide *)
Proof.
  unfold DNE, GD.
  intros DNE P Q.
  apply DNE.
  apply Irrefutable_GD.
Qed.
(* end hide *)

Lemma CM_GD :
  CM -> GD.
(* begin hide *)
Proof.
  unfold CM, GD.
  intros CM P Q.
  apply CM. intro H.
  left. intro p.
  exfalso. apply H.
  right. intros _.
  assumption.
Qed.
(* end hide *)

Lemma Peirce_GD :
  Peirce -> GD.
(* begin hide *)
Proof.
  unfold Peirce, GD.
  intros Peirce P Q.
  apply (Peirce _ False). intro H.
  left. intro p.
  exfalso. apply H.
  right. intros _.
  assumption.
Qed.
(* end hide *)

Lemma Contra_GD :
  Contra -> GD.
(* begin hide *)
Proof.
  unfold Contra, GD.
  intros Contra P Q.
  apply (Contra True).
    intros H _. apply H. left. intro p. exfalso.
      apply H. right. intros. assumption.
    trivial.
Qed.
(* end hide *)

(** * Jakieś podsumowanie (TODO) *)

(** Gratulacje! Udało ci się przebrnąć przez pierwszy (poważny) rozdział
    moich wypocin, czyli rozdział o logice. W nagrodę już nigdy nie
    będziesz musiał ręcznie walczyć ze spójnikami czy prawami logiki -
    zrobi to za ciebie taktyka [firstorder]. Jak sama nazwa wskazuje,
    służy ona do radzenia sobie z czysto logicznymi dowodami w logice
    pierwszego rzędu (czyli w takiej, gdzie nie kwantyfikujemy po
    funkcjach albo tympodobnie skomplikowanych rzeczach).

    TODO: zrobić w Anki:
    - test diagnostyczny tak/nie
    - talię do nauki nazw praw
    - talię do nauki tautologia/nietautologia
    - talię do nauki pozytywny/negatywny
    - inne przydatne talie *)

(** Taktyka [firstorder] dopiero na samym końcu! Podobnie [tauto]. *)