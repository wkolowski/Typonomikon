(** * W4: Inne logiki [schowane na końcu dla niepoznaki] *)

(** * Porównanie logiki konstruktywnej i klasycznej (TODO) *)

(** * Inne logiki? *)

(** Słowo "logika" zazwyczaj występuje w liczbie pojedynczej i nie bez
    przyczyny - zazwyczaj naucza się jednej (a nawet jedynej słusznej)
    logiki. Porównawszy logiki konstruktywną i klasyczną nie pozostaje
    nam nic innego jak tylko skonstatować, że jesteśmy bardzo wyjątkowi,
    bo znamy już dwie logiki. Do głowy powinno nam zatem przyjść jedyne
    słuszne w tej sytuacji pytanie: czy są jeszcze jakieś inne logiki?
    Odpowiedź brzmi: tak, i to nawet nieskończenie wiele.

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
    klasyczna, która jest niczym innym jak logiką konstruktywną, w której
    aksjomatem jest prawo wyłączonego środka. Logika klasyczna jest
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
    życia", a amerykańce - "way of life"). Od niego w średniowiecznej
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
    sprzętu, ale o tym nic nie wiem). Idea jest taka, że możemy robić
    zdania wyrażające różne pożądane właściwości programów, na przykład:
    - bezpieczeństwo - program NIGDY nie zrobi niczego złego
    - żywotność - na każde żądanie serwer KIEDYŚ udzieli odpowiedzi

    Mimo tego powiewu przydatności, nie będzie zajmować się logikami
    temporalnymi, ponieważ ich podejście do weryfikacji poprawności
    programów jest diametralnie różne i niekompatybilne z naszym.

    Na koniec krótka przestroga. Przeczytawszy niniejszy podrozdział
    mógłbyś dojść do wniosku, że logiki modalne są bezużyteczne, ale
    wcale tak nie jest. Modalności to nie tylko możliwość, czas albo
    wiedza, których w Coqowej logice brak. Modalności stanowią także
    bardzo ogólny i elegancki sposób patrzenia na rzeczy dobrze nam
    znane, jak logika klasyczna czy podwójna negacja. Przekonamy się
    o tym już niedługo, gdyż tego spojrzenia na modalności dotyczyć
    będzie większość reszty niniejszego rozdziału... ale najpierw
    jeszcze parę innych logik. *)

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
    gdyż tym, co wyrzucamy, są reguły strutkuralne. Stąd też nazwa:
    logiki substrukturalne.

    Czym są reguły strukturalne? Sa to reguły, które mówią, jakie
    operacje wolno wykonywać na hipotezach, które mamy w kontekście:
    - reguła zamiany (ang. exchange) pozwala zamieniać hipotezy
      miejscami
    - reguła kontrakcji (ang. contraction) pozwala na skopiowanie
      hipotezy
    - reguła osłabiania (ang. weakening) pozwala kasować hipotezy

    W Coqu objawiają się one tak: *)

Lemma structural_rules_test :
  forall P Q R : Prop, (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros P Q R H q p.

  (* reguła kontrakcji - kopiujemy [p] i nazywamy kopię [p'] *)
  pose proof p as p'.

  (* reguła osłabiania - kasujemy [p'] *)
  clear p'.

  (* reguła zamiany - zamieniamy [p] i [q] miejscami *)
  move p after q.

  apply H.
    exact p.
    exact q.
Qed.

(** Jako, że kontekst jest rzeczą absolutnie podstawową przy dowodzeniu
    czegokolwiek, (nie)obecność tych reguł ma absolutnie kluczowy wpływ
    na to, co da się w danej logice udowodnić, a w związku z tym także
    na to, jak możemy daną logikę interpretować.

    Przyjrzyjmy się poniższym twierdzeniom: *)

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
    że kwantowa informacja nie może ot tak sobie pojawiać się ani
    znikać. Bardziej poetycko można powiedzieć, że zachodzi prawo
    zachowania kwantowej informacji. Ponieważ w Coqu udało nam się
    bez problemu udowodnić przeczące im twierdzenia o usuwaniu oraz
    klonowaniu, Coqowa logika nie nadaje się do rozumowania na temat
    kwantowej teorii informacji.

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
    - Wungiel można spalić (wywołując tym sposobem globalne ocieplenie...
      albo i nie - zależy w co kto wierzy), ale nie można go skasować.
    - Podobnie można wungiel wykopać z ziemii, ale nijak nie idzie go
      skopiować, żeby za darmo uzyskać więcej.

    A więc logika liniowa to nie tylko logika kwantowej informacji, ale
    także logika wungla i w ogólności logika zasobów: jej zdania możemy
    interpretować jako zasoby (np. zdanie [P] może oznaczać 5 kilo
    wungla), zaś spójniki jako operacje na zasobach. W szczególności
    liniową implikację [P -> Q] można interpretować jako proces, który
    przekształca zasób [P] w zasób [Q]. Dowody w takim wypadku oznaczają,
    że możliwe jest przekształcenie zasobów reprezentowanych przez
    hipotezy w zasoby reprezentowane przez konkluzję.

    Z deczka odmienne spojrzenie na zasoby ma logika afiniczna: jest
    to logika, w której mamy reguły zamiany i osłabiania, ale nie ma
    reguły kontrakcji. Parafrazując: logika afiniczna wymusza użycie
    każdej hipotezy znajdującej się w kontekście co najwyżej raz.

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
    ten sam plików i zaczną coś do niego zapisywać (dwa użycia uchwytu).
    Logika afiniczna pozwala łatwo rozumować o tego typu sytuacjach i
    dlatego jest ona raczej domeną informatyków niż fizyków kwantowych
    czy filozofów.

    Podobną logiką substrukturalną, która tym razem najbliższa jest
    sercu filozofów, jest logika relewantna. To logika w której mamy
    reguły zamiany i kontrakcji, ale brak reguły osłabiania. W efekcie
    każdej hipotezy znajdującej się w kontekście musimy użyć co najmniej
    raz. Filozofowie (przynajmniej niektórzy) kochają tę logikę, gdyż to
    ograniczenie sprawia, że przesłanki implikacji muszą być relewantne
    dla konkluzji, czyli być z nią jakoś powiązane.

    Typowym przykładem implikacji z irrelewantną przesłanką jest zdanie
    w stylu "jeżeli księżyc jest zrobiony z sera, to 2 + 2 = 4". Zdanie
    to jest prawdziwe w logice konstruktywnej i klasycznej, gdyż jego
    konkluzja, [2 + 2 = 4], jest słuszna (jak w Coqu działają liczby
    naturalne dowiemy się już niedługo!). Jednak tego typu implikacje
    są mocno nieintuicyjne i często sprawiają problem niematematycznym
    osobom, a także studentom pierwszego roku i co po niektórym filzofom
    właśnie. Logika relewantna rozwiązuje "problem", który filozofowie
    mają z takimi zdaniami, gdyż nie można ich w tej logice udowodnić:
    każdej hipotezy musimy użyć co najmniej raz, ale ponieważ hipotezy
    "księżyc jest zrobiony z sera" nie użyliśmy, implikacja nie zachodzi.

    


    
    



*)




(** ** Logiki wielowartościowe *)

(** Innym sposobem klasyfikacji logik jest liczba wartości logicznych,
    które w nich występują. Ponieważ wartości logiczne nie występują
    we wszystkich logikach, a w szczególności nie ma ich w logice
    konstruktywnej, zacznijmy od wytłumaczenia, czym są.

    W skrócie: wartości logiczne mówią, jaki może być "status" danego
    zdania. Dwoma wartościami logicznymi, które występują praktycznie
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
    "nie obchodzi mnie to nic a nic", "brak danych" etc. - każdy może
    sobie wymyślić własną logikę z własną paletą wartości logicznych.

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
    na wygranie partii szachów białymi"), to zdanie [~ Chess] to
    partia szachów, w której maszyna gra czarnymi.

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

    Są też spójniki wyborowe: wyborowa koniunkcja i wyborowa dusjunkcja.
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
    i jeszcze kilka innych, których nie ogarniają nawet najstarsi górale.

    Na koniec jeszcze tylko miłe napomnienie od dobrotliwej babci:
    kontynuuj czytanie niniejszej książki, zamiast gonić za Gruzinem. *)

(** * Logika de Morgana (TODO) *)

(** * Logika modalna *)

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

(** ** Modalność neutralna: nasza ulubiona *)

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

(** ** Modalność trywialna *)

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

(** ** Modalność wymówkowa: pies zjadł mi dowód... :( *)

(** To już ostatnia głupia i bezużyteczna modalność, obiecuję! Wszystkie
    następne będą już praktyczne i przydatne.

    Wyobraźmy sobie następujący dialog, odbywający się na lekcji
    dowodzenia w Coqu w jakiejś zapomnianej przez Boga szkole w
    Pcimiu Dolnym:
    - (N)auczycielka: Jasiu, zrobiłeś zadanie domowe?
    - (J)asiu: tak, psze pani.
    - N: pokaż.
    - J: Hmmm, yhm, uhm, eeee...
    - N: czyli nie zrobiłeś.
    - J: zrobiłem, ale pies mi zjadł.

    Z dialogu jasno wynika, że Jasiu nie zrobił zadania, co jednak nie
    przeszkadza mu w pokrętny sposób twierdzić, że zrobił. Ten pokrętny
    sposób jest powszechnie znany jako "wymówka".

    Słowem kluczowym jest tutaj słowo "sposób", które już na pierwszy
    rzut oka pachnie modalnością. Coś jest na rzeczy, wszakże podanie
    wymówki jest całkiem sprytnym sposobem na uzasadnienie każdego
    zdania:
    - Mam dowód fałszu!
    - Pokaż.
    - Sorry, pies mi zjadł.

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

    Jak można tę modalność zareprezentować formalnie w Coqu? Jeżeli
    [E] jest naszą wymówką, np. "Pies zjadł mi dowód", zaś [P]
    właściwym zdaniem, np. "Pada deszcz", to możemy połączyć je za
    pomocą dysjunkcji, otrzymując [P \/ E], czyli "Pada deszcz lub
    pies zjadł mi dowód". Ze względu na pewne tradycje, modalność
    tę będziemy jednak reprezentować jako [E \/ P], czyli "Pies
    zjadł mi dowód lub pada deszcz". *)

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

(** ** Modalność klasyczna: logika klasyczna jako logika modalna *)

Require Import W3.

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

(** ** Modalność aksjomatyczna *)

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

(** ** Modalność niezaprzeczalna *)

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
      jest zaprzeczalne. Pamiętajmy, że negacja nie jest modalnością.
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

(** ** Modalność pośrednia *)

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

(** ** Modalność wszechpośrednia *)

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
    chmury, ale nawet jeżeli [(deszcz -> mokro) -> mokro <->
    (deszcz -> chmury) -> chmury], to przecież wcale nie oznacza, że
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
    musi [P] (samo w sumie lub na mocy czegoś mocniejszego). Powinno to
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
    spodziewałeś, co?

    Powoli zbliżamy się do końca tego podrozdziału, więc czas
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
    religii. Amerykański filozof Mencjusz Moldbug zauważył (pewnie nie
    jako pierwszy, ale ja dowiedziałem się tego od niego) w swoim poście
    "Dlaczego ateiści wierzą w religię?"
    (https://www.unqualified-reservations.org/2007/04/why-do-atheists-believe-in-religion/),
    że wiara i ogólniej poglądy religijne mają (przynajniej z punktu
    widzenia ateisty) znaczenie jedynie pośrednie, wyrażające się w
    działaniach ludzi je wyznających w rzeczywistym świecie (świat
    bytów nadprzyrodzonych, jak bogowie, anioły, demony etc. uznał
    on za nieistotny).

    Można tego spostrzeżenia użyć na całe multum różnych sposobów. Dla
    przykładu, niektórzy zwolennicy ekumenizmu twierdzą, jakoby
    chrześcijanie i muzułmanie tak naprawdę wierzyli w tego samego Boga.
    Czy tak jest w istocie? Nie, bo ich wiara objawia się w diametralnie
    różny sposób: muzułmanie wysadzają się w powietrze w samobójczych
    zamachach, a chrześcijanie nie. Inne działania = inna wiara, inny
    Bóg.

    TODO: zastanowić się, czy te pierdoły o filozofii religii faktycznie
    są tutaj potrzebne. *)

(** **** Ćwiczenie *)

(** A co, gdyby tak skwantyfikować [E : Prop] i otrzymać w wyniku
    [forall E : Prop, E \/ P]? Zdanie to znaczy coś w stylu "P
    zachodzi albo i nie, wymówkę wybierz wybierz sobie sam". W
    sumie to można by powstały tutaj twór nazwać modalnością
    wszechwymówkową...

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

(** ** Związki między modalnościami *)

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

(** ** Składanie modalności *)

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

(** ** Podsumowanie *)

(** W niniejszy (długaśnym, trzeba przyznać) podrozdziale zapoznaliśmy
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
    ściągę: https://github.com/wkolowski/CoqBookPL/blob/master/txt/modalno%%C5%%9Bci.md *)

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
    to, to nie. Typowy matematyk nie ma bladego pojęcia o logice. Po
    prostu matematycy robią swoje, a tym, co naturalnie im z tego
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

    Poparcie dla pluralizmu logicznego
    jest tutaj uniwersalne i nieświadome. Przyczyną tego jest fakt, że
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

(** * Dziwne aksjomaty i płynące z nich logiki (TODO) *)

Definition ProofIrrelevance : Prop :=
  forall (P : Prop) (p q : P), p = q.

Definition UIP : Prop :=
  forall (A : Type) (x y : A) (p q : x = y), p = q.

Definition K : Prop :=
  forall (A : Type) (x : A) (p : x = x), p = eq_refl x.

Definition PropositionalExtensionality : Prop :=
  forall P Q : Prop, (P <-> Q) -> P = Q.

Lemma UIP_K : UIP -> K.
(* begin hide *)
Proof.
  unfold UIP, K.
  intros UIP A x p.
  apply UIP.
Qed.
(* end hide *)

Lemma K_UIP : K -> UIP.
(* begin hide *)
Proof.
  unfold K, UIP.
  intros K A x y p q.
  destruct p.
  symmetry. apply K.
Qed.
(* end hide *)

(** * Kodowanie impredykatywne (TODO) *)

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
    Wobec tego działanie [try (t; fail)] można podsumować tak: "jeżeli
    [t] rozwiąże cel to użyj jej, a jeżeli nie, to nic nie rób".

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

(** * Jakieś podsumowanie *)

(** Gratulacje! Udało ci się przebrnąć przez pierwszy (poważny) rozdział
    moich wypocin, czyli rozdział o logice. W nagrodę już nigdy nie
    będziesz musiał ręcznie walczyć ze spójnikami czy prawami logiki -
    zrobi to za ciebie taktyka [firstorder]. Jak sama nazwa wskazuje,
    służy ona do radzenia sobie z czysto logicznymi dowodami w logice
    pierwszego rzędu (czyli w takiej, gdzie nie kwantyfikujemy po
    funkcjach albo tympodobnie skomplikowanych rzeczach). *)

(** - taktyka firstorder
    - zrobić test diagnostyczny tak/nie
    - fiszki do nauki nazw praw *)