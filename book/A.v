(** * A: Wstęp *)

(** * Cel *)

(** Celem tego kursu jest zapoznanie czytelnika z kilkoma rzeczami:
    - programowaniem funkcyjnym w duchu Haskella i rodziny ML,
      przeciwstawionym programowaniu imperatywnemu
    - dowodzeniem twierdzeń, które jest:
      - formalne, gdzie "formalny" znaczy "zweryfikowany przez komputer"
      - interaktywne, czyli umożliwiające dowolne wykonywanie i cofanie
        kroków dowodu oraz sprawdzenie jego stanu po każdym kroku
      - (pół)automatyczne, czyli takie, w którym komputer może wyręczyć
        użytkownika w wykonywaniu trywialnych i żmudnych, ale koniecznych
        kroków dowodu
    - matematyką opartą na logice konstruktywnej, teorii typów i teorii
      kategorii oraz na ich zastosowaniach do dowodzenia poprawności
      programów funkcyjnych i w szeroko pojętej informatyce *)

(** W tym krótkim wstępie postaramy się spojrzeć na powyższe cele z
    perspektywy historycznej, a nie dydaktycznej. Nie przejmuj się
    zatem, jeżeli nie rozumiesz jakiegoś pojęcia lub terminu — czas
    na dogłębne wyjaśnienia przyjdzie w kolejnych rozdziałach. *)

(** * Wybór *)

(** Istnieje wiele środków, które pozwoliłyby nam osiągnąć postawione
    cele, a jako że nie sposób poznać ich wszystkich, musimy dokonać
    wyboru.

    Wśród dostępnych języków programowania jest wymieniony już
    Haskell, ale nie pozwala on na dowodzenie twierdzeń (a poza tym jest
    sprzeczny, jeżeli zinterpretujemy go jako system logiczny), a także
    jego silniejsze potomstwo, jak Idris czy Agda, w których możemy
    dowodzić, ale ich wsparcie dla interaktywności oraz automatyzacji
    jest marne.

    Wśród asystentów dowodzenia (ang. proof assistants) mamy do wyboru
    takich zawodników, jak polski system Mizar, który nie jest jednak
    oparty na teorii typów, Lean, który niestety jest jeszcze w fazie
    rozwoju, oraz Coq. Nasz wybór padnie właśnie na ten ostatni język. *)

(** * Programowanie i dowodzenie *)

(** ** Alan Turing i jego maszyna *)

(** Teoretyczna nauka o obliczeniach powstała niedługo przed wynalezieniem
    pierwszych komputerów. Od samego początku definicji obliczalności
    oraz modeli obliczeń było wiele. Choć pokazano później, że wszystkie
    są równoważne, z konkurencji między nimi wyłonił się niekwestionowany
    zwycięzca — maszyna Turinga, wynaleziona przez Alana... (zgadnij
    jak miał na nazwisko).

    Maszyna Turinga nazywa się maszyną nieprzypadkowo — jest mocno
    "hardware'owym" modelem obliczeń. Idea jest dość prosta: maszyna
    ma nieskończenie długą taśmę, przy pomocy której może odczytywać
    i zapisywać symbole oraz manipulować nimi według pewnych reguł.

    W czasach pierwszych komputerów taki "sprzętowy" sposób myślenia
    przeważył i wyznaczył kierunek rozwoju języków programowania,
    który dominuje do dziś. Kierunek ten jest imperatywny; program
    to w jego wyobrażeniu ciąg instrukcji, których rolą jest zmiana
    obecnego stanu pamięci na inny.

    Ten styl programowania sprawdził się w tym sensie, że istnieje na
    świecie cała masa różnych systemów informatycznych zaprogramowanych
    w językach imperatywnych, które jakoś działają... Nie jest on jednak
    doskonały. Wprost przeciwnie — jest:
    - trudny w analizie (trudno przewidzieć, co robi program, jeżeli
      na jego zachowanie wpływ ma cały stan programu)
    - trudny w urównoleglaniu (trudno wykonywać jednocześnie różne
      części programu, jeżeli wszystkie mogą modyfikować wspólny
      globalny stan) *)

(** ** Alonzo Church i rachunek λ *)

(** Innym modelem obliczeń, nieco bardziej abstrakcyjnym czy też
    "software'owym" jest rachunek λ, wymyślony przez Alonzo Churcha.
    Nie stał się tak wpływowy jak maszyny Turinga, mimo że jest równie
    prosty — opiera się jedynie na dwóch operacjach:
    - λ-abstrakcji, czyli związaniu zmiennej wolnej w wyrażeniu, co
      czyni z niego funkcję
    - aplikacji funkcji do argumentu, która jest realizowana przez
      podstawienie argumentu za zmienną związaną *)

(** Nie bój się, jeśli nie rozumiesz; jestem marnym bajkopisarzem i
    postaram się wyjaśnić wszystko później, przy użyciu odpowiednich
    przykładów.

    Oryginalny rachunek λ nie był typowany, tzn. każdą funkcję można
    "wywołać" z każdym argumentem, co może prowadzić do bezsensownych
    pomyłek. Jakiś czas później wymyślono typowany rachunek λ, w którym
    każdy term (wyrażenie) miał swój "typ", czyli metkę, która mówiła,
    jakiego jest rodzaju (liczba, funkcja etc.).

    Następnie odkryto, że przy pomocy typowanego rachunku λ można wyrazić
    intuicjonistyczny rachunek zdań oraz reprezentować dowody przeprowadzone
    przy użyciu dedukcji naturalnej. Tak narodziła się "korespondencja
    Curry'ego-Howarda", która stwierdza między innymi, że pewne systemy
    logiczne odpowiadają pewnym rodzajom typowanego rachunku λ, że
    zdania logiczne odpowiadają typom, a dowody — programom. *)

(** ** Martin-Löf, Coquand, CoC, CIC i Coq *)

(** Kolejnego kroku dokonał Jean-Yves Girard, tworząc System F —
    typowany, polimorficzny rachunek λ, który umożliwia reprezentację
    funkcji generycznych, działających na argumentach dowolnego typu
    w ten sam sposób (przykładem niech będzie funkcja identycznościowa).
    System ten został również odkryty niezależnie przez Johna Reynoldsa.

    Następna gałąź badań, która przyczyniła się do obecnego kształtu
    języka Coq, została zapoczątkowana przez szwedzkiego matematyka
    imieniem Per Martin-Löf. W swojej intuicjonistycznej teorii
    typów (blisko spokrewnionej z rachunkiem λ) wprowadził on pojęcie
    typu zależnego. Typy zależne, jak się okazało, odpowiadają
    intuicjonistycznemu rachunkowi predykatów — i tak korespondencja
    Curry'ego-Howarda rozrastała się...

    Innymi rozszerzeniami typowanego rachunku λ były operatory typów
    (ang. type operators), czyli funkcje biorące i zwracające typy.
    Te trzy ścieżki rozwoju (polimorfizm, operatory typów i typy
    zależne) połączył w rachunku konstrukcji (ang. Calculus of
    Constructions, w skrócie CoC) Thierry Coquand, jeden z twórców
    języka Coq, którego pierwsza wersja była oparta właśnie o rachunek
    konstrukcji.

    Zwieńczeniem tej ścieżki rozwoju były typy induktywne, również
    obecne w teorii typów Martina-Löfa. Połączenie rachunku konstrukcji
    i typów induktywnych dało rachunek induktywnych konstrukcji (ang.
    Calculus of Inductive Constructions, w skrócie CIC), który jest
    obecną podstawą teoretyczną języka Coq (po drobnych rozszerzeniach,
    takich jak dodanie typów koinduktywnych oraz hierarchii uniwersów,
    również pożyczonej od Martina-Löfa). *)

(** * Filozofia i matematyka *)

(** ** Konstruktywizm *)

(** Po co to wszystko, zapytasz? Czy te rzeczy istnieją tylko dlatego, że
    kilku dziwnym ludziom się nudziło? Nie do końca. Przyjrzyjmy się pewnemu
    wesołemu twierdzeniu i jego smutnemu dowodowi.

    Twierdzenie: istnieją takie dwie liczby niewymierne a i b, że a ^ b
    (a podniesione do potęgi b) jest liczbą wymierną.

    Dowód: jeżeli √2 ^ √2 jest niewymierny, to niech a = √2 ^ √2, b = √2.
    Wtedy a ^ b = (√2 ^ √2) ^ √2 = √2 ^ (√2 * √2) = √2 ^ 2 = 2.
    W przeciwnym wypadku (czyli gdy √2 ^ √2 jest wymierny) niech
    a = b = √2. Wtedy a ^ b = √2 ^ √2 jest wymierny na mocy założenia.

    Fajny dowód, co? To teraz dam ci zagadkę: podaj mi dwie niewymierne
    liczby a i b takie, że a ^ b jest wymierne. Pewnie zerkasz teraz do
    dowodu, ale zaraz... cóż to? Jak to możliwe, że ten wredny dowód
    udowadnia istnienie takich liczb, mimo że nie mówi wprost, co to za
    liczby?

    Tym właśnie jest niekonstruktywizm - możesz pokazać, że coś istnieje,
    ale bez wskazywania konkretnego obiektu. Możesz np. pokazać, że równanie
    ma rozwiązanie i wciąż nie wiedzieć, co to za rozwiązanie. Niewesoło,
    prawda?

    Podobnego zdania był dawno temu holenderski matematyk L. E. J. Brouwer.
    Obraził się on więc na tego typu dowody i postanowił zrobić swoją własną
    logikę i oprzeć na niej swoją własną, lepszą matematykę. Powstała w ten
    sposób logika konstruktywna okazała się być mniej więcej tym samym, co
    wspomniany wyżej rachunek lambda, choć Brouwer jeszcze o tym nie
    wiedział. Co ciekawe, Brouwer był przeciwnikiem formalizacji, a jego
    idee sformalizował dopiero jego uczeń, Arend Heyting.

    Ciekawostka: po polsku L. E. J. Brouwer można czytać jako "lej browar". *)

(** ** Praktyka *)

(** W międzyczasie na osiągnięciach wymienionych wyżej panów zaczęto budować
    wieżę z kości słoniowej. Chociaż nigdy nie dosięgnie ona nieba (można
    pokazać, że niektóre problemy są niemożliwe do rozwiązania matematycznie
    ani za pomocą komputerów), to po jakimś czasie zaczęła być przydatna.

    W połowie XIX wieku postawiono problem, który można krótko podsumować
    tak: czy każdą mapę polityczną świata da się pomalować czterema kolorami
    w taki sposób, aby sąsiednie kraje miały inne kolory?

    Przez bardzo długi czas próbowano go rozwiązywać na różne sposoby, ale
    wszystkie one zawodziły. Po ponad stu latach prób problem rozwiązali
    Appel i Haken pokazując, że każdą mapę da się pomalować czterema kolorami.
    Popełnili oni jednak grzech bardzo ciężki, gdyż w swoim dowodzie używali
    komputerów.

    Programy, które napisali, by udowodnić twierdzenie, wiele razy okazały
    się błędne i musiały być wielokrotnie poprawiane. Sprawiło to, że część
    matematyków nie uznała ich dowodu, gdyż nie umieli oni ręcznie sprawdzić
    poprawności wszystkich tych pomocniczych programów.

    Po upływie kolejnych 30 lat dowód udało się sformalizować w Coqu,
    co ostatecznio zamknęło sprawę. Morał płynący z tej historii jest dość
    prosty:
    - niektóre twierdzenia można udowodnić jedynie sprawdzając dużą ilość
      przypadków, co jest trudne dla ludzi
    - można przy dowodzeniu korzystać z komputerów i nie musi to wcale
      podważać wiary w słuszność dowodu, a może ją wręcz wzmocnić *)

(** ** Homofobia... ekhm, homotopia, czyli quo vadimus? *)

(** To jednak nie koniec niebezpiecznych związków matematyków z komputerami.

    Nie tak dawno temu w odległej galaktyce (a konkretniej w Rosji, a potem
    w USA) był sobie matematyk nazwiskiem Voevodsky (czyt. "wojewódzki").
    Zajmował się on takimi dziwnymi rzeczami, jak teoria homotopii czy
    kohomologia motywiczna (nie pytaj co to, bo nawet najstarsi górale
    tego nie wiedzą). Za swoje osiągnięcia w tych dziedzinach otrzymał
    medal Fieldsa, czyli najbardziej prestiżową nagrodę dla matematyków.
    Musiał być więc raczej zdolny.

    Jego historia jest jednak historią popełniania błędu na błędzie błędem
    poprawianym. Dla przykładu, w jednej ze swoich prac popełnił błąd,
    którego znalezienie zajęło 7 lat, a poprawienie - kolejne 6 lat. W
    innym, nieco hardkorowszym przypadku, w jego pracy z 1989 roku inny
    ekspert błąd znalazł w roku 1998, ale Voevodsky nie wierzył, że
    faktycznie jest tam błąd - obu panom po prostu ciężko się było dogadać.
    Ostatecznie Voevodsky o swym błędzie przekonał się dopiero w roku 2013.

    Czy powyższe perypetie świadczą o tym, że Voevodsky jest krętaczem (lub
    po prostu idiotą)? Oczywiście nie. Świadczą one o tym, że matematyka
    uprawiana na wysokim poziomie abstrakcji jest bardzo trudna do ogarnięcia
    przez ludzi. Ludzie, w tym matematycy, mają ograniczoną ilość pamięci
    oraz umiejętności rozumowania, a na dodatek ślepo ufają autorytetom -
    bardzo skomplikowanych i nudnych twierdzeń z dziedzin, którymi mało kto
    się zajmuje, po prostu (prawie) nikt nie sprawdza.

    Powyższe skłoniło Voevodskyego do porzucenia swych dziwnych zainteresowań
    i zajęcia się czymś równie dziwnym (przynajmniej dla matematyków), czyli
    formalną weryfikacją rozumowań matematycznych przez komputery. Po długich
    przemyśleniach związał on swe nadzieje właśnie z Coqiem. Jednak duchy
    przeszłości nie przestawały go nawiedzać i to aż do tego stopnia, że
    wymyślił on (do spółki z takimi ludźmi jak Awodey, Warren czy van den
    Berg) homotopiczną interpretację teorii typów.

    O co chodzi? W skrócie: typy zamiast programów reprezentują przestrzenie,
    zaś programy to punkty w tych przestrzeniach. Programy, które dają takie
    same wyniki są połączone ścieżkami. Programowanie (i robienie matematyki)
    staje się więc w takim układzie niczym innym jak rzeźbieniem figurek w
    bardzo abstrakcyjnych przestrzeniach.

    Jakkolwiek powyższe brzmi dość groźnie, to jest bardzo użyteczne i
    pozwala zarówno załatać różne praktyczne braki teorii typów (np.
    brak typów ilorazowych, cokolwiek to jest) jak i ułatwia czysto
    teoretyczne rozumowania w wielu aspektach.

    Homotopia to przyszłość! *)

(** * Literatura *)

(** ** Książki *)

(** Mimo, iż Coq liczy sobie dobre 27 lat, książek na jego temat zaczęło
    przybywać dopiero od kilku. Z dostępnych pozycji polecenia
    godne są:
    - Software Foundations — trzytomowa seria dostępna za darmo
      tutaj: https://softwarefoundations.cis.upenn.edu/
      W jej skład wchodzą:
      - Logical Foundations, której głównym autorem jest Benjamin
        Pierce — bardzo przystępne acz niekompletne wprowadzenie do
        Coqa. Omawia podstawy programowania funkcyjnego, rekursję i
        indukcję strukturalną, polimorfizm, podstawy logiki i prostą
        automatyzację.
      - Programming Language Foundations, której głównym autorem jest
        Benjamin Pierce — wprowadzenie do teorii języków programowania.
        Omawia definiowanie ich składni i semantyki, dowodzenie ich
        własności oraz podstawy systemów typów i proste optymalizacje.
        Zawiera też kilka rozdziałów na temat bardziej zaawansowanej
        automatyzacji.
      - Verified Functional Algorithms, której autorem jest Andrew
        Appel — jak sama nazwa wskazuje skupia się ona na algorytmach,
        adaptowaniu ich do realiów języków funkcyjnych oraz weryfikacją
        poprawności ich działania. Nie jest ona jeszcze dopracowana, ale
        pewnie zmieni się to w przyszłości.
    - Coq'Art, której autorami są Yves Bertot oraz Pierre Castéran —
      książka nieco szerzej opisująca język Coq, poświęca sporo
      miejsca rachunkowi konstrukcji i aspektom teoretycznym. Zawiera
      także rozdziały dotyczące automatyzacji, silnej specyfikacji,
      koindukcji, zaawansowanej rekurencji i reflekcji. Wersja
      francuska jest dostępna za darmo pod adresem
      https://www.labri.fr/perso/casteran/CoqArt/
      Wersję angielską można za darmo pobrać z rosyjskich stron z
      książkami, ale broń Boże tego nie rób! Piractwo to grzech.
    - Certified Programming with Dependent Types autorstwa Adama
      Chlipali — książka dla zaawansowanych, traktująca o praktycznym
      użyciu typów zależnych oraz kładąca bardzo mocny nacisk na
      automatyzację, dostępna za darmo tu: adam.chlipala.net/cpdt
    - Mathematical Components Book, dostępna za darmo tutaj:
      https://math-comp.github.io/mcb/book.pdf, to książka dotycząca
      biblioteki o nazwie Mathematical Components. Zawiera ona
      wprowadzenia do Coqa, ale poza tym opisuje też dwie inne rzeczy:
      - Metodologię dowodzenia zwaną _small scale reflection_
        (pol. reflekcja na małą skalę), która pozwala wykorzystać
        w dowodach maksimum możliwości obliczeniowych Coqa, a dzięki
        temu uprościć dowody i zorganizować twierdzenia w logiczny
        sposób
      - Język taktyk Ssreflect, którego bazą jest [Ltac], a który
        wprowadza w stosunku do niego wiele ulepszeń i udogodnień,
        umożliwiając między innymi sprawne zastosowanie metodologii
        _small scale reflection_ w praktyce
    - Manual, dostępny pod adresem https://coq.inria.fr/refman/,
      nie jest wprawdzie zbyt przyjazny do czytania ciurkiem, ale
      można tu znaleźć wiele wartościowych informacji. Gdyby ktoś
      jednak pokusił się o przeczytanie go od deski do deski,
      polecam następującą kolejności rozdziałów: 4 -> (5) -> 1 -> 2 ->
      17 -> 29 -> 13 -> 12 -> (3) -> (6) -> 7 -> 8 -> 9 -> 10 -> 21 ->
      22 -> 25 -> 26 -> 27 -> 18 -> 19 -> 20 -> 24 -> 23 -> (11) ->
      (14) -> (15) -> (16) -> (28) -> (30), gdzie nawiasy okrągłe
      oznaczają rozdziały opcjonalne (niezbyt ciekawe lub nieprzydatne)
    - Formal Reasoning About Programs — powstająca książka Adama
      Chlipali. Nie wiem o czym jest i nie polecam czytać dopóki jest
      oznaczona jako draft. Dostępna tu: http://adam.chlipala.net/frap/ *)

(** Zalecana kolejność czytania:
    SF, część 1 -> (Coq'Art) -> (MCB) -> SF, część 2 i 3 -> CPDT ->
    Manual *)

(** ** Blogi *)

(** W Internecie można też dokopać się do blogów, na których przynajmniej
    część postów dotyczy Coqa. Póki co nie miałem czasu wszystkich przeczytać
    i wobec tego większość linków wrzucam w ciemno:
    - http://www.cis.upenn.edu/~aarthur/poleiro/ (znajdziesz tu posty na
      temat parsowania, kombinatorycznej teorii gier, czytelnego
      strukturyzowania dowodu, unikania automatycznego generowania nazw,
      przeszukiwania, algorytmów sortowania oraz dowodzenia przez reflekcję).
    - http://coq-blog.clarus.me/
    - https://gmalecha.github.io/
    - http://seb.mondet.org/blog/index.html (znajdziesz tu 3 posty na temat
      silnych specyfikacji)
    - http://gallium.inria.fr/blog/ (znajdziesz tu posty na temat mechanizmu
      ewaluacji, inwersji, weryfikacji parserów oraz pisania pluginów do Coqa;
      większość materiału jest już dość leciwa)
    - http://ilyasergey.net/pnp/
    - https://homes.cs.washington.edu/~jrw12/##blog
    - http://osa1.net/tags/coq
    - http://coqhott.gforge.inria.fr/blog/ *)

(** ** Inne *)

(** Coq ma też swój subreddit na Reddicie (można tu znaleźć różne rzeczy, w
    tym linki do prac naukowych) oraz tag na StackOverflow, gdzie można
    zadawać i odpowiadać na pytania:
    - https://www.reddit.com/r/Coq/
    - https://stackoverflow.com/questions/tagged/coq *)

(** * Sprawy techniczne *)

(** Kurs ten tworzę z myślą o osobach, które potrafią programować w
    jakimś języku imperatywnym oraz znają podstawy logiki klasycznej,
    ale będę się starał uczynić go jak najbardziej zrozumiałym dla
    każdego. Polecam nie folgować sobie i wykonywać wszystkie ćwiczenia
    w miarę czytania, a cały kod koniecznie przepisywać ręcznie, bez
    kopiowania i wklejania. Poza ćwiczeniami składającymi się z
    pojedynczych twierdzeń powinny się też pojawić miniprojekty, które
    będą polegać na formalizacji jakiejś drobnej teorii lub zastosowaniu
    nabytej wiedzy do rozwiązania jakiegoś typowego problemu.

    Język Coq można pobrać z jego strony domowej: https://coq.inria.fr

    Z tej samej strony można pobrać CoqIDE, darmowe IDE stworzone
    specjalnie dla języka Coq. Wprawdzie z Coqa można korzystać
    w konsoli lub przy użyciu edytora Proof General, zintegrowanego
    z Emacsem, ale w dalszej części tekstu będę zakładał, że użytkownik
    korzysta właśnie z CoqIDE.

    Gdyby ktoś miał problemy z CoqIDE, lekką alternatywą jest ProofWeb:
    http://proofweb.cs.ru.nl/index.html

    Uwaga: kurs powstaje w czasie rzeczywistym, więc w niektórych miejscach
    możesz natknąć się na znacznik TODO, który informuje, że dany fragment
    nie został jeszcze skończony. *)