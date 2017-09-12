(** * R1: Logika *)

(** Naszą przygodę z Coqiem rozpoczniemy od skoku na głęboką wodę,
    czyli nauki dowodzenia twierdzeń w logice konstruktywnej przy
    pomocy taktyk. Powiemy sobie także co nieco o automatyzacji i
    cechach różniących logikę konstruktywną od klasycznej oraz
    dowiemy się, czym jest dedukcja naturalna.

    Coq składa się w zasadzie z trzech języków:
    - język termów nazywa się Gallina. Służy do pisania
      programów oraz podawania twierdzeń
    - język komend nazywa się vernacular ("potoczny"). Służy do
      interakcji z Coqiem, takich jak np. wyszukanie
      wszystkich obiektów związanych z podaną nazwą
    - język taktyk nazywa się Ltac. Służy do dowodzenia twierdzeń. *)

(** * Typy i termy *)

Section constructive_propositional_logic.

(** Mechanizm sekcji nie będzie nas na razie interesował. Użyjemy go,
    żeby nie zaśmiecać głównej przestrzeni nazw. *)

Hypothesis P Q R : Prop.

(** Zapis [x : A] oznacza, że term [x] jest typu [A]. [Prop] to typ zdań
    logicznych, więc komendę tę można odczytać następująco:
    niech [P], [Q] i [R] będą zdaniami logicznymi.

    Czym są termy? Są to twory o naturze syntaktycznej (składniowej),
    reprezentujące funkcje, typy, zdania logiczne, predykaty, relacje
    etc. Polskim słowem o najbliższym znaczeniu jest słowo "wyrażenie".
    Zamiast prób definiowania termów, co byłoby problematyczne,
    zobaczmy przykłady:
    - [2] — stałe są termami
    - [P] — zmienne są termami
    - [Prop] — typy są termami
    - [fun x : nat => x + 2] — λ-abstrakcje (funkcje) są termami
    - [f x] — aplikacje funkcji do argumentu są termami
    - [if true then 5 else 2] — konstrukcja if-then-else jest termem *)

(** Nie są to wszystkie występujące w Coqu rodzaje termów — jest
    ich nieco więcej.

    Kolejnym fundamentalnym pojęciem jest pojęcie typu. W Coqu
    każdy term ma dokładnie jeden, niezmienny typ. Czym są typy?
    Intuicyjnie można powiedzieć, że typ to rodzaj metki, która
    dostarcza nam informacji dotyczących danego termu.

    Dla przykładu,
    stwierdzenie [x : nat] informuje nas, że [x] jest liczbą
    naturalną, dzięki czemu wiemy, że możemy użyć go jako argumentu
    dodawania: term [x + 1] jest poprawnie typowany (ang. well-typed),
    tzn. [x + 1 : nat], a więc możemy skonkludować, że [x + 1] również
    jest liczbą naturalną.

    Innym przykładem niech będzie stwierdzenie [f : nat -> nat],
    które mówi nam, że [f] jest funkcją, która bierze liczbę
    naturalną i zwraca liczbę naturalną. Dzięki temu wiemy, że term
    [f 2] jest poprawnie typowany i jest liczbą naturalną,
    tzn. [f 2 : nat], zaś term [f f] nie jest poprawnie typowany,
    a więc próba jego użycia, a nawet napisania byłaby błędem.

    Typy są tworami absolutnie kluczowymi. Informują nas, z jakimi
    obiektami mamy do czynienia i co możemy z nimi zrobić, a Coq
    pilnuje ścisłego przestrzegania tych reguł. Dzięki temu
    wykluczona zostaje możliwość popełnienia całej gamy różnych
    błędów, które występują w językach nietypowanych, takich jak
    dodanie liczby do ciągu znaków.

    Co więcej, system typów Coqa jest jednym z najsilniejszych,
    jakie dotychczas wymyślono, dzięki czemu umożliwia nam wiele
    rzeczy, których prawie żaden inny język programowania nie potrafi,
    jak np. reprezentowanie skomplikowanych obiektów matematycznych
    i dowodzenie twierdzeń. *)

Check 2.
(* ===> 2 : nat *)

Check P.
(* ===> P : Prop *)

(** Uwaga techniczna: w komentarzach postaci (* ===> *) będę
    przedstawiać wyniki wypisywane przez komendy.

    Typ każdego termu możemy sprawdzić przy pomocy komendy [Check].
    Jest ona nie do przecenienia. Jeżeli nie rozumiesz, co się
    dzieje w trakcie dowodu lub dlaczego Coq nie chce zaakceptować
    jakiejś definicji, użyj komendy [Check], żeby sprawdzić,
    z jakimi typami masz do czynienia. *)

(** * Typy a zbiory *)
(** Z filozoficznego punktu widzenia należy stanowczo odróżnić
    typy od zbiorów, znanych chociażby z teorii zbiorów ZF,
    która jest najpowszechniej używaną podstawą współczesnej
    matematyki:
    - zbiory są materialne, podczas gdy typy są strukturalne.
      Dla przykładu, zbiory {1, 2} oraz {2, 3} mają przecięcie
      równe {2}, które to przecięcie jest podzbiorem każdego
      z nich. W przypadku typów jest inaczej — dwa różne typy
      są zawsze rozłączne i żaden typ nie jest podtypem innego
    - relacja "x ∈ A" jest semantyczna, tzn. jest zdaniem
      logicznym i wymaga dowodu. Relacja "x : A" jest syntaktyczna,
      a więc nie jest zdaniem logicznym i nie wymaga dowodu —
      Coq jest w stanie sprawdzić automatycznie (bez pomocy
      użytkownika), czy dany term jest danego typu, a często
      także wywnioskować z kontekstu, jakiego typu jest dany
      term
    - zbiór to kolekcja obiektów, do której można włożyć cokolwiek.
      Nowe zbiory mogą być formowane ze starych w sposób niemal
      dowolny (aksjomaty są dość liberalne). Typ to kolekcja obiektów
      o takiej samej wewnętrznej naturze. Zasady formowania nowych
      typów ze starych są bardzo ścisłe
    - teoria zbiorów mówi, jakie obiekty istnieją (np. aksjomat
      zbioru potęgowego mówi, że dla każdego zbioru istnieje zbiór
      wszystkich jego podzbiorów). Teoria typów mówi, w jaki sposób
      obiekty mogą być konstruowane — różnica być może ciężko
      dostrzegalna dla niewprawionego oka, ale znaczna. *)

(** * Logika klasyczna i konstruktywna *)
(** Jak udowodnić twierdzenie, by komputer mógł zweryfikować nasz
    dowód? Jedną z metod dowodzenia używanych w logice klasycznej
    są tabelki prawdy. Są one metodą skuteczną, gdyż działają
    zawsze i wszędzie, ale nie są wolne od problemów.

    Pierwszą, praktyczną przeszkodą jest rozmiar tabelek — rośnie on
    wykładniczo wzrast ze wzrostem ilości zmiennych zdaniowych, co
    czyni tę metodę skrajnie niewydajną i obliczeniożerną, a więc
    niepraktyczną dla twierdzeń większych niż zabawkowe.

    Druga przeszkoda, natury filozoficznej, i bardziej fundamentalna
    od pierwszej to poczynione implicite założenie, że każde zdanie
    jest prawdziwe lub fałszywe, co w logice konstruktywnej jest nie
    do końca prawdą, choć w logice klasycznej jest słuszne. Wynika to
    z różnych interpretacji prawdziwości w tych logikach.

    Dowód
    konstruktywny to taki, który polega na skonstruowaniu pewnego
    obiektu i logika konstruktywna dopuszcza jedynie takie dowody.
    Logika klasyczna, mimo że również dopuszcza dowody konstruktywne,
    standardy ma nieco luźniejsze i dopuszcza również dowód polegający
    na pokazaniu, że nieistnienie jakiegoś obiektu jest sprzeczne.
    Jest to sposób dowodzenia fundamentalnie odmienny od poprzedniego,
    gdyż sprzeczność nieistnienia jakiegoś obiektu nie daje nam żadnej
    wskazówki, jak go skonstruować.

    Dobrym przykładem jest poszukiwanie rozwiązań równania: jeżeli
    udowodnimy, że nieistnienie rozwiązania jest sprzeczne, nie
    znaczy to wcale, że znaleźliśmy rozwiązanie. Wiemy tylko, że
    jakieś istnieje, ale nie wiemy, jak je skonstruować. *)

(** * Dedukcja naturalna i taktyki *)
(** Ważną konkluzją płynącą z powyższych rozważań jest fakt, że
    logika konstruktywna ma interpretację obliczeniową — każdy
    dowód można interpretować jako pewien program.
    Odnosząc się do poprzedniego przykładu, konstruktywny dowód
    faktu, że jakieś równanie ma rozwiązanie, jest jednocześnie
    programem, który to rozwiązanie oblicza.

    Wszystko to sprawia, że dużo lepszym, z naszego punktu widzenia,
    stylem dowodzenia będzie _dedukcja naturalna_ — styl oparty na
    małej liczbie aksjomatów, zaś dużej liczbie reguł wnioskowania.
    Reguł, z których każda ma swą własną interpretację obliczeniową,
    dzięki czemu dowodząc przy ich pomocy będziemy jednocześnie
    konstruować pewien program. Sprawdzenie, czy dowód jest poprawny,
    będzie się sprowadzało do sprawdzenia, czy program ten jest
    poprawnie typowany (co Coq może zrobić automatycznie), zaś
    wykonanie tego programu skonstruuje obiekt, który będzie "świadkiem"
    prawdziwości twierdzenia.

    Jako, że każdy dowód jest też programem, w Coqu dowodzić można
    na dwa diametralnie różne sposoby. Pierwszy z nich polega na
    "ręcznym" skonstruowaniu termu, który reprezentuje dowód —
    ten sposób dowodzenia przypomina zwykłe programowanie.

    Drugim sposobem jest użycie taktyk. Ten sposób jest rozszerzeniem
    opisanego powyżej systemu dedukcji naturalnej. Taktyki nie są
    tym samym, co reguły wnioskowania — regułom odpowiadają jedynie
    najprostsze taktyki. Język taktyk Coqa, Ltac, pozwala z prostych
    taktyk budować bardziej skomplikowane przy użyciu konstrukcji
    podobnych do tych, których używa się do pisania "zwykłych"
    programów.

    Taktyki konstruują dowody, czyli programy, jednocześnie same
    będąc programami. Innymi słowy: taktyki to programy, które piszą
    inne programy.

    Ufff... jeżeli twój mózg jeszcze nie eksplodował, to czas
    wziąć się do konkretów! *)

(** * Konstruktywny rachunek zdań *)
(** Nadszedł dobry moment na to, żebyś odpalił CoqIDE. Sesja
    interaktywna w CoqIDE przebiega następująco: edytujemy plik
    z rozszerzeniem .v wpisując komendy. Po kliknięciu przycisku
    "Forward one command" (strzałka w dół) Coq interpretuje kolejną
    komendę, a po kliknięciu "Backward one command" (strzałka w
    górę) cofa się o jedną komendę do tyłu. Ta interaktywność,
    szczególnie w trakcie przeprowadzania dowodu, jest bardzo
    mocnym atutem Coqa — naucz się ją wykorzystywać, dokładnie
    obserwując skutki działania każdej komendy.

    W razie problemów z CoqIDE poszukaj pomocy w manualu:
    coq.inria.fr/refman/Reference-Manual018.html *)

(** ** Implikacja *)
(** Zacznijmy od czegoś prostego: pokażemy, że P implikuje P. *)

Theorem impl_refl : P -> P.
Proof.
  intro dowód_na_to_że_P_zachodzi.
  exact dowód_na_to_że_P_zachodzi.
Qed.

(** Słowo kluczowe [Theorem] obwieszcza, że chcemy podać twierdzenie.
    Musi mieć ono nazwę (tutaj [impl_refl]). Samo twierdzenie podane jest
    po dwukropku — twierdzenie jest typem, a jego udowodnienie sprowadza
    się do skonstruowania termu tego typu. Zauważmy też, że każda
    komenda musi kończyć się kropką.
   
    Twierdzenia powinny mieć łatwe do zapamiętania oraz sensowne nazwy,
    które informują (z grubsza), co właściwie chcemy udowodnić.
    Nazwa [impl_refl] oznacza, że twierdzenie wyraża fakt, że
    implikacja jest zwrotna.

    Dowody będziemy zaczynać komendą [Proof]. Jest ona opcjonalna, ale
    poprawia czytelność, więc warto ją stosować. 

    Jeżeli każesz Coqowi zinterpretować komendę zaczynającą się
    od [Theorem], po prawej stronie ekranu pojawi się stan aktualnie
    przeprowadzanego dowodu.

    Od góry mamy: ilość podcelów (rozwiązanie wszystkich kończy dowód)
    — obecnie 1, kontekst (znajdują się w nim obiekty, które możemy
    wykorzystać w dowodzie) — obecnie mamy w nim zdania
    [P], [Q] i [R]; kreskę oddzielającą kontekst od aktualnego celu,
    obok niej licznik, który informuje nas, nad którym podcelem pracujemy
    — obecnie 1/1, oraz aktualny cel — dopiero zaczynamy, więc brzmi
    tak samo jak nasze twierdzenie.

    Taktyki mogą wprowadzać zmiany w celu lub w kontekście,
    w wyniku czego rozwiązują lub generują nowe podcele. Taktyka może
    zakończyć się sukcesem lub zawieść. Dokładne warunki sukcesu lub
    porażnki zależą od konkretnej taktyki.

    Taktyka [intro] działa na cele będące implikacją [->] i wprowadza
    jedną hipotezę z celu do kontekstu jeżeli to możliwe; w przeciwnym
    przypadku zawodzi. W dowodach słownych lub pisanych na kartce/tablicy
    użyciu taktyki [intro] odpowiadałoby stwierdzenie "załóżmy, że
    P jest prawdą", "załóżmy, że P zachodzi" lub po prostu "załóżmy,
    że P".

    Szczegółem, który odróżnia dowód w Coqu (który dalej będziemy
    zwać "dowodem formalnym") od dowodu na kartce/tablicy/słownie
    (zwanego dalej "dowodem nieformalnym"), jest fakt, że nie tylko
    sama hipoteza,
    ale też dowód ("świadek") jej prawdziwości, musi mieć jakąś
    nazwę — w przeciwnym wypadku nie bylibyśmy w stanie się do
    nich odnosić. Dowodząc na tablicy, możemy odnieść się
    do jej zawartości np. poprzez wskazanie miejsca, w stylu
    "dowód w prawym górnym rogu tablicy". W Coqu wszelkie
    odniesienia działają identycznie jak odniesienia
    do zmiennych w każdym innym języku programowania — przy
    pomocy nazwy.

    Upewnij się też, że dokładnie rozumiesz, co taktyka [intro]
    wprowadziła do kontekstu. Nie było to zdanie [P] — ono już
    się tam znajdowało, o czym świadczyło stwierdzenie [P : Prop]
    — cofnij stan dowodu i sprawdź, jeżeli nie wierzysz. Hipotezą
    wprowadzoną do kontekstu był obiekt, którego nazwę podaliśmy taktyce
    jako argument, tzn. [dowód_na_to_że_P_zachodzi], który jest właśnie
    tym, co głosi jego nazwa — "świadkiem" prawdziwości [P]. Niech
    nie zmyli cię użyte na początku rozdziału słowo kluczowe
    [Hypothesis].

    Taktyka [exact] rozwiązuje cel, jeżeli term podany jako argument
    ma taki sam typ, jak cel, a w przeciwnym przypadku zawodzi.
    Jej użyciu w dowodzie nieformalnym odpowiada stwierdzenie
    "mamy w założeniach dowód na to, że P, który nazywa się x,
    więc x dowodzi tego, że P".

    Pamiętaj, że cel jest zdaniem logicznym, czyli typem, a hipoteza
    jest dowodem tego zdania, czyli termem tego typu. Przyzwyczaj się
    do tego utożsamienia typów i zdań oraz dowodów i programów/termów
    — jest to wspomniana we wstępie korespondencja Curry'ego-Howarda,
    której wiele wcieleń jeszcze zobaczymy.

    Dowód kończy się zazwyczaj komendą [Qed], która go zapisuje. *)

Theorem impl_refl' : P -> P.
Proof.
  intro. assumption.
Qed.

(** Zauważmy, że w Coqowych nazwach można używać apostrofu.
    Zgodnie z konwencją nazwa pokroju [x'] oznacza, że [x']
    jest w jakiś sposób blisko związany z [x]. W tym wypadku
    używamy go, żeby podać inny dowód udowodnionego już
    wcześniej twierdzenia. Nie ma też nic złego w pisaniu
    taktyk w jednej linijce (styl pisania jak zawsze powinien
    maksymalizować czytelność).

    Jeżeli użyjemy taktyki [intro] bez podawania nazwy hipotezy,
    zostanie użyta nazwa domyślna (dla wartości typu [Prop] jest to [H];
    jeżeli ta nazwa jest zajęta, zostanie użyte [H0], [H1]...). Domyślne
    nazwy zazwyczaj nie są dobrym pomysłem, ale w prostych dowodach
    możemy sobie na nie pozwolić.

    Taktyka [assumption] (ang. "założenie") sama potrafi znaleźć
    nazwę hipotezy, która rozwiązuje cel. Jeżeli nie znajdzie
    takiej hipotezy, to zawodzi. Jej użycie w dowodzenie nieformalnym
    odpowiada stwierdzeniu "P zachodzi na mocy założenia". *)

Print impl_refl'.
(* ===> impl_refl' = fun H : P => H
    : P -> P *)

(** Wspomnieliśmy wcześniej, że zdania logiczne są typami,
    a ich dowody termami. Używając komendy [Print] możemy
    wyświetlić definicję podanego termu (nie każdego, ale
    na razie się tym nie przejmuj). Jak się okazuje,
    dowód naszej trywialnej implikacji jest funkcją. Jest
    to kolejny element korespondencji Curry'ego-Howarda.

    Po głębszym namyśle nie powinien nas on dziwić:
    implikację można interpretować wszakże jako funkcję,
    która bierze dowód poprzednika i zwraca dowód następnika.
    Wykonanie funkcji odpowiada tutaj procesowi wywnioskowania
    konkluzji z przesłanki.

    Wspomnieliśmy także, że każda taktyka ma swoją własną
    interpretację obliczeniową. Jaki był więc udział taktyk
    [intro] i [exact] w konstrukcji naszego dowodu? Dowód
    implikacji jest funkcją, więc możemy sobie wyobrazić,
    że na początku dowodu term wyglądał tak: [fun ?1 => ?2]
    (symbole [?1] i [?2] reprezentują fragmenty dowodu, których
    jeszcze nie skonstruowaliśmy). Taktyka [intro] wprowadza
    zmienną do kontekstu i nadaje jej nazwę, czemu odpowiada
    zastąpienie w naszym termie [?1] przez [H : P]. Możemy
    sobie wyobrazić, że po użyciu taktyki intro term wygląda
    tak: [fun H : P => ?2]. Użycie taktyki [exact] (lub
    [assumption]) dało w efekcie zastępienie [?2] przez [H],
    czyli szukany dowód zdania [P]. Ostatecznie term przybrał
    postać [fun H : P => H]. Ponieważ nie ma już żadnych
    brakujących elementów, dowód kończy się. Gdy użyliśmy
    komendy [Qed] Coq zweryfikował, czy aby na pewno term
    skonstruowany przez taktyki jest poprawnie typowany,
    a następnie zaakceptował nasz dowód. *)

Theorem modus_ponens : (P -> Q) -> P -> Q.
Proof.
  intros. apply H. assumption.
Qed.

(** Implikacja jest operatorem łączącym w prawo (ang. right
    associative), więc wyrażenie [(P -> Q) -> P -> Q] to coś
    innego, niż [P -> Q -> P -> Q] — w pierwszym przypadku
    jedna z hipotez jest implikacją

    Wprowadzanie zmiennych do kontekstu pojedynczo może nie być
    dobrym pomysłem, jeżeli jest ich dużo. Taktyka [intros] pozwala
    nam wprowadzić do kontekstu zero lub więcej zmiennych na raz,
    a także kontrolować ich nazwy. Taktyka ta nigdy nie zawodzi.
    Jej odpowiednik w dowodach nieformalnych oraz interpretacja
    obliczeniowa są takie, jak wielokrotnego (lub zerokrotnego)
    użycia taktyki [intro].

    Taktyka [apply] pozwala zaaplikować hipotezę do celu, jeżeli
    hipoteza jest implikacją, której konkluzją jest cel. W wyniku
    działania tej taktyki zostanie wygenerowana ilość podcelów
    równa ilości przesłanek, a stary cel zostanie rozwiązany. W
    kolejnych krokrach będziemy musieli udowodnić, że przesłanki
    są prawdziwe. W naszym przypadku hipotezę [H] typu [P -> Q]
    zaaplikowaliśmy do celu [Q], więc zostanie wygenerowany jeden
    podcel [P].

    Interpretacją obliczeniową taktyki [apply] jest, jak sama
    nazwa wskazuje, aplikacja funkcji. Nie powinno nas to wcale
    dziwić — wszak ustaliliśmy przed chwilą, że implikacje
    są funkcjami. Możemy sobie wyobrazić, że po użyciu
    taktyki [intros] nasz proofterm (będę tego wyrażenia używał
    zamiast rozwlekłego "term będący dowodem") wyglądał tak:
    [fun (H : P -> Q) (H0 : P) => ?1]. Taktyka [apply H]
    przekształca brakujący fragment dowodu [?1] we fragment,
    w którym również czegoś brakuje: [H ?2] — tym czymś jest
    argument. Pasujący argument znaleźliśmy przy pomocy taktyki
    assumption, więc ostatecznie proofterm ma postać
    [fun (H : P -> Q) (H0 : P) => H H0].

    Reguła wnioskowania modus ponens jest zdecydowanie najważniejszą
    (a w wielu systemach logicznych jedyną) regułą wnioskowania.
    To właśnie ona odpowiada za to, że w systemie dedukcji
    naturalnej dowodzimy "od tyłu" — zaczynamy od celu i aplikujemy
    hipotezy, aż dojdziemy do jakiegoś zdania prawdziwego.

    Nadszedł czas na pierwsze ćwiczenia. Zanim przejdziesz dalej,
    postaraj się je wykonać — dzięki temu upewnisz się, że
    zrozumiałeś w wystarczającym stopniu omawiane w tekście
    zagadnienia. Postaraj się nie tylko udowodnić poniższe
    twierdzenia, ale także zrozumieć (a póki zadania są
    proste — być może także przewidzieć), jaki proofterm zostanie
    wygenerowany. Powodzenia! *)

(** **** Ćwiczenie *)
Theorem impl_trans : (P -> Q) -> (Q -> R) -> (P -> R).
(* begin hide *)
Proof.
  intros. apply H0. apply H. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie  *)
Theorem impl_permute : (P -> Q -> R) -> (Q -> P -> R).
(* begin hide *)
Proof.
  intros. apply H.
    assumption.
    assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem impl_dist : (P -> Q -> R) -> ((P -> Q) -> (P -> R)).
(* begin hide *)
Proof.
  intros. apply H.
    assumption.
    apply H0. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie. Udowodnij to twierdzenie bez używania [apply]. *)
Theorem modus_ponens' : (P -> Q) -> P -> Q.
(* begin hide *)
Proof.
   intro. assumption.
Qed.
(* end hide *)

(** ** Fałsz *)

Theorem ex_falso : False -> P.
Proof.
  intro. inversion H.
Qed.

(** [False] to zdanie zawsze fałszywe, którego nie można udowodnić.
    Nie istnieje żaden term tego typu, więc jeżeli taki term znajdzie
    się w naszym kontekście, to znaczy, że uzyskaliśmy sprzeczność.
    Jeżeli użyjemy taktyki [inversion] na hipotezie, która jest typu
    [False], obecny podcel zostanie natychmiast rozwiązany.

    Nazwa [ex_falso] pochodzi od łacińskiego wyrażenia "ex falso
    sequitur quodlibet", które znaczy "z fałszu wynika cokolwiek
    zechcesz".

    Uzasadnienie tej reguły wnioskowania w logice klasycznej jest
    dziecinnie proste: skoro fałsz to prawda, to w tabelce prawdy
    dla tego zdania w kolumnie wynikowej wszystkie zera (fałsz)
    możemy zastąpić jedynkami (prawda), otrzymując zdanie prawdziwe.

    W logice konstruktywnej takie uzasadnienie oczywiście nie
    przejdzie, gdyż ustaliliśmy już, że nie możemy o dowolnym
    zdaniu powiedzieć, że jest albo prawdziwe, albo fałszywe,
    gdyż nie jesteśmy w stanie tak ogólnego faktu udowodnić. Nie
    będziemy na razie uzasadniać tej reguły ani wnikać w szczegóły
    działania taktyki [inversion] — dowiemy się tego już niedługo. *)

(** ** Prawda *)

Theorem truth : True.
Proof.
  trivial.
Qed.

(** [True] to zdanie zawsze prawdziwe. Jego udowodnienie nie jest
    zbyt trudne — możemy to zrobić np. przy pomocy taktyki [trivial],
    która, jak sama nazwa wskazuje, potrafi sama rozwiązywać proste
    cele. *)

Print truth.
(* ===> truth = I : True *)

(** Jeżeli przyjrzymy się skonstruowanemu prooftermowi, dostrzeżemy
    term o nazwie [I]. Jest to jedyny dowód zdania [True]. Jego
    nazwa nie niesie ze sobą żadnego głębszego znaczenia, ale jego
    istnienie jest konieczne — pamiętajmy, że udowodnienie zdania
    sprowadza się do skonstruowania termu odpowiedniego typu.
    Nie inaczej jest w przypadku zdania zawsze prawdziwego — musi
    istnieć jego dowód, a żeby móc się do niego odnosić, musi też
    mieć jakąś nazwę.

    Zdanie [True], w przeciwieństwie do [False], nie jest zbyt
    użyteczne ani często spotykane, ale czasem się przydaje. *)

(** ** Negacja *)

Check ~P.
(* ===> ~ P : Prop *)

(** W Coqu negację zdania [P] oznaczamy przez [~P]. Symbol [~]
    nie jest jednak nazwą negacji — nazwy nie mogą być symbolami.
    Jest to jedynie notacja, która ma uczynić zapis krótszym i
    bardziej podobnym do tego używanego na codzień. Niesie to
    jednak za sobą pewne konsekwencje — nie możemy np. użyć
    komendy [Print ~.], żeby wyświetlić definicję negacji. Jak
    więc poznać nazwę, kryjącą się za jakąś notacją? *)

Locate "~".
(* ===> "~ x" := not x ... *)

(** Możemy to zrobić przy pomocy komendy [Locate]. Wyświetla ona,
    do jakich nazw odwołuje się dana notacja. Negacja w Coqu
    nazywa się [not].

    W logice klasycznej negację zdania P można zinterpretować
    po prostu jako spójnik zdaniowy tworzący nowe zdanie, którego
    wartość logiczna jest przeciwna do wartości zdania P.

    Jeżeli uważnie czytałeś fragmenty dotyczące logiki klasycznej
    i konstruktywnej, dostrzegasz już zapewne, że taka definicja
    nie przejdzie w logice konstruktywnej, której interpretacja
    opiera się na dowodach, a nie wartościach logicznych. Jak więc
    konstruktywnie zdefiniować negację?

    Zauważmy, że jeżeli zdanie [P] ma dowód, to nie powinien istnieć
    żaden dowód jego negacji, [~P]. Uzyskanie takiego dowodu oznaczałoby
    sprzeczność, a więc w szczególności możliwość udowodnienia [False].
    Jak to spostrzeżenie przekłada się na Coqową praktykę? Skoro znamy
    już nazwę negacji, [not], możemy sprawdzić jej definicję: *)

Print not.
(* ===> not = fun A : Prop => A -> False
    : Prop -> Prop *)

(** Definicja negacji w Coqu opiera się właśnie na powyższym spostrzeżeniu:
    jest to funkcja, która bierze zdanie [A], a zwraca zdanie [A -> False],
    które możemy odczytać jako "A prowadzi do sprzeczności". Jeżeli
    nie przekonuje cię to rozumowanie, przyjrzyj się uważnie poniższemu
    twierdzeniu. *)

Theorem P_notP : ~P -> P -> False.
Proof. 
  intros HnotP HP.
  unfold not in HnotP.
  apply HnotP.
  assumption.
Qed.

(** Taktyka [unfold] służy do odwijania definicji. W wyniku jej działania
    nazwa zostanie zastąpiona przez jej definicję, ale tylko w celu.
    Jeżeli podana nazwa do niczego się nie odnosi, taktyka zawiedzie. Aby
    odwinąć definicję w hipotezie, musimy użyć taktyki [unfold nazwa in
    hipoteza], a jeżeli chcemy odwinąć ją wszędzie — [unfold nazwa in] *.

    Twierdzenie to jest też pewnym uzasadnieniem definicji negacji: jest
    ona zdefiniowana tak, aby uzyskanie fałszu z dwóch sprzecznych
    przesłanek było jak najprostsze. *)

Theorem P_notP' : ~P -> P -> 42 = 666.
Proof.
  intros. cut False.
    inversion 1.
    apply H. assumption.
Qed.

(** Taktyką, która czasem przydaje się w dowodzeniu negacji i radzeniu
    sobie z [False], jest [cut]. Jeżeli nasz cel jest postaci [G],
    to taktyka [cut P] rozwiąże go i wygeneruje nam w zamian dwa
    podcele postaci [P -> G] oraz [P]. Nieformalnie odpowiada takiemu
    rozumowaniu: "cel G wynika z P; P zachodzi".

    Udowodnić [False -> 42 = 666] moglibyśmy tak jak poprzednio:
    wprowadzić hipotezę [False] do kontekstu przy pomocy [intro],
    a potem użyć na niej [inversion]. Możemy jednak zrobić to nieco
    szybciej. Jeżeli cel jest implikacją, to taktyka [inversion 1]
    działa tak samo, jak wprowadzenie do kontekstu jednej przesłanki
    i użycie na niej zwykłego [inversion].

    Drugi podcel również moglibyśmy rozwiązać jak poprzednio: odwinąć
    definicję negacji, zaaplikować odpowiednią hipotezę, a potem
    zakończyć przy pomocy [assumption]. Nie musimy jednak wykonywać
    pierwszego z tych kroków — Coq jest w stanie zorientować się,
    że [~P] jest tak naprawdę implikacją, i zaaplikować hipotezę [H]
    bez odwijania definicji negacji. W ten sposób oszczędzamy sobie
    trochę pisania, choć ktoś mógłby argumentować, że zmniejszamy
    czytelność dowodu.

    Uwaga dotycząca stylu kodowania: postaraj się zachować 2 spacje
    wcięcia na każdy poziom zagłębienia, gdzie poziom zagłębienia
    zwiększa się o 1, gdy jakaś taktyka wygeneruje więcej niż 1 podcel.
    Tutaj taktyka [cut] wygenerowała nam 2 podcele, więc dowody
    obydwu zaczniemy od nowej linii po dwóch dodatkowych spacjach.
    Rozwiązanie takie znacznie zwiększa czytelność, szczególnie w
    długich dowodach.

    Interpretacja obliczeniowa negacji wynika wprost z interpretacji
    obliczeniowej implikacji. Konstruktywna negacja różni się od tej
    klasycznej, o czym przekonasz się w ćwiczeniu. *)

(** **** Ćwiczenie *)
Theorem not_False : ~False.
(* begin hide *)
Proof.
  intro. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem not_True : ~True -> False.
(* begin hide *)
Proof.
  intro. apply H. trivial.
Qed.
(* end hide *)

(** **** Ćwiczenie. Czy odwrotna implikacja również zachodzi? *)
Theorem dbl_neg_intro : P -> ~~P.
(* begin hide *)
Proof.
  unfold not. intros. apply H0. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie. Czym to twierdzenie różni się od poprzedniego? *)
Theorem triple_neg_rev : ~~~P -> ~P.
(* begin hide *)
Proof.
  unfold not. intros. apply H. intro. apply H1. assumption.
Qed.
(* end hide *)

(** ** Koniunkcja *)

Theorem and_intro : P -> Q -> P /\ Q.
Proof.
  intros. split.
    assumption.
    assumption.
Qed.

(** Symbol [/\] oznacza koniunkcję dwóch zdań logicznych i podobnie
    jak [~] jest jedynie notacją (koniunkcja w Coqu nazywa się [and]).

    W logice
    klasycznej koniunkcja jest prawdziwa, gdy obydwa jej człony są
    prawdziwe. W logice konstruktywnej sytuacja jest analogiczna, choć
    subtelnie różna: aby udowodnić koniunkcję, musimy udowodnić każdy
    z jej dwóch członów osobno.

    Koniunkcji w Coqu dowodzimy przy pomocy taktyki [split]. Jako że
    musimy udowodnić oddzielnie oba jej człony, zostały dla nas
    wygenerowane dwa nowe podcele — jeden dla lewego członu, a drugi
    dla prawego. Ponieważ stary cel został rozwiązany, to do udowodnienia
    pozostają nam tylko te dwa nowe podcele. *)

Theorem and_proj1 : P /\ Q -> P.
Proof.
  intro H. destruct H. assumption.
Qed.

(** Aby udowodnić koniunkcję, użyliśmy taktyki [split], która rozbiła
    ją na dwa osobne podcele. Jeżeli koniunkcją jest jedną z naszych
    hipotez, możemy posłużyć się podobnie działającą taktyką
    [destruct], która dowód koniunkcji rozbija na osobne dowody obu
    jej członów. W naszym przypadku hipoteza [H : P /\ Q] zostaje
    rozbita na hipotezy [H : P] oraz [H0 : Q]. Zauważ, że nowe hipotezy
    dostały nowe, domyślne nazwy. *)

Theorem and_proj1' : P /\ Q -> P.
Proof.
  intro HPQ. destruct HPQ as [HP HQ]. assumption.
Qed.

(** Podobnie jak w przypadku taktyki [intro], domyślne nazwy nadawane
    przez taktykę [destruct] często nie są zbyt fortunne. Żeby nadać
    częściom składowym rozbijanej hipotezy nowe nazwy, możemy użyć
    tej taktyki ze składnią [destruct nazwa as wzorzec]. Ponieważ
    koniunkcja składa się z dwóch członów, [wzorzec] będzie miał
    postać [[nazwa1 nazwa2]].

    Interpretacja obliczeniowa koniunkcji jest bardzo prosta:
    koniunkcja to uporządkowana para zdań, zaś dowód koniunkcji
    to uporządkowana para dowodów — pierwszy jej element dowodzi
    pierwszego członu koniunkcji, a drugi element — drugiego
    członu koniunkcji. *)

(** **** Ćwiczenie *)
Theorem and_proj2 : P /\ Q -> Q.
(* begin hide *)
Proof.
  intro. destruct H. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem and3_intro : P -> Q -> R -> P /\ Q /\ R.
(* begin hide *)
Proof.
  intros. split. assumption. split. assumption. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem and3_proj : P /\ Q /\ R -> Q.
(* begin hide *)
Proof.
  intro. destruct H. destruct H0. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem noncontradiction : ~(P /\ ~P).
(* begin hide *)
Proof.
  intro. destruct H. apply H0. assumption.
Qed.
(* end hide *)

(** ** Równoważność zdaniowa *)

(** Równoważność zdaniowa jest w Coqu oznaczana [<->]. Symbol ten,
    jak (prawie) każdy jest jedynie notacją — równoważność
    nazywa się [iff]. *)

Print iff.
(* ===> fun A B : Prop => (A -> B) /\ (B -> A)
    : Prop -> Prop -> Prop *)

(** Jak widać, równoważność [P <-> Q] to koniunkcja dwóch implikacji
    [P -> Q] oraz [Q -> P]. W związku z tym nie powinno nas dziwić,
    że pracuje się z nią tak samo jak z koniunkcją. Tak jak nie
    musieliśmy odwijać definicji negacji, żeby zaaplikować ją jak
    rasową impikcję, tak też nie musimy odwijać definicji równoważności,
    żeby posługiwać się nią jak prawdziwą koniunkcją. Jej interpretacja
    obliczeniowa wywodzi się z interpretacji obliczeniowej koniunkcji
    oraz implikacji. *)

Theorem iff_intro : (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof.
  intros. split.
    intro. apply H. assumption.
    intro. apply H0. assumption.
Qed.

(** Do rozbijania równoważności będących celem służy, tak jak w
    przypadku koniunkcji, taktyka [split]. *)

Theorem iff_proj1 : (P <-> Q) -> (P -> Q).
Proof.
  intros. destruct H as [HPQ HQP].
  apply HPQ. assumption.
Qed.

(** Równoważnosć znajdującą się w kontekście możemy zaś, tak jak
    koniunkcje, rozbijać taktyką [destruct]. Taką samą postać ma
    również wzorzec, służący w klauzuli [as] do nadawania nazw
    zmiennym. *)

(** **** Ćwiczenie *)
Theorem iff_refl : P <-> P.
(* begin hide *)
Proof.
  split.
    intro. assumption.
    intro. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem iff_symm : (P <-> Q) -> (Q <-> P).
(* begin hide *)
Proof.
  intro. destruct H. split.
    intro. apply H0. assumption.
    intro. apply H. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem iff_trans: (P <-> Q) -> (Q <-> R) -> (P <-> R).
(* begin hide *)
Proof.
  intros. destruct H, H0. split.
    intro. apply H0. apply H. assumption.
    intro. apply H1. apply H2. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem iff_not : (P <-> Q) -> (~P <-> ~Q).
(* begin hide *)
Proof.
  intro. destruct H as [HPQ HQP]. split.
    intro. intro. apply H. apply HQP. assumption.
    intro. intro. apply H. apply HPQ. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem curry_uncurry : (P -> Q -> R) <-> (P /\ Q -> R).
(* begin hide *)
Proof.
  split.
    intros. destruct H0. apply H.
      assumption.
      assumption.
    intros. apply H. split.
      assumption.
      assumption.
Qed.
(* end hide *)

(** ** Alternatywa *)

Theorem or_left : P -> P \/ Q.
Proof.
  intro. left. assumption.
Qed.

(** Symbol [\/] oznacza alternatywę (zwaną też czasem dysjunkcją)
    dwóch zdań logicznych. Żeby dowieść alternatywy [P \/ Q],
    musimy udowonić albo lewy, albo prawy jej człon. Taktyki [left]
    oraz [right] pozwalają nam wybrać, którego z nich chcemy dowodzić. *)

Theorem or_comm_impl : P \/ Q -> Q \/ P.
Proof.
  intro. destruct H as [p | q].
    right. assumption.
    left. assumption.
Qed.

(** Zauważmy, że użycie taktyki destruct zmieniło nam ilość celów.
    Wynika to z faktu, że nie wiemy, który człon hipotezy [P \/ Q] jest
    prawdziwy, więc dla każdego przypadku musimy przeprowadzić osobny
    dowód. Inaczej wygląda też wzorzec służący do rozbicia tej
    hipotezy — w przypadku alternatywy ma on postać [[nazwa1 | nazwa2]].

    Interpretacja obliczeniowa alternatywy jest następująca: jest to
    suma rozłączna dwóch zdań. Dowód alternatywy to dowód jednego z jej
    członów z dodatkową informacją o tym, który to człon.

    To ostatnie stwierdzenie odróżnia alternatywę konstruktywną od
    klasycznej: klasyczna alternatywa to stwierdzenie "któres z tych
    dwóch zdań jest prawdziwe (lub oba)", zaś konstruktywna to
    stwierdzenie "lewy człon jest prawdziwy albo prawy człon jest
    prawdziwy (albo oba, ale i tak dowodzimy tylko jednego)". Jest
    to znaczna różnica — w przypadku logiki klasycznej nie wiemy,
    który człon jest prawdziwy. *)

(** **** Ćwiczenie *)
Theorem or_right : Q -> P \/ Q.
(* begin hide *)
Proof.
  intro. right. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem or_big : Q -> P \/ Q \/ R.
(* begin hide *)
Proof.
  intro. right. left. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem or3_comm_impl : P \/ Q \/ R -> R \/ Q \/ P.
(* begin hide *)
Proof.
  intro. destruct H. right. right. assumption.
  destruct H. right. left. assumption. left. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie. Czy odwrotna implikacja również zachodzi? *)
Theorem or_impl : ~P \/ Q -> (P -> Q).
(* begin hide *)
Proof.
  intros. destruct H.
    cut False.
      inversion 1.
      apply H. assumption.
    assumption.
Qed.
(* end hide *)

(** * Konstruktywny rachunek predykatów *)

End constructive_propositional_logic.

(** Komenda [End] zamyka sekcję, którą otworzyliśmy na samym początku
    tego rozdziału. Zdania [P], [Q] i [R] znikają z
    dostępnej dla nas przestrzeni nazw, dzięki czemu uniknęliśmy jej
    zaśmiecenia. Nasze twierdzenia wciąż są jednak dostępne (sprawdź
    to).

    Zajmiemy się teraz konstruktywnym rachunkiem predykatów. Jest on
    rozszerzeniem omawianego poprzednio konstruktywnego rachunku zdań
    o predykaty oraz kwantyfikatory, które pozwolą
    nam wyrażać takie zależności jak "każdy" oraz "istnieje". Predykaty
    możemy interpretować jako "właściwości obiektów". *)

(** ** Kwantyfikacja uniwersalna *)

(** Zobaczmy o co chodzi na znanym nam już przykładzie zrotności
    implikacji: *)

Theorem impl_refl'' : forall P : Prop, P -> P.
Proof.
  intros. assumption.
Qed.

(** [forall] oznacza kwantyfikację uniwersalną. Możemy ten symbol
    odczytywać "dla każdego". Zasięg kwantyfikatora rozciąga się
    od przecinka aż do kropki. Wobec tego treść naszego twierdzenia
    możemy odczytać "dla każdego zdania logicznego P, P implikuje P".

    Kwantyfikator uniwersalny jest w swej naturze bardzo podobny do
    implikacji — zmienne, których dotyczy, możemy wprowadzić do
    kontekstu przy pomocy taktyki [intro]. W dowodzie nieforamlnym
    użyciu taktyki [intro P] na celu kwantyfikowanym uniwersalnie
    odpowiadałoby stwierdzenie "niech P będzie dowolnym zdaniem logicznym".

    Zauważ, że używając taktyki [intros], możemy wprowadzić do kontekstu
    jednocześnie zmienne kwantyfikowane uniwersalnie oraz przesłanki
    występujące po lewej stronie implikacji. To wszystko powinno nasunąć
    nam myśl, że kwantyfikacja uniwersalna i implikacja są ze sobą blisko
    związane. *)

Print impl_refl''.
(* ===> impl_refl'' = fun (P : Prop) (H : P) => H
    : forall P : Prop, P -> P *)

(** Rzeczywiście: dowodem naszego zdania jest coś, co na pierwszy rzut
    oka wygląda jak funkcja. Jeżeli jednak przyjrzysz się jej uważnie,
    dostrzeżesz że nie może być to zwykła funkcja — typ zwracanej
    wartości [H] różni się w zależności od argumentu [P]. Jeżeli
    za [P] wstawimy [1 = 1], to [H] będzie dowodem na to, że
    [1 = 1]. Jeżeli za [P] wstawimy [2 = 2], to [H] będzie dowodem
    na to, że [2 = 2]. Zauważ, że [1 = 1] oraz [2 = 2] to dwa różne
    zdania, a zatem są to także różne typy.

    Dowód naszego zdania nie może być zatem zwykłą funkcją — gdyby
    nią był, zawsze zwracałby wartości tego samego typu. Jest on
    funkcją zależną, czyli taką, której przeciwdziedzina zależy
    od dziedziny. Funkcja zależna dla każdego argumentu może
    zwracać wartości różnego typu.

    Ustaliliśmy więc, że kwantyfikacja uniwersalna jest pewnym
    uogólnieniem implikacji, zaś jej interpretacją obliczeniową
    jest funkcja zależna, czyli pewne uogólnienie zwykłej funkcji,
    która jest interpretacją obliczeniową implikacji. *)

Theorem general_to_particular : forall P : nat -> Prop,
    (forall n : nat, P n) -> P 42.
Proof.
  intros. apply H.
Restart.
  intros. specialize (H 42). assumption.
Qed.

(** Podobnie jak zwykłe funkcje, funkcje zależne możemy aplikować
    do celu za pomocą taktyki [apply]. Możliwy jest też inny
    sposób rozumowania, nieco bardziej przypominający rozumowania
    "w przód": przy pomocy taktyki [specialize] możemy zainstancjować
    [n] w naszej hipotezie [H], podając jej pewną liczbę naturalną.
    Wtedy nasza hipoteza [H] z ogólnej, z kwantyfikacją po wszystkich
    liczbach naturalnych, zmieni się w szczególną, dotyczącą tylko
    podanej przez nas liczby.

    Komenda [Restart] pozwala nam zacząć dowód od nowa w dowolnym
    jego momencie. Jej użycie nie jest wymagane, by ukończyć
    powyższy dowód — spróbuj wstawić w jej miejsce [Qed]. *)

Theorem and_proj1'' : forall (P Q : nat -> Prop),
    (forall n : nat, P n /\ Q n) -> (forall n : nat, P n).
Proof.
  intros P Q H k. destruct (H k). assumption.
Qed.

(** W powyższym przykładzie próba użycia taktyki [destruct] na
    hipotezie [H] zawiodłaby — [H] nie jest produktem. Żeby
    rozbić tę hipotezę, musielibyśmy najpierw wyspecjalizować
    ją dla interesującego nas [k], a dopiero potem rozbić.
    Możemy jednak zrobić to w nieco krótszy sposób — pisząc
    [destruct (H k)]. Dzięki temu "w locie" przemienimy [H]
    z hipotezy ogólnej w szczególną, dotycząca tylko [k], a
    potem rozbijemy. Podobnie poprzednie twierdzenie moglibyśmy
    udowodnić szybciej, jeżeli zamiast [specialize] i [assumption]
    napisalibyśmy [destruct (H 42)]. *)

(** **** Ćwiczenie *)
Theorem all_dist : forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x /\ Q x) <->
    (forall x : A, P x) /\ (forall x : A, Q x).
(* begin hide *)
Proof.
  split.
    intros. split.
      intro. destruct (H x). assumption.
      intro. destruct (H x). assumption.
    intros. destruct H. split.
      apply H.
      apply H0.
Restart.
  split; intros.
    split; intros; destruct (H x); assumption.
    destruct H. split; try apply H; apply H0.
Qed.
(* end hide *)

(** ** Kwantyfikacja egzystencjalna *)

(** Zdania egzystencjalne to zdania postaci "istnieje obiekt x,
    który ma właściwość P". W Coqu prezentują się tak: *)

Theorem ex_example1 : exists n : nat, n = 0.
Proof.
  exists 0. trivial.
Qed.

(** Kwantyfikacja egzystencjalna jest w Coqu zapisywana jako [exists]
    (exists). Aby udowodnić zdanie kwantyfikowane egzystencjalnie, musimy
    skonstruować obiekt, którego istnienie postulujemy, oraz
    udowodnić, że ma deklarowaną właściwość. Jest to wymóg dużo
    bardziej restrykcyjny niż w logice klasycznej, gdzie możemy
    zadowolić się stwierdzeniem, że nieistnienie takiego obiektu
    jest sprzeczne.

    Powyższe twierdzenie możemy odczytać "istnieje liczba naturalna,
    która jest równa 0". W dowodzenie nieformalnym użyciu taktyki
    [exists] odpowiada stwierdzenie: "liczbą posiadającą tę właściwość
    jest 0". Następnie pozostaje nam udowodnić, iż rzeczywiście [0 = 0],
    co jest trywialne. *)

Theorem ex_example2 : ~ exists n : nat, 0 = S n.
Proof.
  intro. destruct H as [n H]. inversion H.
Qed.

(** Gdy zdanie kwantyfikowane egzystencjalnie znajdzie się w naszych
    założeniach, możemy je rozbić i uzyskać wspomniany w nim obiekt
    oraz dowód wspominianej właściwości. Nie powinno nas to dziwić —
    skoro zakładamy, że zdanie to jest prawdziwe, to musiało zostać
    ono udowodnione w sposób opisany powyżej — właśnie poprzez wskazanie
    obiektu i udowodnienia, że ma daną własność.

    Myślę, że dostrzegasz już pewną prawidłowość:
    - udowodnienie koniunkcji wymaga udowodnienia obydwu członów z osobna,
      więc dowód koniunkcji można rozbić na dowody poszczególnych członów
      (podobna sytuacja zachodzi w przypadku równoważności)
    - udowodnienie alternatywy wymaga udowodnienia któregoś z członów, więc
      dowód alternatywy można rozbić, uzyskując dwa osobne podcele, a w
      każdym z nich dowód jednego z członów tej alternatywy
    - udowodnienie zdania egzystencjalnego wymaga wskazania obiektu i
      podania dowodu żądanej własności, więc dowód takiego zdania
      możemy rozbić, uzyskując ten obiekt i dowód jego własności *)

(** Takie konstruowanie i dekonstruowanie dowodów (i innych termów)
    będzie naszym chlebem powszednim w logice konstruktywnej i w Coqu.
    Wynika ono z samej natury konstrukcji: zasady konstruowania termów
    danego typu są ściśle określone, więc możemy dokonywać dekonstrukcji,
    która polega po prostu na sprawdzeniu, jakimi zasadami posłużono się
    w konstrukcji. Nie przejmuj się, jeżeli wydaje ci się to nie do końca
    jasne — więcej dowiesz się już w kolejnym rozdziale.

    Ostatnią wartą omówienia sprawą jest interpretacja obliczeniowa
    kwantyfikacji egzystencjalnej. Jest nią para zależna, tzn. taka,
    w której typ drugiego elementu może zależeć od pierwszego — pierwszym
    elementem pary jest obiekt, a drugim dowód, że ma on pewną własność.
    Zauważ, że podstawiając [0] do [exists n : nat, n = 0], otrzymamy
    zdanie [0 = 0], które jest innym zdaniem, niż [1 = 0] (choćby dlatego,
    że pierwsze jest prawdziwe, a drugie nie). Interpretacją obliczeniową
    taktyki [exists] jest wobec tego podanie pierwszego elementu pary,
    a podanie drugiego to po prostu przeprowadzenie reszty dowodu.

    "Zależność" jest tutaj tego samego rodzaju, co w przypadku produktu
    zależnego — tam typ wyniku mógł być różny w zależność od wartości,
    jaką funkcja bierze na wejściu, a w przypadku sumy zależnej typ
    drugiego elementu może być różny w zależności od tego, jaki jest
    pierwszy element.

    Nie daj się zwieść niefortunnemu nazewnictwu: produkt zależny
    [forall x : A, B], którego elementami są funkcje zależne,
    jest uogólnieniem typu funkcyjnego [A -> B], którego elementami
    są zwykłe funkcje, zaś suma zależna [exists x : A, B], której
    elementami są pary zależne, jest uogólnieniem produktu [A * B],
    którego elementami są zwykłe pary. *)

(** **** Ćwiczenie *)
Theorem ex_or_dist : forall (A : Type) (P Q : A -> Prop),
    (exists x : A, P x \/ Q x) <->
    (exists x : A, P x) \/ (exists x : A, Q x).
(* begin hide *)
Proof.
  split.
    intros. destruct H as [x [HP | HQ]].
      left. exists x. assumption.
      right. exists x. assumption.
    intros. destruct H as [[x HP] | [x HQ]].
      exists x. left. assumption.
      exists x. right. assumption.
Qed.
(* end hide *)

(** * Kombinatory taktyk *)

(** Przyjrzyjmy się jeszcze raz twierdzeniu [iff_intro] (lekko
    zmodernizowanemu przy pomocy kwantyfikacji uniwersalnej). *)

Theorem iff_intro' : forall P Q : Prop, (P -> Q) -> (Q -> P) -> (P <-> Q).
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

Theorem iff_intro'' : forall P Q : Prop, (P -> Q) -> (Q -> P) -> (P <-> Q).
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

(** Następujące ćwiczenia rozwiąż najpierw najpierw z jak największym
    zrozumieniem, a następnie zautomatyzuj tak, aby całość była
    rozwiązywana w jednym kroku przez pojedynczą (złożoną) taktykę. *)

(** **** Ćwiczenie *)
Theorem or_comm_ex : forall P Q : Prop, P \/ Q -> Q \/ P.
(* begin hide *)
Proof.
  intros; destruct H; [right | left]; assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)
Theorem diamond : forall P Q R S : Prop,
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

Theorem iff_intro''' : forall P Q : Prop, (P -> Q) -> (Q -> P) -> (P <-> Q).
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

Theorem idtac_do_example : forall P Q R S : Prop, P -> S \/ R \/ Q \/ P.
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
    przy wyborze członu alternatywy, którego chcemy dowodzić,
    trzykrotnie pójdziemy w prawo. Zauważmy, że taktyka [do 4 right]
    zawiodłaby, gdyż po 3 użyciach [right] cel nie byłby już
    alternatywą, więc kolejne użycie [right] zawiodłoby, a wtedy
    cała taktyka [do 4 right] również zawiodłaby. *)

Theorem repeat_example : forall P A B C D E F : Prop,
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
    członu alternatywy wybieramy człon będący najbardziej na prawo,
    tzn. dopóki cel jest alternatywą, aplikowana jest taktyka [right],
    która wybiera prawy człon. Kiedy nasz cel przestaje być alternatywą,
    taktyka [right] zawodzi i wtedy taktyka [repeat right] kończy swoje
    działanie sukcesem. *)

(** ** [try] i [fail] *)

Theorem iff_intro4 : forall P Q : Prop, (P -> Q) -> (Q -> P) -> (P <-> Q).
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
    https://coq.inria.fr/refman/tactic-index.html *)

(** * Zadania (beta) *)
(** Uwaga: niektóre zadania mogą pokrywać się z ćwiczeniami, które
    występują w tekście.
    Uwaga TODO: dodać ćwiczenia do sekcji Kombinatory taktyk. *)

(** ** Konstruktywny rachunek zdań *)

Section exercises_propositional.
Hypotheses P Q R S : Prop.

(** Komenda [Hypotheses] formalnie działa jak wprowadzenie aksjomatu,
    który w naszym przypadku brzmi "P, Q, R i S są zdaniami logicznymi".
    Taki aksjomat jest rzecz jasna zupełnie niegroźny, ale z innymi
    trzeba uważać — gdybyśmy wprowadzili aksjomat [1 = 2], to
    popadlibyśmy w sprzeczność i nie moglibyśmy ufać żadnym dowodom,
    które przeprowadzamy. *)

(* begin hide *)
Ltac search := unfold not; intros; match goal with
    | H : _ /\ _ |- _ => destruct H; search
    | H : _ \/ _ |- _ => destruct H; search
    | |- _ /\ _ => split; search
    | |- _ <-> _ => split; search
    | |- _ \/ _ => left; search || right; search
    | _ => eauto; fail
end.
(* end hide *)

(* Przemienność *)
Theorem and_comm : P /\ Q -> Q /\ P.
(* begin hide *)
Proof.
  destruct 1; split; assumption.
Restart.
  search.
Qed.
(* end hide *)

Theorem or_comm : P \/ Q -> Q \/ P.
(* begin hide *)
Proof.
  destruct 1; [right | left]; assumption.
Qed.
(* end hide *)

(* Łączność *)
Theorem and_assoc : P /\ (Q /\ R) <-> (P /\ Q) /\ R.
(* begin hide *)
Proof.
  split; intros.
    destruct H as [p [q r]]. repeat split; assumption.
    destruct H as [[p q] r]. repeat split; assumption.
Restart.
  split; intros; repeat
  match goal with
      | H : _ /\ _ |- _ => destruct H
  end; repeat split; assumption.
Restart.
  search.
Qed.
(* end hide *)

Theorem or_assoc : P \/ (Q \/ R) <-> (P \/ Q) \/ R.
(* begin hide *)
Proof.
  split; intros.
    destruct H as [p | [q | r]].
      left. left. assumption.
      left. right. assumption.
      right. assumption.
    destruct H as [[p | q] | r].
      left. assumption.
      right. left. assumption.
      right. right. assumption.
Restart.
  search.
Qed.
(* end hide *)

(* Rozdzielność *)
Theorem and_dist_or : P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
(* begin hide *)
Proof.
  split; intros.
    destruct H as [p [q | r]].
      left. split; assumption.
      right. split; assumption.
    destruct H as [[p q] | [p r]].
      split. assumption. left. assumption.
      split. assumption. right. assumption.
Restart.
  search.
Qed.
(* end hide *)

(* begin hide *)
Ltac leftright t := ((left; t) || (right; t)).
(* end hide *)

Theorem or_dist_and : P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
(* begin hide *)
Proof.
  split; intros.
    destruct H as [p | [q r]].
      split; left; assumption.
      split; right; assumption.
    destruct H as [[p1 | q] [p2 | r]].
      left. assumption.
      left. assumption.
      left. assumption.
      right. split; assumption.
Restart.
  split; intros.
    destruct H as [p | [q r]];
      split; ((left; assumption) || (right; assumption)).
    destruct H as [[p1 | q] [p2 | r]];
      ((left; assumption) || (right; split; assumption)).
Restart.
  split; intros.
    destruct H as [p | [q r]];
      split; leftright assumption.
    destruct H as [[p1 | q] [p2 | r]];
      leftright ltac:(try split; assumption).
Restart.
  search.
Qed.
(* end hide *)

Theorem imp_dist_imp : (P -> Q -> R) <-> ((P -> Q) -> (P -> R)).
(* begin hide *)
Proof.
  split; intros.
    apply H.
      assumption.
      apply H0. assumption.
    apply H.
      intro. assumption.
      assumption.
Restart.
  split; intros; apply H; intros; try apply H0; assumption.
Restart.
  search.
Qed.
(* end hide *)

(* Kuryfikacja *)
Theorem curry : (P /\ Q -> R) -> (P -> Q -> R).
(* begin hide *)
Proof.
  intros; apply H; split; assumption.
Restart.
  search.
Qed.
(* end hide *)

Theorem uncurry : (P -> Q -> R) -> (P /\ Q -> R).
(* begin hide *)
Abort.
(* end hide *)

(* De Morgan *)
Theorem deMorgan_1 : ~(P \/ Q) <-> ~P /\ ~Q.
(* begin hide *)
Abort.
(* end hide *)

Theorem deMorgan_2 : ~P \/ ~Q -> ~(P /\ Q).
(* begin hide *)
Abort.
(* end hide *)

(* Niesprzeczność i zasada wyłączonego środka *)
Theorem noncontradiction' : ~(P /\ ~P).
(* begin hide *)
Proof.
  unfold not; intros. destruct H. apply H0. assumption.
Restart.
  search.
Qed.
(* end hide *)

Theorem noncontradiction_v2 : ~(P <-> ~P).
(* begin hide *)
Abort.
(* end hide *)

Theorem em_irrefutable : ~~(P \/ ~P).
(* begin hide *)
Abort.
(* end hide *)

(* Elementy neutralne i anihilujące *)
Theorem and_false_annihilation : P /\ False <-> False.
(* begin hide *)
Abort.
(* end hide *)

Theorem or_false_neutral : P \/ False <-> P.
(* begin hide *)
Abort.
(* end hide *)

Theorem and_true_neutral : P /\ True <-> P.
(* begin hide *)
Abort.
(* end hide *)

Theorem or_true_annihilation : P \/ True <-> True.
(* begin hide *)
Abort.
(* end hide *)

(* Różne *)
Theorem or_imp_and : (P \/ Q -> R) <-> (P -> R) /\ (Q -> R).
(* begin hide *)
Abort.
(* end hide *)

Theorem and_not_imp : P /\ ~Q -> ~(P -> Q).
(* begin hide *)
Abort.
(* end hide *)

Theorem or_not_imp : ~P \/ Q -> (P -> Q).
(* begin hide *)
Abort.
(* end hide *)

Theorem contraposition : (P -> Q) -> (~Q -> ~P).
(* begin hide *)
Abort.
(* end hide *)

Theorem absurd : ~P -> P -> Q.
(* begin hide *)
Abort.
(* end hide *)

Theorem impl_and : (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
(* begin hide *)
Proof.
  split; intro H'; destruct (H H'); assumption.
Qed.
(* end hide *)

End exercises_propositional.

Check and_comm.
(* ===> forall P Q : Prop, P /\ Q -> Q /\ P *)

(** W praktyce komenda [Hypothesis] służy do tego, żeby za dużo nie
    pisać — po zamknięciu sekcji komendą [End], Coq doda do każdego
    twierdzenia znajdującego się w tej sekcji kwantyfikację uniwersalną
    po hipotezach zadeklarowanych przy pomocy [Hypothesis]. W naszym
    przypadku Coq dodał do [and_comm] kwantyfikację po [P] i [Q],
    mimo że nie napisaliśmy jej explicite. *)

(** ** Konstruktywny rachunek predykatów *)

Section exercises_predicate. 
Variable A : Type.
Hypotheses P Q R S : A -> Prop.

(* Projekcje *)
Theorem forall_and_proj1 :
    (forall x : A, P x /\ Q x) -> (forall x : A, P x).
(* begin hide *)
Proof.
  intros. destruct (H x). assumption.
Qed.
(* end hide *)

Theorem forall_and_proj2 :
    (forall x : A, P x /\ Q x) -> (forall x : A, Q x).
(* begin hide *)
Proof.
  intros. destruct (H x). assumption.
Qed.
(* end hide *)

(* Rozdzielność *)
Theorem forall_dist_and :
    (forall x : A, P x /\ Q x) <->
    (forall x : A, P x) /\ (forall x : A, Q x).
(* begin hide *)
Proof.
  split.
    intros. split.
      intros. destruct (H x). assumption.
      intros. destruct (H x). assumption.
    intros. split.
      destruct H. apply H.
      destruct H. apply H0.
Restart.
  split; intros; split; intros; try destruct H; try (destruct (H x));
  try assumption; try apply H; try apply H0.
Qed.
(* end hide *)

Theorem exists_dist_or :
    (exists x : A, P x \/ Q x) <-> (exists x : A, P x) \/ (exists x : A, Q x).
(* begin hide *)
Proof.
  split; intros.
    destruct H as [x [HP | HQ]].
      left. exists x. assumption.
      right. exists x. assumption.
    destruct H as [[x HP] | [x HQ]].
      exists x. left. assumption.
      exists x. right. assumption.
Restart.
  split; intros.
    destruct H as [x [HP | HQ]];
      [left | right]; exists x; assumption.
    destruct H as [[x HP] | [x HQ]];
      exists x; [left | right]; assumption.
Qed.
(* end hide *)

(* Inne *)
Theorem forall_or_imp :
    (forall x : A, P x) \/ (forall x : A, Q x) -> (forall x : A, P x \/ Q x).
(* begin hide *)
Proof.
  destruct 1; intros.
    left. apply H.
    right. apply H.
Restart.
  destruct 1; intros; [left | right]; apply H.
Qed.
(* end hide *)

Theorem forall_imp_imp :
    (forall x : A, P x -> Q x) -> (forall x : A, P x) -> (forall x : A, Q x).
(* begin hide *)
Proof.
  intros. apply H. apply H0.
Qed.
(* end hide *)

Theorem forall_inhabited_nondep : forall R : Prop,
    A -> ((forall x : A, R) <-> R).
(* begin hide *)
Proof.
  split; intros.
    apply H. assumption.
    assumption.
Restart.
  split; intros; try apply H; assumption.
Qed.
(* end hide *)

Theorem forall_or_nondep : forall R : Prop,
    (forall x : A, P x) \/ R -> (forall x : A, P x \/ R).
(* begin hide *)
Proof.
  destruct 1; intros.
    left. apply H.
    right. assumption.
Qed.
(* end hide *)

Theorem forall_nondep_impl : forall R : Prop,
    (forall x : A, R -> P x) <-> (R -> forall x : A, P x).
(* begin hide *)
Proof.
  split; intros.
    apply H. assumption.
    apply H. assumption.
Restart.
  split; intros; apply H; assumption.
Qed.
(* end hide *)

End exercises_predicate.

(** ** Paradoks golibrody *)

Theorem barber_paradox : forall (man : Type) (barber : man)
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
    (przykładów jest masa, np. jednorożce).

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
    podstawiając [barber] za [x] otrzymujemy sprzeczność: [shaves barber barber]
    zachodzi wtedy i tylko wtedy, gdy [~ shaves barber barber].

    Tak więc golibroda, zupełnie jak Święty Mikołaj, nie istnieje. Zdanie to
    nie ma jednak wiele wspólnego ze światem rzeczywistym: wynika ono jedynie
    z takiej a nie innej, przyjętej przez nas całkowicie arbitralnie definicji
    słowa "golibroda". Można to łatwo zobrazować, przeformułowywując powyższe
    twierdzenie z użyciem innych nazw: *)

Theorem barber_paradox' :
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

(** ** Klasyczny rachunek zdań (i predykatów) *)

Section exercises_classical.
Require Import Classical.
Hypotheses P Q R S : Prop.

(** Komenda [Require Import] pozwala nam zaimportować żądany
    moduł z biblioteki standardowej Coqa. Dzięki temu będziemy
    mogli używać zawartych w nim definicji, twierdzeń etc.

    Classical to moduł, który pozwala przeprowadzać rozumowania
    w logice klasycznej. Deklaruje on jako aksjomaty niektóre
    tautologie logiki klasycznej, np. zasadę wyłączonego środka,
    która tutaj nazywa się [classic]. *)

Check classic.
(* ===> forall P : Prop, P \/ ~ P *)

Theorem imp_and_or : (P -> Q \/ R) -> ((P -> Q) \/ (P -> R)).
(* begin hide *)
Proof.
  intros. destruct (classic P) as [HP | HnotP].
    destruct (H HP); [left | right]; intro; assumption.
    left. intro. cut False.
      inversion 1.
      apply HnotP. apply H0.
Qed.
(* end hide *)

Theorem deMorgan_2_conv : ~(P /\ Q) -> ~P \/ ~Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Theorem not_imp : ~(P -> Q) -> P /\ ~Q.
(* begin hide *)
Abort.
(* end hide *)

Theorem imp_not_or : (P -> Q) -> (~P \/ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Theorem material_implication : (P -> Q) <-> (~P \/ Q).
(* begin hide *)
Proof.
  split; intros.
    destruct (classic P).
      right. apply H. assumption.
      left. intro. contradiction.
    destruct H.
      contradiction.
      assumption.
Qed.
(* end hide *)

Theorem contraposition_conv : (~Q -> ~P) -> (P -> Q).
(* begin hide *)
Abort.
(* end hide *)

Theorem excluded_middle : P \/ ~P.
(* begin hide *)
Abort.
(* end hide *)

Theorem peirce : ((P -> Q) -> P) -> P.
(* begin hide *)
Abort.
(* end hide *)

End exercises_classical.

(** ** Paradoks pijoka *)

Theorem drinker_paradox : forall (man : Type)
  (drinks : man -> Prop) (random_guy : man),
    exists drinker : man, drinks drinker ->
      forall x : man, drinks x.
(* begin hide *)
Proof.
  intros. destruct (classic (forall x : man, drinks x)).
    exists random_guy. intros _. assumption.
    apply not_all_ex_not in H. destruct H.
      exists x. intro. contradiction.
Qed.
(* end hide *)

(** Na zakończenie zwróćmy swą uwagę ku kolejnemu paradoksowi, tym razem
    dotyczącemu logiki klasycznej. Z angielska zwie się on "drinker's
    paradox", ja zaś ku powszechnej wesołości używał będę nazwy "paradoks
    pijoka".

    Zazwyczaj jest on wyrażany mniej więcej tak: w każdym barze jest taki
    człowiek, że jeżeli on pije, to wszyscy piją. Jak to możliwe? Czy
    matematyka stwierdza istnienie magicznych ludzi zdolnych popaść swoich
    barowych towarzyszy w alkoholizm?

    Oczywiście nie. W celu osiągnięcia oświecenia w tej kwestii prześledźmy
    dowód tego faktu (jeżeli nie udało ci się go wymyślić, pomyśl jeszcze
    trochę).

    Ustalmy najpierw, jak ma się formalne brzmienie twierdzenia do naszej
    poetyckiej parafrazy dwa akapity wyżej. Początek "w każdym barze"
    możemy pominąć i sformalizować sytuację w pewnym konkretnym barze. Nie
    ma to znaczenia dla prawdziwości tego zdania.

    Sytuację w barze modelujemy za pomocą typu [man], które reprezentuje
    klientów baru, predykatu [drinks], interpretowanego tak, że [drinks x]
    oznacza, że [x] pije. Pojawia się też osoba określona tajemniczym
    mianem [random_guy]. Jest ona konieczna, gdyż nasza poetycka parafraza
    czyni jedno założenie implicite: mianowicie, że w barze ktoś jest.
    Jest ono konieczne, gdyż gdyby w barze nie byłoby nikogo, to w szcezgóności
    nie mogłoby tam być nikogo, kto spełnia jakieś dodatkowe warunki.

    I tak docieramy do sedna sprawy: istnieje osoba, którą będziemy zwać
    pijokiem ([exists drinker : man]), taka, że jeżeli ona pije ([drinks
    drinker]), to wszyscy piją ([forall x : man, drinks x]).

    Dowód jest banalny i opiera się na zasadzie wyłączonego środka, w Coqu
    zwanej [classic]. Dzięki niej możemy sprowadzić dowód do analizy
    dwóch przypadków.

    Przypadek 1: wszyscy piją. Cóż, skoro wszyscy piją, to wszyscy piją.
    Pozostaje nam wskazać pijoka: mógłby to być ktokolwiek, ale z
    konieczności zostaje nim [random_guy], gdyż do żadnego innego klienta
    baru nie możemy się odnieść.

    Przypadek 2: nieprawda, że wszyscy piją. Parafrazując: istnieje ktoś,
    kto nie pije. Jest to obserwacja kluczowa. Skoro kolo przyszedł do baru
    i nie pije, to z automatu jest podejrzany. Uczyńmy go więc, wbrew
    zdrowemu rozsądkowi, naszym pijokiem.

    Pozostaje nam udowodnić, że jeżeli pijok pije, to wszyscy piją. Załóżmy
    więc, że pijok pije. Wiemy jednak skądinąd, że pijok nie pije. Wobec
    tego mamy sprzeczność i wszyscy piją (a także jedzą naleśniki z betonem
    serwowane przez gadające ślimaki i robią dużo innych dziwnych rzeczy —
    wszakże _ex falso quodlibet_).

    Gdzież więc leży paradoksalność całego paradoksu? Wynika ona w znacznej
    mierze ze znaczenia słowa "jeżeli". W mowie potocznej różni się ono
    znacznie od tzw. implikacji materialnej, w Coqu reprezentowanej (ale
    tylko przy założeniu reguły wyłączonego środka) przez implikację ([->]).

    Określenie "taka osoba, że jeżeli ona pije, to wszyscy piją" przeciętny
    człowiek interpretuje w kategoriach przyczyny i skutku, a więc przypisuje
    rzeczonej osobie magiczną zdolność zmuszania wszystkich do picia, tak
    jakby posiadała zdolność wznoszenia toastów za pomocą telepatii.

    Jest to błąd, gdyż zamierzonym znaczeniem słowa jeżeli jest tutaj (ze
    względu na kontekst matematyczny) implikacja materialna. W jednym z
    powyższych ćwiczeń udowodniłeś, że w logice klasycznej mamy tautologię
    [P -> Q <-> ~P \/ Q], a więc że implikacja jest prawdziwa gdy jej
    przesłanka jest fałszywa lub gdy jej konkluzja jest prawdziwa.

    Do paradoksalności paradoksu swoje cegiełki dokładają też reguły logiki
    klasycznej (wyłączony środek) oraz logiki konstruktywnej (_ex falso
    quodlibet_), których w użyliśmy w dowodzie, a które dla zwykłego człowieka
    nie muszą być takie oczywiste. *)

(** **** Ćwiczenie *)

(** W powyższym dowodzie logiki klasycznej użyłem conajmniej dwukrotnie.
    Zacytuj wszystkie fragmenty dowodu wykorzystujące logikę klasyczną. *)

(** **** Ćwiczenie *)
(** Pokaż, że założenie o tym, że w barze jest conajmniej jeden klient,
    jest konieczne. Co więcej, pokaż że stwierdzenie "w barze jest taki
    klient, że jeżeli on pije, to wszyscy piją" jest równoważne stwierdzeniu
    "w barze jest jakiś klient". *)

Theorem dp_nonempty :
  forall (man : Type) (drinks : man -> Prop),
    (exists drinker : man, drinks drinker ->
      forall x : man, drinks x) <->
    (exists x : man, True).
(* begin hide *)
Proof.
  split; intros; destruct H as [random_guy _].
    exists random_guy. trivial.
    apply drinker_paradox. assumption.
Qed.
(* end hide *)