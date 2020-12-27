(** * B0: Stary rozdział o logice *)

(* begin hide *)
(*
TODO 1: Napisać bardziej wprost o deklarowaniu hipotez.
TODO 2: opisać rzeczy do strukturyzowania dowodów, np. `{}` albo bullet
TODO 2: pointy `*`, `+` i `-`
*)
(* end hide *)

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

(** * Logika klasyczna i konstruktywna *)

(** Jak udowodnić twierdzenie, by komputer mógł zweryfikować nasz
    dowód? Jedną z metod dowodzenia używanych w logice klasycznej
    są tabelki prawdy. Są one metodą skuteczną, gdyż działają
    zawsze i wszędzie, ale nie są wolne od problemów.

    Pierwszą, praktyczną przeszkodą jest rozmiar tabelek — rośnie on
    wykładniczo wraz ze wzrostem ilości zmiennych zdaniowych, co czyni
    tę metodę skrajnie niewydajną i obliczeniożerną, a więc niepraktyczną
    dla twierdzeń większych niż zabawkowe.

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
    obserwując skutki działania każdej komendy i taktyki.

    W razie problemów z CoqIDE poszukaj pomocy w manualu:
    https://coq.inria.fr/refman/practical-tools/coqide.html *)

Section constructive_propositional_logic.

(** Mechanizm sekcji nie będzie nas na razie interesował. Użyjemy go,
    żeby nie zaśmiecać głównej przestrzeni nazw. *)

Hypothesis P Q R : Prop.

(** Zapis [x : A] oznacza, że term [x] jest typu [A]. [Prop] to typ zdań
    logicznych, więc komendę tę można odczytać następująco: niech [P], [Q]
    i [R] będą zdaniami logicznymi. Używamy tej komendy, gdyż potrzebujemy
    jakichś zdań logicznych, na których będziemy operować. *)

(** ** Implikacja *)

(** Zacznijmy od czegoś prostego: pokażemy, że [P] implikuje [P]. *)

Lemma impl_refl : P -> P.
Proof.
  intro dowód_na_to_że_P_zachodzi.
  exact dowód_na_to_że_P_zachodzi.
Qed.

(** Słowo kluczowe [Lemma] obwieszcza, że chcemy podać twierdzenie.
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
    od [Lemma], po prawej stronie ekranu pojawi się stan aktualnie
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

Lemma impl_refl' : P -> P.
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

    Taktyka [assumption] (pol. "założenie") sama potrafi znaleźć
    nazwę hipotezy, która rozwiązuje cel. Jeżeli nie znajdzie
    takiej hipotezy, to zawodzi. Jej użycie w dowodzenie nieformalnym
    odpowiada stwierdzeniu "P zachodzi na mocy założenia". *)

Print impl_refl'.
(* ===> impl_refl' = fun H : P => H : P -> P *)

(** Uwaga: w komentarzach postaci (* ===> *) będę przedstawiać wyniki
    wypisywane przez komendy, żeby leniwi czytacze nie musieli sami
    sprawdzać.

    Wspomnieliśmy wcześniej, że zdania logiczne są typami,
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

Lemma modus_ponens :
  (P -> Q) -> P -> Q.
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

(** **** Ćwiczenie (implikacja) *)

(** Udowodnij poniższe twierdzenia. *)

Lemma impl_trans :
  (P -> Q) -> (Q -> R) -> (P -> R).
(* begin hide *)
Proof.
  intros. apply H0. apply H. assumption.
Qed.
(* end hide *)

Lemma impl_permute :
  (P -> Q -> R) -> (Q -> P -> R).
(* begin hide *)
Proof.
  intros. apply H.
    assumption.
    assumption.
Qed.
(* end hide *)

Lemma impl_dist :
  (P -> Q -> R) -> ((P -> Q) -> (P -> R)).
(* begin hide *)
Proof.
  intros. apply H.
    assumption.
    apply H0. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie (bez [apply])*)

(** Udowodnij następujące twierdzenie bez używania taktyki [apply]. *)

Lemma modus_ponens' :
  (P -> Q) -> P -> Q.
(* begin hide *)
Proof.
   intro. assumption.
Qed.
(* end hide *)

(** ** Fałsz *)

Lemma ex_falso : False -> P.
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

Lemma truth : True.
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

(** *** Komendy [Check] i [Locate] *)

Check P.
(* ===> P : Prop *)

(** Typ każdego termu możemy sprawdzić przy pomocy komendy [Check].
    Jest ona nie do przecenienia. Jeżeli nie rozumiesz, co się
    dzieje w trakcie dowodu lub dlaczego Coq nie chce zaakceptować
    jakiejś definicji, użyj komendy [Check], żeby sprawdzić,
    z jakimi typami masz do czynienia. *)

Check ~P.
(* ===> ~ P : Prop *)

(** W Coqu negację zdania [P] oznaczamy przez [~P]. Symbol [~]
    nie jest jednak nazwą negacji — nazwy nie mogą zawierać symboli.
    Jest to jedynie notacja, która ma uczynić zapis krótszym i
    bardziej podobnym do tego używanego na co dzień. Niesie to
    jednak za sobą pewne konsekwencje — nie możemy np. użyć
    komendy [Print ~.], żeby wyświetlić definicję negacji. Jak
    więc poznać nazwę, kryjącą się za jakąś notacją? *)

Locate "~".
(* ===> "~ x" := not x ... *)

(** Możemy to zrobić przy pomocy komendy [Locate]. Wyświetla ona,
    do jakich nazw odwołuje się dana notacja. Jak widać, negacja
    w Coqu nazywa się [not]. *)

(** ** Negacja *)

(** W logice klasycznej negację zdania P można zinterpretować
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

Lemma P_notP : ~P -> P -> False.
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

Lemma P_notP' : ~P -> P -> 42 = 666.
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

(** **** Ćwiczenie (negacja) *)

(** Udowodnij poniższe twierdzenia. *)

Lemma not_False : ~False.
(* begin hide *)
Proof.
  intro. assumption.
Qed.
(* end hide *)

Lemma not_True : ~True -> False.
(* begin hide *)
Proof.
  intro. apply H. trivial.
Qed.
(* end hide *)

(** **** Ćwiczenie (podwójna negacja) *)

(** Udowodnij poniższe twierdzenia. Zastanów się, czy można udowodnić
    [~~P -> P]. *)

Lemma dbl_neg_intro : P -> ~~P.
(* begin hide *)
Proof.
  unfold not. intros. apply H0. assumption.
Qed.
(* end hide *)

Lemma double_neg_elim_irrefutable :
  ~~ (~~ P -> P).
(* begin hide *)
Proof.
  intro. apply H. intro. cut False.
    inversion 1.
    apply H0. intro. apply H. intro. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie (potrójna negacja) *)

(** Udowodnij poniższe twierdzenie. Jakie są różnice między negacją, podwójną
    negacją i potrójną negacją? *)

Lemma triple_neg_rev : ~~~P -> ~P.
(* begin hide *)
Proof.
  unfold not. intros. apply H. intro. apply H1. assumption.
Qed.
(* end hide *)

(** ** Koniunkcja *)

Lemma and_intro : P -> Q -> P /\ Q.
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

Lemma and_proj1 : P /\ Q -> P.
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

Lemma and_proj1' : P /\ Q -> P.
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

(** **** Ćwiczenie (koniunkcja) *)

(** Udowodnij poniższe twierdzenia. *)

Lemma and_proj2 : P /\ Q -> Q.
(* begin hide *)
Proof.
  intro. destruct H. assumption.
Qed.
(* end hide *)

Lemma and3_intro : P -> Q -> R -> P /\ Q /\ R.
(* begin hide *)
Proof.
  intros. split. assumption. split. assumption. assumption.
Qed.
(* end hide *)

Lemma and3_proj : P /\ Q /\ R -> Q.
(* begin hide *)
Proof.
  intro. destruct H. destruct H0. assumption.
Qed.
(* end hide *)

Lemma noncontradiction : ~ (P /\ ~ P).
(* begin hide *)
Proof.
  intro. destruct H. apply H0. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie ([ex_contradictione]) *)

Lemma ex_contradictione : (P /\ ~ P) -> Q.
(* begin hide *)
Proof.
  intros [p np].
  apply np in p.
  contradiction.
Qed.
(* end hide *)

(** Ciekawostka: powyższe prawo można by nazwać "ex contradictione
    (sequitur) quodlibet", czyli "ze sprzeczności wynika cokolwiek
    zechcesz".

    Jest ono połączeniem prawa niesprzeczności ([noncontradiction])
    oraz ex falso quodlibet ([ex_falso]). W niektórych biedackich
    systemach logicznych, w których nie ma odpowiednika [False],
    może być użyte zamiast [ex_falso]. *)

(** ** Równoważność zdaniowa *)

(** Równoważność zdaniowa jest w Coqu oznaczana [<->]. Symbol ten,
    jak (prawie) każdy jest jedynie notacją — równoważność
    nazywa się [iff]. Jest to skrót od ang. "if and only if". Po
    polsku zdanie [P <-> Q] możemy odczytać jako "P wtedy i tylko
    wtedy, gdy Q". *)

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

Lemma iff_intro : (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof.
  intros. split.
    intro. apply H. assumption.
    intro. apply H0. assumption.
Qed.

(** Do rozbijania równoważności będących celem służy, tak jak w
    przypadku koniunkcji, taktyka [split]. *)

Lemma iff_proj1 : (P <-> Q) -> (P -> Q).
Proof.
  intros. destruct H as [HPQ HQP].
  apply HPQ. assumption.
Qed.

(** Równoważnosć znajdującą się w kontekście możemy zaś, tak jak
    koniunkcje, rozbijać taktyką [destruct]. Taką samą postać ma
    również wzorzec, służący w klauzuli [as] do nadawania nazw
    zmiennym. *)

(** **** Ćwiczenie (równoważność zdaniowa) *)

(** Udowodnij poniższe twierdzenia. *)

Lemma iff_refl : P <-> P.
(* begin hide *)
Proof.
  split.
    intro. assumption.
    intro. assumption.
Qed.
(* end hide *)

Lemma iff_symm : (P <-> Q) -> (Q <-> P).
(* begin hide *)
Proof.
  intro. destruct H. split.
    intro. apply H0. assumption.
    intro. apply H. assumption.
Qed.
(* end hide *)

Lemma iff_trans: (P <-> Q) -> (Q <-> R) -> (P <-> R).
(* begin hide *)
Proof.
  intros. destruct H, H0. split.
    intro. apply H0. apply H. assumption.
    intro. apply H1. apply H2. assumption.
Qed.
(* end hide *)

Lemma iff_not : (P <-> Q) -> (~P <-> ~Q).
(* begin hide *)
Proof.
  intro. destruct H as [HPQ HQP]. split.
    intro. intro. apply H. apply HQP. assumption.
    intro. intro. apply H. apply HPQ. assumption.
Qed.
(* end hide *)

Lemma curry_uncurry : (P -> Q -> R) <-> (P /\ Q -> R).
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

(** ** Dysjunkcja *)

Lemma or_left : P -> P \/ Q.
Proof.
  intro. left. assumption.
Qed.

(** Symbol [\/] oznacza dysjunkcję dwóch zdań logicznych. W języku polskim
    czasem używa się też określenia "alternatywa", ale będziemy się tego
    wystrzegać, rezerwując to słowo dla czegoś innego. Żeby dowieść
    dysjunkcji [P \/ Q], musimy udowonić albo lewy, albo prawy jej człon.
    Taktyki [left] oraz [right] pozwalają nam wybrać, którego z nich chcemy
    dowodzić. *)

Lemma or_comm_impl : P \/ Q -> Q \/ P.
Proof.
  intro. destruct H as [p | q].
    right. assumption.
    left. assumption.
Qed.

(** Zauważmy, że użycie taktyki [destruct] zmieniło nam ilość celów.
    Wynika to z faktu, że nie wiemy, który człon hipotezy [P \/ Q] jest
    prawdziwy, więc dla każdego przypadku musimy przeprowadzić osobny
    dowód. Inaczej wygląda też wzorzec służący do rozbicia tej
    hipotezy — w przypadku dysjunkcji ma on postać [[nazwa1 | nazwa2]].

    Interpretacja obliczeniowa dysjunkcji jest następująca: jest to
    suma rozłączna dwóch zdań. Dowód dysjunkcji to dowód jednego z
    jej członów z dodatkową informacją o tym, który to człon.

    To ostatnie stwierdzenie odróżnia dysjunkcję konstruktywną od
    klasycznej: klasyczna dysjunkcja to stwierdzenie "któres z tych
    dwóch zdań jest prawdziwe (lub oba)", zaś konstruktywna to
    stwierdzenie "lewy człon jest prawdziwy albo prawy człon jest
    prawdziwy (albo oba, ale i tak dowodzimy tylko jednego)". Jest
    to znaczna różnica — w przypadku logiki klasycznej nie wiemy,
    który człon jest prawdziwy. *)

(** **** Ćwiczenie (dysjunkcja) *)

(** Udowodnij poniższe twierdzenia. *)

Lemma or_right : Q -> P \/ Q.
(* begin hide *)
Proof.
  intro. right. assumption.
Qed.
(* end hide *)

Lemma or_big : Q -> P \/ Q \/ R.
(* begin hide *)
Proof.
  intro. right. left. assumption.
Qed.
(* end hide *)

Lemma or3_comm_impl : P \/ Q \/ R -> R \/ Q \/ P.
(* begin hide *)
Proof.
  intro. destruct H. right. right. assumption.
  destruct H. right. left. assumption. left. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie (dysjunkcja i implikacja) *)

(** Udowodnij poniższe twierdzenie. Następnie zastanów się, czy odwrotna
    implikacja również zachodzi. *)

Lemma or_impl : ~P \/ Q -> (P -> Q).
(* begin hide *)
Proof.
  intros. destruct H.
    cut False.
      inversion 1.
      apply H. assumption.
    assumption.
Qed.
(* end hide *)

(** * Konstruktywny rachunek kwantyfikatorów *)

End constructive_propositional_logic.

(** Komenda [End] zamyka sekcję, którą otworzyliśmy na samym początku
    tego rozdziału. Zdania [P], [Q] i [R] znikają z
    dostępnej dla nas przestrzeni nazw, dzięki czemu uniknęliśmy jej
    zaśmiecenia. Nasze twierdzenia wciąż są jednak dostępne (sprawdź
    to).

    Zajmiemy się teraz konstruktywnym rachunkiem kwantyfikatorów. Jest on
    rozszerzeniem omówionego przed chwilą konstruktywnego rachunku zdań
    o kwantyfikatory, które pozwolą nam wyrażać takie zależności jak "każdy"
    oraz "istnieje", oraz o predykaty i relacje, które mózemy interpretować
    odpowiednio jako właściwości obiektów oraz zależności między obiektami. *)

(** ** Kwantyfikacja uniwersalna *)

(** Zobaczmy o co chodzi na znanym nam już przykładzie zwrotności
    implikacji: *)

Lemma impl_refl'' : forall P : Prop, P -> P.
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

Lemma general_to_particular :
  forall P : nat -> Prop,
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
    powyższy dowód — spróbuj wstawić w jej miejsce [Qed]. Użyłem jej
    tylko po to, żeby czytelnie zestawić ze sobą sposoby rozumowania
    w przód i w tył dla kwantyfikacji uniwersalnej. *)

Lemma and_proj1'' :
  forall (P Q : nat -> Prop),
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
    napisalibyśmy [destruct (H 42)] (choć i tak najszybciej jest
    oczywiście użyć [apply H]. *)

(** **** Ćwiczenie (kwantyfikacja uniwersalna) *)

(** Udowodnij poniższe twierdzenie. Co ono oznacza? Przeczytaj je na głos.
    Zinterpretuj je, tzn. sparafrazuj. *)

Lemma all_dist :
  forall (A : Type) (P Q : A -> Prop),
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

Lemma ex_example1 :
  exists n : nat, n = 0.
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

Lemma ex_example2 :
  ~ exists n : nat, 0 = S n.
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
    - udowodnienie dysjunkcji wymaga udowodnienia któregoś z członów,
      więc dowód dysjunkcji można rozbić, uzyskując dwa osobne podcele,
      a w każdym z nich dowód jednego z członów tej dysjunkcji
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

(** **** Ćwiczenie (kwantyfikacja egzystencjalna) *)

(** Udowodnij poniższe twierdzenie. *)

Lemma ex_or_dist :
  forall (A : Type) (P Q : A -> Prop),
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

(** * Zadania *)

(** Poniższe zadania stanowią (chyba) kompletny zbiór praw rządzących
    logikami konstruktywną i klasyczną (w szczególności, niektóre z
    zadań mogą pokrywać się z ćwiczeniami zawartymi w tekście). Wróć
    do nich za jakiś czas, gdy czas przetrzebi trochę twoją pamięć
    (np. za tydzień).

    Rozwiąż wszystkie zadania dwukrotnie: raz ręcznie, zaś za drugim
    razem w sposób zautomatyzowany. *)

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

Ltac leftright t := ((left; t) || (right; t)).
(* end hide *)

(** *** Przemienność *)

Lemma and_comm :
  P /\ Q -> Q /\ P.
(* begin hide *)
Proof.
  destruct 1; split; assumption.
Restart.
  search.
Qed.
(* end hide *)

Lemma or_comm :
  P \/ Q -> Q \/ P.
(* begin hide *)
Proof.
  destruct 1; [right | left]; assumption.
Qed.
(* end hide *)

(** *** Łączność *)

Lemma and_assoc :
  P /\ (Q /\ R) <-> (P /\ Q) /\ R.
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

Lemma or_assoc :
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
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

(** *** Rozdzielność *)

Lemma and_dist_or :
  P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
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

Lemma or_dist_and :
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
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

Lemma imp_dist_imp :
  (P -> Q -> R) <-> ((P -> Q) -> (P -> R)).
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

(** *** Kuryfikacja i dekuryfikacja *)

Lemma curry :
  (P /\ Q -> R) -> (P -> Q -> R).
(* begin hide *)
Proof.
  intros; apply H; split; assumption.
Restart.
  search.
Qed.
(* end hide *)

Lemma uncurry :
  (P -> Q -> R) -> (P /\ Q -> R).
(* begin hide *)
Proof.
  intros pqr pq.
  destruct pq as [p q].
  apply pqr.
    assumption.
    assumption.
Qed.
(* end hide *)

(** *** Prawa de Morgana *)

Lemma deMorgan_1 :
  ~(P \/ Q) <-> ~P /\ ~Q.
(* begin hide *)
Proof.
  split.
    intro npq. split.
      intro p. apply npq. left. assumption.
      intro q. apply npq. right. assumption.
    intros npnq npq. destruct npnq as [np nq]. destruct npq.
      apply np. assumption.
      apply nq. assumption.
Qed.
(* end hide *)

Lemma deMorgan_2 :
  ~P \/ ~Q -> ~(P /\ Q).
(* begin hide *)
Proof.
  intros npnq pq.
  destruct pq as [p q].
  destruct npnq as [np | nq].
    apply np. assumption.
    apply nq. assumption.
Qed.
(* end hide *)

(** *** Niesprzeczność i zasada wyłączonego środka *)

Lemma noncontradiction' :
  ~(P /\ ~P).
(* begin hide *)
Proof.
  unfold not; intros. destruct H. apply H0. assumption.
Restart.
  search.
Qed.
(* end hide *)

Lemma noncontradiction_v2 :
  ~ (P <-> ~P).
(* begin hide *)
Proof.
  intro H.
  destruct H as [lr rl].
  apply lr.
    apply rl. intro p. apply lr.
      assumption.
      assumption.
    apply rl. intro p. apply lr.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma em_irrefutable :
  ~~ (P \/ ~P).
(* begin hide *)
Proof.
  intro H.
  apply H.
  right. intro p.
  apply H.
  left. assumption.
Qed.
(* end hide *)

(** *** Elementy neutralne i anihilujące *)

Lemma and_false_annihilation :
  P /\ False <-> False.
(* begin hide *)
Proof.
  split; intro H.
    destruct H. contradiction.
    contradiction.
Qed.
(* end hide *)

Lemma or_false_neutral :
  P \/ False <-> P.
(* begin hide *)
Proof.
  split.
    intro H. destruct H.
      assumption.
      contradiction.
    intro p. left. assumption.
Qed.
(* end hide *)

Lemma and_true_neutral :
  P /\ True <-> P.
(* begin hide *)
Proof.
  split.
    intro H. destruct H as [p t]. assumption.
    intro p. split.
      assumption.
      trivial.
Qed.
(* end hide *)

Lemma or_true_annihilation :
  P \/ True <-> True.
(* begin hide *)
Proof.
  split.
    intros _. trivial.
    intros _. right. trivial.
Qed.
(* end hide *)

(** *** Inne *)

Lemma or_imp_and :
  (P \/ Q -> R) <-> (P -> R) /\ (Q -> R).
(* begin hide *)
Proof.
  split.
    intro H. split.
      intro p. apply H. left. assumption.
      intro q. apply H. right. assumption.
    intros H1 H2. destruct H1 as [pr qr]. destruct H2 as [p | q].
      apply pr. assumption.
      apply qr. assumption.
Qed.
(* end hide *)

Lemma and_not_imp :
  P /\ ~ Q -> ~ (P -> Q).
(* begin hide *)
Proof.
  intros H pq. destruct H as [p nq].
  apply nq. apply pq. assumption.
Qed.
(* end hide *)

Lemma or_not_imp :
  ~ P \/ Q -> (P -> Q).
(* begin hide *)
Proof.
  intros H p. destruct H as [np | q].
    contradiction.
    assumption.
Qed.
(* end hide *)

Lemma contraposition :
  (P -> Q) -> (~ Q -> ~ P).
(* begin hide *)
Proof.
  intros pq nq p. apply nq, pq, p.
Qed.
(* end hide *)

Lemma absurd :
  ~ P -> P -> Q.
(* begin hide *)
Proof.
  intros np p. contradiction.
Qed.
(* end hide *)

Lemma impl_and :
  (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
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

(** ** Konstruktywny rachunek kwantyfikatorów *)

Section QuantifiersExercises.

Variable A : Type.
Hypotheses P Q : A -> Prop.

(** *** Projekcje *)

Lemma forall_and_proj1 :
  (forall x : A, P x /\ Q x) -> (forall x : A, P x).
(* begin hide *)
Proof.
  intros. destruct (H x). assumption.
Qed.
(* end hide *)

Lemma forall_and_proj2 :
  (forall x : A, P x /\ Q x) -> (forall x : A, Q x).
(* begin hide *)
Proof.
  intros. destruct (H x). assumption.
Qed.
(* end hide *)

(** *** Rozdzielność *)

Lemma forall_dist_and :
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

Lemma exists_dist_or :
  (exists x : A, P x \/ Q x) <->
  (exists x : A, P x) \/ (exists x : A, Q x).
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

Lemma ex_dist_and :
  (exists x : A, P x /\ Q x) ->
    (exists y : A, P y) /\ (exists z : A, Q z).
(* begin hide *)
Proof.
  intros. destruct H as [x H]. destruct H.
  split; exists x; assumption.
Qed.
(* end hide *)

(** *** Inne *)

Lemma forall_or_imp :
  (forall x : A, P x) \/ (forall x : A, Q x) ->
    forall x : A, P x \/ Q x.
(* begin hide *)
Proof.
  destruct 1; intros.
    left. apply H.
    right. apply H.
Restart.
  destruct 1; intros; [left | right]; apply H.
Qed.
(* end hide *)

Lemma forall_imp_imp :
  (forall x : A, P x -> Q x) ->
    (forall x : A, P x) -> (forall x : A, Q x).
(* begin hide *)
Proof.
  intros. apply H. apply H0.
Qed.
(* end hide *)

Lemma forall_inhabited_nondep :
  forall R : Prop, A -> ((forall x : A, R) <-> R).
(* begin hide *)
(* TODO: wyrzucić *)
Proof.
  split; intros.
    apply H. assumption.
    assumption.
Restart.
  split; intros; try apply H; assumption.
Qed.
(* end hide *)

Lemma forall_or_nondep :
  forall R : Prop,
    (forall x : A, P x) \/ R -> (forall x : A, P x \/ R).
(* begin hide *)
Proof.
  destruct 1; intros.
    left. apply H.
    right. assumption.
Qed.
(* end hide *)

Lemma forall_nondep_impl :
  forall R : Prop,
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

End QuantifiersExercises.

(** ** Klasyczny rachunek zdań (i kwantyfikatorów) *)

Section ClassicalExercises.

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

Lemma imp_and_or : (P -> Q \/ R) -> ((P -> Q) \/ (P -> R)).
(* begin hide *)
Proof.
  intros. destruct (classic P) as [HP | HnotP].
    destruct (H HP); [left | right]; intro; assumption.
    left. intro. cut False.
      inversion 1.
      apply HnotP. apply H0.
Qed.
(* end hide *)

Lemma deMorgan_2_conv : ~ (P /\ Q) -> ~ P \/ ~Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_impl : ~ (P -> Q) -> P /\ ~ Q.
(* begin hide *)
Proof.
  intro H. split.
    cut False.
      destruct 1.
      apply H. intro.
Abort.
(* end hide *)

Lemma impl_not_or : (P -> Q) -> (~ P \/ Q).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma material_implication : (P -> Q) <-> (~P \/ Q).
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

Lemma contraposition_conv : (~ Q -> ~ P) -> (P -> Q).
(* begin hide *)
Proof.
  intros H p. cut False.
    destruct 1.
    apply H.
Abort.
(* end hide *)

Lemma excluded_middle : P \/ ~P.
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma peirce : ((P -> Q) -> P) -> P.
(* begin hide *)
Proof.
Abort.
(* end hide *)

End ClassicalExercises.

(** * Paradoks pijoka *)

Theorem drinkers_paradox :
  forall (man : Type) (drinks : man -> Prop) (random_guy : man),
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
    Jest ono konieczne, gdyż gdyby w barze nie było nikogo, to w szczególności
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

(** **** Ćwiczenie (logika klasyczna) *)

(** W powyższym dowodzie logiki klasycznej użyłem conajmniej dwukrotnie.
    Zacytuj wszystkie fragmenty dowodu wykorzystujące logikę klasyczną. *)

(** **** Ćwiczenie (niepusty bar) *)

(** Pokaż, że założenie o tym, że w barze jest conajmniej jeden klient,
    jest konieczne. Co więcej, pokaż że stwierdzenie "w barze jest taki
    klient, że jeżeli on pije, to wszyscy piją" jest równoważne stwierdzeniu
    "w barze jest jakiś klient".

    Które z tych dwóch implikacji wymagają logiki intuicjonistycznej, a
    które klasycznej? *)

Lemma dp_nonempty :
  forall (man : Type) (drinks : man -> Prop),
    (exists drinker : man, drinks drinker ->
      forall x : man, drinks x) <->
    (exists x : man, True).
(* begin hide *)
Proof.
  split; intros; destruct H as [random_guy _].
    exists random_guy. trivial.
    apply drinkers_paradox. assumption.
Qed.
(* end hide *)

(** * Ściąga *)

(** Zauważyłem palącą potrzebę istnienia krótkiej ściągi, dotyczącą
    podstaw logiki. Oto i ona (ściąga, nie potrzeba):
    - [True] to zdanie zawsze prawdziwe. Można je udowodnić za pomocą
      taktyki [trivial]. Można je też rozbić za pomocą [destruct], ale
      nie jest to zbyt użyteczne.
    - [False] to zdanie zawsze fałszywe. Można je udowodnić tylko jeżeli
      w kontekście już mamy jakiś inny (zazwyczaj zakamuflowany) dowód
      [False]. Można je rozbić za pomocą taktyki [destruct], co kończy
      dowód, bo z fałszu wynika wszystko.
    - [P /\ Q] to koniunkcja zdań [P] i [Q]. Aby ją udowodnić, używamy
      taktyki [split] i dowodzimy osobno [P], a osobno [Q]. Jeżeli mamy
      w kontekście dowód na [P /\ Q], to za pomocą taktyki [destruct]
      możemy z niego wyciągnąć dowody na [P] i na [Q].
    - [P \/ Q] to dysjunkcja zdań [P] i [Q]. Aby ją udowodnić, używamy
      taktyki [left] lub [right], a następnie dowodzimy odpowiednio [P]
      albo [Q]. Jeżeli mamy w kontekście dowód [H : P \/ Q], to możemy go
      rozbić za pomocą taktyki [destruct H], co odpowiada rozumowaniu przez
      przypadki: musimy pokazać, że cel jest prawdziwy zarówno, gdy prawdziwe
      jest tylko [P], jak i wtedy, gdy prawdziwe jest jedynie [Q]
    - [P -> Q] to zdanie "[P] implikuje [Q]". Żeby je udowodnić, używamy
      taktyki [intro] lub [intros], które wprowadzają do kontekstu dowód
      na [P] będący założeniem. Jeżeli mamy w kontekście dowód [H : P -> Q],
      to możemy dowieść [Q] za pomocą taktyki [apply H], a następnie będziemy
      musieli udowodnić [P]. Jeżeli mamy w kontekście [H : P -> Q] oraz
      [p : P], to możemy uzyskać dowód [p : Q] za pomocą taktyki
      [apply H in p]. Możemy uzyskać [H : Q] za pomocą [specialize (H p)]
    - [~ P] to negacja zdania [P]. Faktycznie jest to notacja na [not P],
      które to samo jest skrótem oznaczającym [P -> False]. Z negacją
      radzimy sobie za pomocą taktyki [unfold not] albo [unfold not in ...],
      a następnie postępujemy jak z implikacją.
    - [P <-> Q] to równoważność zdań [P] i [Q]. Jest to notacja na [iff P Q],
      które jest skrótem od [(P -> Q) /\ (Q -> P)]. Radzimy sobie z nią za
      pomocą taktyk [unfold iff] oraz [unfold iff in ...]
    - [forall x : A, P x] to zdanie mówiące "dla każdego x typu A zachodzi
      P x". Postępujemy z nim tak jak z implikacją, która jest jego
      specjalnym przypadkiem.
    - [exists x : A, P x] to zdanie mówiące "istnieje taki x typu A, który
      spełnia P". Dowodzimy go za pomocą taktyki [exists a], a następnie
      musimy pokazać [P a]. Jeżeli mamy taki dowód w kontekście, możemy
      rozbić go na [a] i [P a] za pomocą taktyki [destruct]. *)

(** Tutaj dodatkowa ściąga, w nieco bardziej czytelnym formacie:
    https://github.com/wkolowski/Typonomikon/tree/master/txt/logika.md

    Tutaj inna ściąga:
    https://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf *)

(** * Konkluzja *)

(** W niniejszym rozdziale zapoznaliśmy się z logiką konstruktywną.
    Poznaliśmy  jej składnię, interpretację obliczeniową, nauczyliśmy
    się dowodzić w systemie dedukcji naturalnej oraz dowiedzieliśmy
    się, jak to wszystko zrealizować w Coqu. Poznaliśmy też kombinatory
    taktyk, dzięki którym możemy skrócić i uprościć nasze formalne dowody.

    Zapoznaliśmy się też z logiką klasyczną i jej interpretacją. Poznaliśmy
    też dwa paradoksy związane z różnicami w interpretacji zdań w języku
    naturalnym oraz zdań matematycznych. Jeden z paradoksów dobrze pokazał
    nam w praktyce, na czym polega różnica między logiką konstruktywną i
    klasyczną.

    Skoro potrafimy już co nieco dowodzić, a także wiemy, że nasze metody
    nie nadają się do rozumowania o pieniądzach ani kebabach, nadszedł
    czas zapoznać się z jakimiś bytami, o których moglibyśmy czegoś
    dowieść — w następnym rozdziale zajmiemy się na poważnie typami,
    programami i obliczeniami oraz udowadnianiem ich właściwości. *)