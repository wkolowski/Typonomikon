(** * B1: Konstruktywny rachunek zdań [TODO] *)

(* begin hide *)
(*
TODO 1: Napisać bardziej wprost o deklarowaniu hipotez.
TODO 2: opisać rzeczy do strukturyzowania dowodów, np. `{}` albo bullet
TODO 2: pointy `*`, `+` i `-`
*)
(* end hide *)

(** * Stary wstęp *)

(** ** Logika klasyczna i konstruktywna *)

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

(** ** Dedukcja naturalna i taktyki *)

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

(** * Wstęp *)

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

(** ** Zdania logiczne *)

(** ** Rozumowanie i dowodzenie *)

(** ** Reguły i taktyki *)

(** ** Przydatne komendy *)

(** *** Komendy [Check] i [Locate] *)

(* Check P. *) (* TODO *)
(* ===> P : Prop *)

(** Typ każdego termu możemy sprawdzić przy pomocy komendy [Check].
    Jest ona nie do przecenienia. Jeżeli nie rozumiesz, co się
    dzieje w trakcie dowodu lub dlaczego Coq nie chce zaakceptować
    jakiejś definicji, użyj komendy [Check], żeby sprawdzić,
    z jakimi typami masz do czynienia. *)

(* Check ~ P. *) (* TODO *)
(* ===> ~ P : Prop *)

(** W Coqu negację zdania [P] oznaczamy przez [~ P]. Symbol [~]
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

(** * Zdania i spójniki logiczne (TODO) *)

(** Nadszedł dobry moment na to, żebyś odpalił CoqIDE. Sesja
    interaktywna w CoqIDE przebiega następująco: edytujemy plik
    z rozszerzeniem .v wpisując komendy. Po kliknięciu przycisku
    "Forward one command" (strzałka w dół) Coq interpretuje kolejną
    komendę, a po kliknięciu "Backward one command" (strzałka w
    górę) cofa się o jedną komendę do tyłu. Ta interaktywność,
    szczególnie w trakcie przeprowadzania dowodu, jest bardzo
    mocnym atutem Coqa — naucz się ją wykorzystywać, dokładnie
    obserwując skutki działania każdej komendy i taktyki.

    W razie problemów z CoqIDE poszukaj pomocy w
    #<a class='link' href='https://coq.inria.fr/refman/practical-tools/coqide.html'>manualu</a>#. *)

Section constructive_propositional_logic.

(** Mechanizm sekcji nie będzie nas na razie interesował. Użyjemy go,
    żeby nie zaśmiecać głównej przestrzeni nazw. *)

Hypothesis P Q R : Prop.

(** Zapis [x : A] oznacza, że term [x] jest typu [A]. [Prop] to typ zdań
    logicznych, więc komendę tę można odczytać następująco: niech [P], [Q]
    i [R] będą zdaniami logicznymi. Używamy tej komendy, gdyż potrzebujemy
    jakichś zdań logicznych, na których będziemy operować. *)

(** ** Implikacja (TODO) *)

(* begin hide *)
(* TODO: rozumowania w przód i w tył, czyli
  [apply] i [apply ... in ...] *)
(* end hide *)

(* begin hide *)
(* rozumowanie od tyłu jest lepsze, logika jest bezmyślna *)
(* end hide *)

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

(** ** Dysjunkcja (TODO) *)

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

Lemma or_impl : ~ P \/ Q -> (P -> Q).
(* begin hide *)
Proof.
  intros. destruct H.
    cut False.
      inversion 1.
      apply H. assumption.
    assumption.
Qed.
(* end hide *)

(** ** Koniunkcja (TODO) *)

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

(** ** Prawda i fałsz (TODO) *)

(** *** Prawda *)

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

(** *** Fałsz *)

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

(* begin hide *)
(* TODO: wspomnieć, że to 0-arne wersje dysjunkcji i koniunkcji *)
(* end hide *)

(** ** Równoważność (TODO) *)

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
    rasową implikację, tak też nie musimy odwijać definicji równoważności,
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

Lemma iff_trans : (P <-> Q) -> (Q <-> R) -> (P <-> R).
(* begin hide *)
Proof.
  intros. destruct H, H0. split.
    intro. apply H0. apply H. assumption.
    intro. apply H1. apply H2. assumption.
Qed.
(* end hide *)

Lemma iff_not : (P <-> Q) -> (~ P <-> ~ Q).
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

(** ** Negacja (TODO) *)

(** W logice klasycznej negację zdania P można zinterpretować
    po prostu jako spójnik zdaniowy tworzący nowe zdanie, którego
    wartość logiczna jest przeciwna do wartości zdania P.

    Jeżeli uważnie czytałeś fragmenty dotyczące logiki klasycznej
    i konstruktywnej, dostrzegasz już zapewne, że taka definicja
    nie przejdzie w logice konstruktywnej, której interpretacja
    opiera się na dowodach, a nie wartościach logicznych. Jak więc
    konstruktywnie zdefiniować negację?

    Zauważmy, że jeżeli zdanie [P] ma dowód, to nie powinien istnieć
    żaden dowód jego negacji, [~ P]. Uzyskanie takiego dowodu oznaczałoby
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

Lemma P_notP : ~ P -> P -> False.
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

Lemma P_notP' : ~ P -> P -> 42 = 666.
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
    że [~ P] jest tak naprawdę implikacją, i zaaplikować hipotezę [H]
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

Lemma not_False : ~ False.
(* begin hide *)
Proof.
  intro. assumption.
Qed.
(* end hide *)

Lemma not_True : ~ True -> False.
(* begin hide *)
Proof.
  intro. apply H. trivial.
Qed.
(* end hide *)

(** **** Ćwiczenie (podwójna negacja) *)

(** Udowodnij poniższe twierdzenia. Zastanów się, czy można udowodnić
    [~ ~ P -> P]. *)

Lemma dbl_neg_intro : P -> ~ ~ P.
(* begin hide *)
Proof.
  unfold not. intros. apply H0. assumption.
Qed.
(* end hide *)

Lemma double_neg_elim_irrefutable :
  ~ ~ (~ ~ P -> P).
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

Lemma triple_neg_rev : ~ ~ ~ P -> ~ P.
(* begin hide *)
Proof.
  unfold not. intros. apply H. intro. apply H1. assumption.
Qed.
(* end hide *)

End constructive_propositional_logic.

(** * O implikacji nieco więcej *)

(* begin hide *)
(* TODO: czy to się do czegoś przyda? *)
(* TODO: https://en.wikipedia.org/wiki/Converse_(semantics) *)
(* TODO: https://en.wikipedia.org/wiki/Opposite_(semantics) *)
(* end hide *)

(** ** Implikacja odwrotna *)

(* begin hide *)
(* https://en.wikipedia.org/wiki/Converse_(logic) *)
(* end hide *)

(** ** Implikacja przeciwna *)

(* begin hide *)
(* https://en.wikipedia.org/wiki/Inverse_(logic) *)
(* end hide *)

(** ** Kontrapozycja *)

(* begin hide *)
(* https://en.wikipedia.org/wiki/Contraposition *)
(* end hide *)

(** * Logika a język naturalny *)

(** ** Paradoksy implikacji *)

(* begin hide *)
(** https://en.wikipedia.org/wiki/Paradoxes_of_material_implication *)
(* end hide *)

(** ** Przemienność koniunkcji a język naturalny *)

Lemma and_comm :
  forall P Q : Prop,
    P /\ Q -> Q /\ P.
(* begin hide *)
Proof.
  intros P Q H.
  destruct H as [p q].
  split.
    assumption.
    assumption.
Qed.
(* end hide *)

(** Przemienność koniunkcji wydaje się byc własnością dość oczywistą i
    nietrudno ją udowodnić, a jednak nie powinniśmy przejść obok niej
    bez podejrzliwości. Przynajmniej w kwestii języka naturalnego: nie
    zawsze Coqowe [/\] dokładnie odpowiada polskiemu "i" (ani angielskiemu
    "and"). Dwa przykłady:

    Czasem "i" jest przemienne, mimo że nie wyraża zdania logicznego.
    Dla przykładu: "ja i ty" znaczy to samo co "ty i ja". Nie są to
    jednak zdania logiczne, więc nie można wyrazić tego w Coqu za
    pomocą spójnika [/\].

    Czasem "i" nie jest przemienne, np. zdanie "otworzyłem drzwi
    i wszedłem do środka" wygląda całkiem normalnie, ale zdanie
    "wszedłem do środka i otworzyłem drzwi" jest już nieco dziwne.
    Zdania te mogą mieć potencjalnie różne znaczenie (jeżeli nie
    wierzysz, to zastanów się, czy oba poprawnie opisują sytuację,
    gdy wchodzisz do kibla), więc nie można tutaj użyć Coqowego [/\].

    Podsumowując: koniunkcja jest przemienna, ale polski spójnik "i"
    czasem nie jest przemienny, a czasem nie służy do tworzenia
    zdań logicznych, więc trzeba uważać. *)

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

(** ** Inne paradoksy autoreferencji *)

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

(** TODO:
    - paradoks Richarda
    - Hilbert-Bernays: https://en.wikipedia.org/wiki/Hilbert-Bernays_paradox
    - Barbershop: https://en.wikipedia.org/wiki/Barbershop_paradox
    - paradoks kłamcy *)

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

(** * Harmonia logiki konstruktywnej i "prawo zachowania informacji" (TODO) *)

(** * Logika intuicjonistyczna jako logika certyfikatów (TODO) *)

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

    Tutaj dodatkowa
    #<a class='link'
        href='https://github.com/wkolowski/Typonomikon/blob/master/txt/ściągi/logika.md'>
    ściąga</a>#, w nieco bardziej czytelnym formacie. A tutaj inna
    #<a class='link' href='https://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf'>
    ściąga</a>#. *)

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

(** * Kombinatory taktyk *)

(** Przyjrzyjmy się jeszcze raz twierdzeniu [iff_intro] (lekko
    zmodernizowanemu przy pomocy kwantyfikacji uniwersalnej). *)

Lemma iff_intro' :
  forall P Q : Prop,
    (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof.
  intros. split.
  - intro. apply H. assumption.
  - intro. apply H0. assumption.
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
    z biblioteki standardowej znajdziesz w
    #<a class='link' href='https://coq.inria.fr/refman/coq-tacindex.html'>
    manualu</a>#. *)

(** * Zadania (TODO) *)

(** - na koniec dać tylko te zadania, które łączą wiele spójników
    - dodać zadanie dotyczące czytania twierdzeń i dowodów
    - dodać zadania dotyczące czytania formuł (precedencja etc.) *)

(** Poniższe zadania stanowią (chyba) kompletny zbiór praw rządzących
    logiką konstruktywną (w szczególności, niektóre z zadań mogą
    pokrywać się z ćwiczeniami zawartymi w tekście). Wróć do nich za
    jakiś czas, gdy czas przetrzebi trochę twoją pamięć (np. za
    tydzień). *)

Module exercises_propositional.

Parameters P Q R S : Prop.

(** Komenda [Parameters] formalnie działa jak wprowadzenie aksjomatu,
    który w naszym przypadku brzmi "P, Q, R i S są zdaniami logicznymi".
    Taki aksjomat jest rzecz jasna zupełnie niegroźny, ale z innymi
    trzeba uważać — gdybyśmy wprowadzili aksjomat [1 = 2], to
    popadlibyśmy w sprzeczność i nie moglibyśmy ufać żadnym dowodom,
    które przeprowadzamy. *)

End exercises_propositional.

Check and_comm.
(* ===> forall P Q : Prop, P /\ Q -> Q /\ P *)

(** W praktyce komenda [Parameters] służy do tego, żeby za dużo nie
    pisać — po zamknięciu sekcji komendą [End], Coq doda do każdego
    twierdzenia znajdującego się w tej sekcji kwantyfikację uniwersalną
    po hipotezach zadeklarowanych przy pomocy [Parameters]. W naszym
    przypadku Coq dodał do [and_comm] kwantyfikację po [P] i [Q],
    mimo że nie napisaliśmy jej explicite. *)

(** * Zadania po raz drugi *)

(** Tym razem ułożymy zadania w innej kolejności, i będzie ich wincyj! *)

Module NewExercises.

Parameters
  (P Q R S : Prop)
  (P' Q' R' S' : Prop).

(** ** Kluczowe prawa *)

Lemma noncontradiction :
  (P /\ ~ P) <-> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma noncontradiction_curried :
  P -> ~ P -> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma noncontradiction_iff :
  (P <-> ~ P) <-> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_LEM :
  ~ ~ (P \/ ~ P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_reductio_ad_absurdum :
  ~ ~ (~ (P /\ ~ Q) -> (P -> Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma reductio_ad_absurdum_conv :
  (P -> Q) -> ~ (P /\ ~ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma resolution :
  (P \/ Q) /\ (~ P \/ R) -> Q \/ R.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** ** Dysjunkcja *)

(** *** Reguły *)

Lemma or_intro_l :
  P -> P \/ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_intro_r :
  Q -> P \/ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_elim :
  (P -> R) -> (Q -> R) -> (P \/ Q -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Właściwości działaniowe *)

Lemma or_True_l :
  True \/ P <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_True_r :
  P \/ True <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_False_l :
  False \/ P <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_False_r :
  P \/ False <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_True_l' :
  P -> P \/ Q <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_True_r' :
  Q -> P \/ Q <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_False_l' :
  ~ P -> P \/ Q <-> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_False_r' :
  ~ Q -> P \/ Q <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_idem :
  P \/ P <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_comm :
  P \/ Q <-> Q \/ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_assoc :
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_mon_l :
  (P -> Q) -> (R \/ P -> R \/ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_mon_r :
  (P -> Q) -> (P \/ R -> Q \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_mon :
  (P -> Q) -> (R -> S) -> P \/ R -> Q \/ S.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_or_l :
  (P \/ Q) \/ R <-> (P \/ R) \/ (Q \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_or_r :
  P \/ (Q \/ R) <-> (P \/ Q) \/ (P \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_and_l :
  (P /\ Q) \/ R <-> (P \/ R) /\ (Q \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_and_r :
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_and_l_abs :
  (P /\ Q) \/ Q <-> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_and_r_abs :
  P \/ (P /\ Q) <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_iff_l :
  ((P <-> Q) \/ R) -> ((P \/ R) <-> (Q \/ R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_iff_r :
  (P \/ (Q <-> R)) -> ((P \/ Q) <-> (P \/ R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_impl_r :
  P \/ (Q -> R) -> (P \/ Q -> P \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_or_impl_r_conv :
  ~ ~ ((P \/ Q -> P \/ R) -> P \/ (Q -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_or_impl_r_conv' :
  (P \/ Q -> P \/ R) -> ~ ~ (P \/ (Q -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_impl_l :
  (P -> Q) \/ R -> (P \/ R) -> (Q \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_or_impl_l :
  ~ ~ ((P \/ R -> Q \/ R) -> (P -> Q) \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_or_impl_l' :
  (P \/ R -> Q \/ R) -> ~ ~ ((P -> Q) \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Właściwości relacjowe *)

(** *** Pozostałe właściwości *)

Lemma or_not_l :
  ~ P \/ Q -> (P -> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_or_not_l_conv :
  ~ ~ ((P -> Q) -> ~ P \/ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_or_not_l_conv' :
  (P -> Q) -> ~ ~ (~ P \/ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** ** Koniunkcja *)

(** *** Reguły *)

Lemma and_intro :
  P -> Q -> P /\ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_elim_l :
  P /\ Q -> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_elim_r :
  P /\ Q -> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_elim :
  (P -> Q -> R) -> (P /\ Q -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Właściwości działaniowe *)

Lemma and_True_l :
  True /\ P <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_True_r :
  P /\ True <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_False_l :
  False /\ P <-> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_False_r :
  P /\ False <-> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_True_l' :
  P -> P /\ Q <-> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_True_r' :
  Q -> P /\ Q <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_False_l' :
  ~ P -> P /\ Q <-> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_False_r' :
  ~ Q -> P /\ Q <-> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_idem :
  P /\ P <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_comm :
  P /\ Q <-> Q /\ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_assoc :
  P /\ (Q /\ R) <-> (P /\ Q) /\ R.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_mon_l :
  (P -> Q) -> (R /\ P -> R /\ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_mon_r :
  (P -> Q) -> (P /\ R -> Q /\ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_mon :
  (P -> Q) -> (R -> S) -> P /\ R -> Q /\ S.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_and_l :
  (P /\ Q) /\ R <-> (P /\ R) /\ (Q /\ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_and_r :
  P /\ (Q /\ R) <-> (P /\ Q) /\ (P /\ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_or_l :
  (P \/ Q) /\ R <-> (P /\ R) \/ (Q /\ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_or_r :
  P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_or_l_abs :
  (P \/ Q) /\ Q <-> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_or_r_abs :
  P /\ (P \/ Q) <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_iff_l :
  ((P <-> Q) /\ R) -> ((P /\ R) <-> (Q /\ R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_iff_r :
  (P /\ (Q <-> R)) -> ((P /\ Q) <-> (P /\ R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Właściwości relacjowe *)

(** *** Pozostałe właściwości *)

Lemma and_not_r :
  P /\ ~ Q -> ~ (P -> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_and_not_r_conv :
  ~ ~ (~ (P -> Q) -> P /\ ~ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_and_not_r_conv' :
  ~ (P -> Q) <-> ~ ~ (P /\ ~ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** ** Równoważność *)

(** *** Reguły *)

Lemma iff_intro :
  (P -> Q) -> (Q -> P) -> P <-> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_elim_l :
  (P <-> Q) -> (P -> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_elim_r :
  (P <-> Q) -> (Q -> P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_elim :
  ((P -> Q) -> (Q -> P) -> R) -> ((P <-> Q) -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Właściwości działaniowe *)

Lemma iff_True_l :
  (True <-> P) <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_True_r :
  P <-> True <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_False_l :
  False <-> P <-> ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_False_r :
  P <-> False <-> ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_True_l' :
  P -> (P <-> Q) <-> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_True_r' :
  Q -> (P <-> Q) <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_False_l' :
  ~ P -> (P <-> Q) <-> ~ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_False_r' :
  ~ Q -> (P <-> Q) <-> ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_refl :
  (P <-> P) <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_comm :
  (P <-> Q) <-> (Q <-> P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_iff_assoc :
  ~ ~ ((P <-> (Q <-> R)) <-> ((P <-> Q) <-> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Właściwości relacjowe *)

Lemma iff_refl' : P <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_symm : (P <-> Q) <-> (Q <-> P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_trans : (P <-> Q) -> (Q <-> R) -> (P <-> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Pozostałe właściwości *)

Lemma Irrefutable_iff_not :
  ~ ~ ((~ P <-> ~ Q) -> (P <-> Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_not_conv :
  (P <-> Q) -> (~ P <-> ~ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_not :
  (~ P <-> ~ Q) <-> ~ ~ (P <-> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_iff_spec :
  ~ ~ ((P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_iff_spec' :
  (P <-> Q) -> ~ ~ ((P /\ Q) \/ (~ P /\ ~ Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_spec_conv :
  (P /\ Q) \/ (~ P /\ ~ Q) -> (P <-> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Bardzo nudne właściwości *)

Lemma impl_pres_iff :
  (P <-> P') -> (Q <-> Q') -> (P -> Q) <-> (P' -> Q').
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma or_pres_iff :
  (P <-> P') -> (Q <-> Q') -> P \/ Q <-> P' \/ Q'.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma and_pres_iff :
  (P <-> P') -> (Q <-> Q') -> P /\ Q <-> P' /\ Q'.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma iff_pres_iff :
  (P <-> P') -> (Q <-> Q') -> (P <-> Q) <-> (P' <-> Q').
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_pres_iff :
  (P <-> P') -> ~ P <-> ~ P'.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** ** Implikacja *)

(** *** Reguły *)

Lemma impl_intro :
  (P -> Q) -> P -> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_elim :
  P -> (P -> Q) -> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Właściwości działaniowe *)

Lemma impl_True_l :
  (True -> P) <-> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_True_r :
  (P -> True) <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_False_l :
  (False -> P) <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_False_r :
  (P -> False) <-> ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_True_l' :
  P -> (P -> Q) <-> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_True_r' :
  Q -> (P -> Q) <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_False_l' :
  ~ P -> (P -> Q) <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_False_r' :
  ~ Q -> (P -> Q) <-> ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_refl :
  (P -> P) <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_mon_l :
  (P -> Q) -> ((R -> P) -> (R -> Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_antimon_r :
  (P -> Q) -> ((Q -> R) -> (P -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_bimon :
  (P -> Q) -> (R -> S) -> ((Q -> R) -> (P -> S)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_impl_r :
  (P -> (Q -> R)) <-> (P -> Q) -> (P -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_impl_or_r :
  ~ ~ ((P -> Q \/ R) -> (P -> Q) \/ (P -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_impl_or_r' :
  (P -> Q \/ R) -> ~ ~ ((P -> Q) \/ (P -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_or_r_conv :
  (P -> Q) \/ (P -> R) -> (P -> Q \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_impl_and_l' :
  ~ ~ (((P /\ Q) -> R) -> (P -> R) \/ (Q -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_impl_and_l'' :
  ((P /\ Q) -> R) -> ~ ~ ((P -> R) \/ (Q -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_and_l'_conv :
  (P -> R) \/ (Q -> R) -> ((P /\ Q) -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_and_r :
  (P -> Q /\ R) <-> (P -> Q) /\ (P -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_iff_r :
  (P -> (Q <-> R)) -> ((P -> Q) <-> (P -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Właściwości relacjowe *)

Lemma impl_refl' : P -> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_trans : (P -> Q) -> (Q -> R) -> (P -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_antisym : (P -> Q) -> (Q -> P) -> (P <-> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Pozostałe właściwości *)

Lemma weakening :
  P -> Q -> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_and_l :
  (P /\ Q -> R) <-> (P -> Q -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_or_l :
  (P \/ Q -> R) <-> (P -> R) /\ (Q -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma contraposition :
  (P -> Q) -> (~ Q -> ~ P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_contraposition_conv :
  ~ ~ ((~ Q -> ~ P) -> (P -> Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_contraposition_conv' :
  (~ Q -> ~ P) -> ~ ~ (P -> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_not_r :
  (P -> ~ Q) -> (Q -> ~ P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_impl_not_l :
  ~ ~ ((~ P -> Q) -> (~ Q -> P)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_impl_not_l' :
  (~ P -> Q) -> ~ ~ (~ Q -> P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_impl_converse :
  ~ (P -> Q) -> (Q -> P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma impl_permute :
  (P -> Q -> R) -> (Q -> P -> R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** ** Negacja *)

(** *** Reguły *)

Lemma not_intro :
  (P -> False) -> ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_intro_wiki :
  (P -> Q) -> (P -> ~ Q) -> ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** Z jakiegoś powodu Wikipedia (i parę innych źródeł) nazywa powyższe prawem
    wprowadzania negacji... nie wiem dlaczego.  *)

Lemma not_elim :
  ~ P -> P -> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Negacja stałych i spójników *)

Lemma not_True :
  ~ True <-> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_False :
  ~ False <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_or :
  ~ (P \/ Q) <-> ~ P /\ ~ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_not_and :
  ~ ~ (~ (P /\ Q) -> ~ P \/ ~ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_and_conv :
  ~ P \/ ~ Q -> ~ (P /\ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_and :
  ~ (P /\ Q) <-> ~ ~ (~ P \/ ~ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_not_impl :
  ~ ~ (~ (P -> Q) -> P /\ ~ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_impl_conv :
  P /\ ~ Q -> ~ (P -> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_impl :
  ~ (P -> Q) <-> ~ ~ (P /\ ~ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_not_not :
  ~ ~ (~ ~ P -> P).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_not_conv :
  P -> ~ ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Podwójna negacja *)

Lemma not_not_True :
  ~ ~ True <-> True.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_not_False :
  ~ ~ False <-> False.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_not_impl :
  ~ ~ (P -> Q) <-> ~ ~ P -> ~ ~ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_not_or :
  ~ ~ P \/ ~ ~ Q -> ~ ~ (P \/ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_not_and :
  ~ ~ (P /\ Q) <-> ~ ~ P /\ ~ ~ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Potrójna negacja *)

Lemma not_not_not :
  ~ ~ ~ P <-> ~ P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Pozostałe właściwości *)

Lemma reductio_ad_absurdum' :
  ~ (P /\ ~ Q) <-> ~ ~ (P -> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** ** Pozostałe mało istotne prawa *)

Lemma Irrefutable_exchange :
  ~ ~ ((~ P \/ Q) /\ (P \/ R) -> (P /\ Q) \/ (~ P /\ R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_exchange' :
  (~ P \/ Q) /\ (P \/ R) -> ~ ~ ((P /\ Q) \/ (~ P /\ R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma exchange_conv :
  (P /\ Q) \/ (~ P /\ R) -> (~ P \/ Q) /\ (P \/ R).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma isolation :
  (P /\ ~ Q) \/ (P /\ Q) -> P.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_isolation_conv :
 ~ ~ (P -> (P /\ ~ Q) \/ (P /\ Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_isolation_conv' :
  P -> ~ ~ ((P /\ ~ Q) \/ (P /\ Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma dd_and_or_r :
  P /\ (~ P \/ Q) <-> P /\ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** Uwaga: [dd] to skrót od ang. destructive dilemma (chyba). *)

Lemma dd_and_impl_r :
  P /\ (P -> Q) <-> P /\ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma dd_or_and_r :
  P \/ (~ P /\ Q) -> P \/ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_dd_or_and_r_conv :
  ~ ~ (P \/ Q -> P \/ (~ P /\ Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_dd_or_and_r_conv' :
  P \/ Q -> ~ ~ (P \/ (~ P /\ Q)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_dd_or_impl_r :
  ~ ~ (P \/ (~ P -> Q) -> P \/ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_dd_or_impl_r' :
  P \/ (~ P -> Q) -> ~ ~ (P \/ Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma dd_or_impl_r_conv :
  P \/ Q -> P \/ (~ P -> Q).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma dd_impl_or_r :
  P -> (~ P \/ Q) <-> P -> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma dd_impl_or_l :
  (P \/ Q) -> Q <-> P -> Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

(** *** Wesołe podwójnie zanegowane prawa *)

Lemma Irrefutable_Godel_Dummet :
  ~ ~ ((P -> Q) \/ (Q -> P)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma Irrefutable_fully_disjunctive_reasoning :
  ~ ~ ((P -> Q) \/ (Q -> R)).
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

End NewExercises.