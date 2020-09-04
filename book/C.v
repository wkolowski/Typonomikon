(** * C: Podstawy teorii typów [TODO] *)

(* begin hide *)
(*
TODO 1: Osąd `x : A` możemy czytać jako "x jest typu A", zaś konkretnie
TODO 1: `x : nat` jako "x jest liczbą naturalną".
TODO 2: Zrobić więcej ściąg/zadań z czytania różnych rzeczy.
TODO 3: powiązanie reguł wprowadzania/eliminacji/obliczania/unikalności
TODO 3: z równoważnościami, czyli w sumie Harmonia.
TODO 3: A równoważności to nic innego jak konstrukcje uniwersalne.
TODO 4: Podkreślić gdzieś mocniej, że reguła indukcji mówi,
TODO 4: że nie ma nic poza tym, co można zrobić konstruktorami.
TODO 5: Intuicja dla reguł unikalności: dzida składa się z przeddzidzia
TODO 5: dzidy, śróddzidzia dzidy i zadzidzia dzidy.
TODO 6: Wprowadzić pojęcie "motyw eliminacji" i częściej używać.
TODO 7: Podkreślić związki teorii typów z rzeczywistością przez
TODO 7: podkreślenie kwestii silnej normalizacji.
TODO 8: Opisać parametryczność tuż po opisaniu funkcji i [Type].
*)
(* end hide *)

(** Uwaga: ten rozdział jest póki co posklejany z fragmentów innych
    rozdziałów. Czytając go, weź na to poprawkę. W szczególności zawiera on
    zadania, których nie będziesz w stanie zrobić, bo niezbędny do tego
    materiał jest póki co w kolejnym rozdziale. Możesz więc przeczytać
    część teoretyczną, a zadania pominąć (albo w ogóle pominąć cały ten
    rozdział). *)

(** * Typy i termy *)

(** Czym są termy? Są to twory o naturze syntaktycznej (składniowej),
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

(** * Typy i termy, kanoniczność i uzasadnienie reguł eliminacji *)

(** Co to są termy? Po polsku: wyrażenia. Są to napisy zbudowane według
    pewnych reguł (które będziemy chcieli poznać), które mogą oznaczać
    przeróżne rzeczy: zdania logiczne i ich dowody, programy i ich
    specyfikacje, obiekty matematyczne takie jak liczby czy funkcje,
    struktury danych takie jak napisy czy listy.

    Najważniejszym, co wiemy o każdym termie, jest jego typ. Co to jest typ?
    To taki klasyfikator, który mówi, czego możemy się po termie spodziewać -
    można liczyć za pomocą liczb, ale nie za pomocą wartości logicznych.
    Można dowodzić zdań, ale nie napisów. Można skleić ze sobą dwa napisy,
    ale nie napis i funkcję etc.

    Każdy term ma tylko jeden typ, więc każdy typ możemy sobie wyobrazić jako
    wielki worek z termami. Dla przykładu, typ [nat], czyli typ liczb
    naturalnych, to worek, w którym są takie wyrażenia, jak:
    - [42]
    - [2 + 2]
    - [10 * 10]
    - jeżeli słowo "dupa" zawiera "i", to [123], a w przeciwnym wypadku [765]
    - długość listy [[a, b, c, d, e]]

    Najważniejsze termy są nazywane elementami. Dla [nat] są to [0], [1],
    [2], [3], [4], [5] i tak dalej. Elementy wyróżnia to, że są w postaci
    normalnej (zwanej też postacią kanoniczną). Znaczy to intuicyjnie, że
    są one ostatecznymi wynikami obliczeń, np.:
    - obliczenie [42] daje [42]
    - obliczenie [2 + 2] daje [4]
    - obliczenie [10 * 10] daje [100]
    - obliczenie ... daje [765]
    - obliczenie długości listy daje [5]

    Czym dokładnie są obliczenia, dowiemy się później. Na razie wystarczy
    nam wiedzieć, że każdy term zamknięty, czyli taki, o którym wiadomo
    wystarczająco dużo, oblicza się do postaci normalnej, np. 5 + 1 oblicza
    się do 6. Jeżeli jednak czegoś nie wiadomo, to term się nie oblicza, np.
    n + 1 nie wiadomo ile wynosi, jeżeli nie wiadomo, co oznacza n.

    Podsumowując, każdy element jest termem, a każdy term oblicza się do
    postaci normalnej, czyli do elementu. *)

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
      dostrzegalna dla niewprawionego oka, ale znaczna *)

(** * Uniwersa *)

(** Jeżeli przeczytałeś uważnie sekcję "Typy i termy" z rozdziału o logice,
    zauważyłeś zapewne stwierdzenie, że typy są termami. W połączeniu ze
    stwierdzeniem, że każdy term ma swój typ, zrodzić musi się pytanie:
    jakiego typu są typy? Zacznijmy od tego, że żeby uniknąć używania mało
    poetyckiego określenia "typy typów", typy typów nazywamy uniwersami.
    Czasami używa się też nazwy "sort", bo określenie "jest sortu" jest
    znacznie krótsze, niż "należy do uniwersum" albo "żyje w uniwersum". *)

(** [Prop], jak już wiesz, jest uniwersum zdań logicznych. Jeżeli
    [x : A] oraz [A : Prop] (tzn. [A] jest sortu [Prop]), to typ
    [A] możemy interpretować jako zdanie logiczne, a term [x]
    jako jego dowód. Na przykład [I] jest dowodem zdania [True],
    tzn. [I : True], zaś term [42] nie jest dowodem [True], gdyż
    [42 : nat]. *)

Check True.
(* ===> True : Prop *)

Check I.
(* ===> I : True *)

Check 42.
(* ===> 42 : nat *)

(** O ile jednak każde zdanie logiczne jest typem, nie każdy typ jest
    zdaniem — przykładem niech będą liczby naturalne [nat]. Sortem [nat]
    jest [Set]. Niech nie zmyli cię ta nazwa: [Set] nie ma nic wspólnego
    ze zbiorami znanymi choćby z teorii zbiorów ZF.

    [Set] jest uniwersum, w którym żyją specyfikacje. Jeżeli [x : A] oraz
    [A : Set] (tzn. sortem [A] jest [Set]), to [A] możemy interpretować
    jako specyfikację pewnej klasy programów, a term [x] jako program,
    który tę specyfikację spełnia (implementuje). Na przykład [2 + 2]
    jest programem, ktory spełnia specyfikację [nat], tzn. [2 + 2 : nat],
    zaś [fun n : nat => n] nie spełnia specyfikacji [nat], gdyż
    [fun n : nat => n : nat -> nat]. *)

Check nat.
(* ===> nat : Set *)

Check 2 + 2.
(* ===> 2 + 2 : nat *)

Check fun n : nat => n.
(* fun n : nat => n : nat -> nat *)

(** Oczywiście w przypadku typu [nat] mówiene o specyfikacji jest trochę
    na wyrost, gdyż określenie "specyfikacja" kojarzy nam się z czymś,
    co określa właściwości, jakie powinien mieć spełniający ją program.
    O takich specyfikacjach dowiemy się więcej w kolejnych rozdziałach.
    Choć każda specyfikacja jest typem, to rzecz jasna nie każdy typ jest
    specyfikacją — niektóre typy są przecież zdaniami.

    Jeżeli czytasz uważnie, to pewnie wciąż czujesz niedosyt — wszakże
    uniwersa, jako typy, także są termami. Jakiego zatem typu są uniwersa?
    Przekonajmy się. *)

Check Prop.
(* ===> Prop : Type *)

Check Set.
(* ===> Set : Type *)

(** [Prop] oraz [Set] są sortu [Type]. To stwierdzenie wciąż jednak pewnie
    nie zaspakaja twojej ciekawości. Pójdźmy więc po nitce do kłębka. *)

Check Type.
(* ===> Type : Type *)

(** Zdaje się, że osiągnęliśmy kłębek i że [Type] jest typu [Type].
    Rzeczywistość jest jednak o wiele ciekawsza. Gdyby rzeczywiście
    zachodziło [Type : Type], doszłoby do paradoksu znanego jako
    paradoks Girarda (którego omówienie jednak pominiemy). Prawda
    jest inna. *)

(* Set Printing Universes. *)

(** Uwaga: powyższa komenda zadziała jedynie w konsoli (program coqtop).
    Aby osiągnąć ten sam efekt w CoqIDE, zaznacz opcję
    [View > Display universe levels]. *)

Check Type.
(* ===> Type (* Top.7 *) : Type (* (Top.7)+1 *) *)

(** Co oznacza ten dziwny napis? Otóż w Coqu mamy do czynienia nie z
    jednym, ale z wieloma (a nawet nieskończenie wieloma) uniwersami.
    Uniwersa te są numerowane liczbami naturalnymi: najniższe uniwersum
    ma numer 0, a każde kolejne o jeden większy. Wobec tego hierarchia
    uniwersów wygląda tak (użyta notacja nie jest tą, której używa Coq;
    została wymyślona ad hoc):
    - [Set] żyje w uniwersum [Type(0)]
    - [Type(0)] żyje w uniwersum [Type(1)]
    - w ogólności, [Type(i)] żyje w uniwersum [Type(i + 1)] *)

(** Aby uniknąć paradoksu, definicje odnoszące się do typów żyjących
    na różnych poziomach hierarchii muszą same bytować w uniwersum
    na poziomie wyższym niż każdy z tych, do których się odwołują.
    Aby to zapewnić, Coq musi pamiętać, na którym poziomie znajduje
    każde użycie [Type] i odpowiednio dopasowywać poziom hierarchii,
    do którego wrzucone zostaną nowe definicje.

    Co więcej, w poprzednim rozdziale dopuściłem się drobnego kłamstewka
    twierdząc, że każdy term ma dokładnie jeden typ. W pewnym sensie nie
    jest tak, gdyż powyższa hierarcha jest _kumulatywna_ — znaczy to, że
    jeśli [A : Type(i)], to także [A : Type(j)] dla i < j. Tak więc każdy
    typ, którego sortem jest [Type], nie tylko nie ma unikalnego typu/sortu,
    ale ma ich nieskończenie wiele.

    Brawo! Czytając tę sekcję, dotarłeś do króliczej nory i posiadłeś
    wiedzę tajemną, której prawie na pewno nigdy ani nigdzie nie użyjesz.
    Możemy zatem przejść do meritum. *)

(** * Pięć rodzajów reguł *)

(** Być może jeszcze tego nie zauważyłeś, ale większość logiki konstruktywnej,
    programowania funkcyjnego, a przede wszystkim teorii typów kręci się wokół
    pięciu rodzajów reguł.
    Są to reguły:
    - formacji (ang. formation rules)
    - wprowadzania (ang. introduction rules)
    - eliminacji (ang. elimination rules)
    - obliczania (ang. computation rules)
    - unikalności (ang. uniqueness principles) *)

(** W tym podrozdziale przyjrzymy się wszystkim pięciu typom reguł. Zobaczymy
    jak wyglądają, skąd się biorą i do czego służą. Podrozdział będzie miał
    charakter mocno teoretyczny. *)

(** ** Reguły formacji *)

(** Reguły formacji mówią nam, jak tworzyć typy (termy sortów [Set] i [Type])
    oraz zdania (termy sortu [Prop]). Większość z nich pochodzi z nagłówków
    definicji induktywnych. Reguła dla typu [bool] wygląda tak: *)

(*
    ----------
    bool : Set
*)

(** Ten mistyczny zapis pochodzi z publikacji dotyczących teorii typów.
    Nad kreską znajdują się przesłanki reguły, a pod kreską znajduje się
    konkluzja reguły.

    Regułę tę możemy odczytać: [bool] jest typem sortu [Set]. Postać tej
    reguły wynika wprost z definicji typu [bool]. *)

Print bool.

(* ===> Inductive bool : Set :=  true : bool | false : bool *)

(** Powyższej regule formacji odpowiada tutaj fragment [Inductive bool : Set],
    który stwierdza po prostu, że [bool] jest typem sortu [Set].

    Nie zawsze jednak reguły formacji są aż tak proste. Reguła dla produktu
    wygląda tak: *)

(*
    A : Type, B : Type
    ------------------
    prod A B : Type
*)

(** Reguła formacji dla [prod] głosi: jeżeli [A] jest typem sortu [Type]
    oraz [B] jest typem sortu [Type], to [prod A B] jest typem sortu
    [Type]. Jest ona rzecz jasna konsekwencją definicji produktu. *)

Print prod.

(* ===> Inductive prod (A B : Type) : Type :=
          pair : A -> B -> A * B *)

(** Regule odpowiada fragment [Inductive prod (A B : Type) : Type]. To,
    co w regule jest nad kreską ([A : Type] i [B : Type]), tutaj występuje
    przed dwukropkiem, po prostu jako argumentu typu [prod]. Jak widać,
    nagłówek typu induktywnego jest po prostu skompresowaną formą reguły
    formacji.

    Należy zauważyć, że nie wszystkie reguły formacji pochodzą z definicji
    induktywnych. Tak wygląda reguła formacji dla funkcji (między typami
    sortu [Type]): *)

(*
    A : Type, B : Type
    ------------------
    A -> B : Type
*)

(** Reguła nie pochodzi z definicji induktywnej, gdyż typ funkcji [A -> B]
    jest typem wbudowanym i nie jest zdefiniowany indukcyjnie. *)

(** **** Ćwiczenie *)

(** Napisz, bez podglądania, jak wyglądają reguły formacji dla [option],
    [nat] oraz [list]. Następnie zweryfikuj swoje odpowiedzi za pomocą
    komendy [Print]. *)

(* begin hide *)

(*  [option]

    A : Type
    ---------------
    option A : Type
*)

(*  [nat]

    ---------
    nat : Set
*)

(*  [list]

    A : Type
    -------------
    list A : Type
*)

(* end hide *)

(** ** Reguły wprowadzania *)

(** Reguły wprowadzania mówią nam, w jaki sposób formować termy danego
    typu. Większość z nich pochodzi od konstruktorów typów induktywnych.
    Dla typu bool reguły wprowadzania wyglądają tak: *)

(*
    -----------
    true : bool

    ------------
    false : bool
*)

(** Reguły te stwierdzają po prostu, że [true] jest termem typu [bool]
    oraz że [false] jest termem typu [bool]. Wynikają one wprost z
    definicji typu [bool] — każda z nich odpowiada jednemu konstruktorowi.

    Wobec powyższego nie powinna zaskoczyć cię reguła wprowadzania dla
    produktu: *)

(*
    A : Type, B : Type, a : A, b : B
    --------------------------------
    pair A B a b : prod A B
*)

(** Jeżeli jednak zaskoczyła cię obecność w regule [A : Type] i [B : Type],
    przyjrzyj się dokładnie typowi konstruktora [pair]: *)

Check @pair.
(* ===> pair : forall A B : Type, A -> B -> A * B *)

(** Widać tutaj jak na dłoni, że [pair] jest funkcją zależną biorącą
    cztery argumenty i zwracają wynik, którego typ jest produktem jej
    dwóch pierwszych argumentów.

    Podobnie jak w przypadku reguł formacji, nie wszystkie reguły
    wprowadzania pochodzą od konstruktorów typów induktywnych. W
    przypadku funkcji reguła wygląda mniej więcej tak: *)

(*
    Γ |- A -> B : Type, Γ; x : T |- y : B
    -------------------------------------
    Γ |- fun x => y : A -> B
*)

(** Pojawiło się tu kilka nowych rzeczy: litera Γ oznacza kontekst,
    zaś zapis Γ |- j, że osąd j zachodzi w kontekście Γ. Zapis Γ; j
    oznacza rozszerzenie kontekstu Γ poprzez dodanie do niego osądu j.

    Regułę możemy odczytać tak: jeżeli [A -> B] jest typem sortu [Type]
    w kontekście Γ i [y] jest termem typu [B] w kontekście Γ rozszerzonym
    o osąd [x : T], to [fun x => y] jest termem typu [A -> B] w kontekście
    Γ.

    Powyższa reguła nazywana jest "lambda abstrakcją" (gdyż zazwyczaj jest
    zapisywana przy użyciu symbolu λ zamiast słowa kluczowego [fun], jak
    w Coqu). Nie przejmuj się, jeżeli jej. Znajomość reguł wprowadzania nie
    jest nam potrzebna, by skutecznie posługiwać się Coqiem.

    Należy też dodać, że reguła ta jest nieco uproszczona. Pełniejszy
    opis teoretyczny induktywnego rachunku konstrukcji można znaleźć
    w manualu: https://coq.inria.fr/refman/language/cic.html *)

(** **** Ćwiczenie *)

(** Napisz (bez podglądania) jak wyglądają reguły wprowadzania dla
    [option], [nat] oraz [list]. Następnie zweryfikuj swoje odpowiedzi
    za pomocą komendy [Print]. *)

(* begin hide *)

(*  [option]

    A : Type
    -----------------
    None A : option A

    A : Type, x : A
    -----------------
    Some x : option A
*)

(*  [nat]

    -------
    0 : nat

    n : nat
    ---------
    S n : nat
*)

(*  [list]

    A : Type
    ------------
    nil A : Type

    A : Type, h : A, t : list A
    ---------------------------
    h :: t : list A
*)

(* end hide *)

(** ** Reguły eliminacji *)

(** Reguły eliminacji są w pewien sposób dualne do reguł wprowadzania.
    Tak jak reguły wprowadzania dla typu [T] służą do konstruowania
    termów typu [T] z innych termów, tak reguły eliminacji dla typu [T]
    mówią nam, jak z termów typu [T] skonstruować termy innych typów.

    Zobaczmy, jak wygląda jedna z reguł eliminacji dla typu [bool]. *)

(*
    A : Type, x : A, y : A, b : bool
    --------------------------------
    if b then x else y : A
*)

(** Reguła ta mówi nam, że jeżeli mamy typ [A] oraz dwie wartości
    [x] i [y] typu [A], a także term [b] typu [bool], to możemy
    skonstruować inną wartość typu [A], mianowicie [if b then x
    else y].

    Reguła ta jest dość prosta. W szczególności nie jest ona zależna,
    tzn. obie gałęzie [if]a muszą być tego samego typu. Przyjrzyjmy
    się nieco bardziej ogólnej regule. *)

(*
    P : bool -> Type, x : P true, y : P false, b : bool
    ----------------------------------------------------
    bool_rect P x y b : P b
*)

(** Reguła ta mówi nam, że jeżeli mamy rodzinę typów [P : bool -> Type]
    oraz termy [x] typu [P true] i [y] typu [P false], a także term [b]
    typu [bool], to możemy skonstruować term [bool_rect P x y b] typu
    [P b].

    Spójrzmy na tę regułę z nieco innej strony: *)

(*
    P : bool -> Type, x : P true, y : P false
    ----------------------------------------------------
    bool_rect P x y : forall b : bool, P b
*)

(** Widzimy, że reguły eliminacji dla typu induktywnego [T] służą do
    konstruowania funkcji, których dziedziną jest [T], a więc mówią
    nam, jak "wyeliminować" term typu [T], aby uzyskać term innego typu. 

    Reguły eliminacji występują w wielu wariantach:
    - zależnym i niezależnym — w zależności od tego, czy służą do definiowania
      funkcji zależnych, czy nie.
    - rekurencyjnym i nierekurencyjnym — te druge służą jedynie do
      przeprowadzania rozumowań przez przypadki oraz definiowania funkcji
      przez dopasowanie do wzorca, ale bez rekurencji. Niektóre typy nie
      mają rekurencyjnych reguł eliminacji.
    - pierwotne i wtórne — dla typu induktywnego [T] Coq generuje regułę
      [T_rect], którą będziemy zwać regułą pierwotną. Jej postać wynika
      wprost z definicji typu [T]. Reguły dla typów nieinduktywnych (np.
      funkcji) również będziemy uważać za pierwotne. Jednak nie wszystkie
      reguły są pierwotne — przekonamy się o tym w przyszłości, tworząc
      własne reguły indukcyjne.
*)

(** Zgodnie z zaprezentowaną klasyfikacją, pierwsza z naszych reguł jest:
    - niezależna, gdyż obie gałęzie [if]a są tego samego typu. Innymi słowy,
      definiujemy term typu [A], który nie jest zależny
    - nierekurencyjna, gdyż typ [bool] nie jest rekurencyjny i wobec tego
      może posiadać jedynie reguły nierekurencyjne
    - wtórna — regułą pierwotną dla [bool] jest [bool_rect] *)

(** Druga z naszych reguł jest:
    - zależna, gdyż definiujemy term typu zależnego [P b]
    - nierekurencyjna z tych samych powodów, co reguła pierwsza
    - pierwotna — Coq wygenerował ją dla nas automatycznie *)

(** W zależności od kombinacji powyższych cech reguły eliminacji mogą
    występować pod różnymi nazwami:
    - reguły indukcyjne są zależne i rekurencyjne. Służą do definiowania
      funkcji, których przeciwdziedzina jest sortu [Prop], a więc do
      dowodzenia zdań przez indukcję
    - rekursory to rekurencyjne reguły eliminacji, które służą do definiowania
      funkcji, których przeciwdziedzina jest sortu [Set] lub [Type] *)

(** Nie przejmuj się natłokiem nazw ani rozróżnień. Powyższą klasyfikację
    wymyśliłem na poczekaniu i nie ma ona w praktyce żadnego znaczenia.

    Zauważmy, że podobnie jak nie wszystkie reguły formacji i wprowadzania
    pochodzą od typów induktywnych, tak i nie wszystkie reguły eliminacji
    od nich pochodzą. Kontrprzykładem niech będzie reguła eliminacji dla
    funkcji (niezależnych): *)

(*
    A : Type, B : Type, f : A -> B, x : A
    -------------------------------------
    f x : B
*)

(** Reguła ta mówi nam, że jeżeli mamy funkcję [f] typu [A -> B] oraz
    argument [x] typu [A], to aplikacja funkcji [f] do argumentu [x]
    jest typu [B].

    Zauważmy też, że mimo iż reguły wprowadzania i eliminacji są w pewien
    sposób dualne, to istnieją między nimi różnice.

    Przede wszystkim, poza regułami wbudowanymi, obowiązuje prosta zasada:
    jeden konstruktor typu induktywnego — jedna reguła wprowadzania. Innymi
    słowy, reguły wprowadzania dla typów induktywnych pochodzą bezpośrednio
    od konstruktorów i nie możemy w żaden sposób dodać nowych. Są one w
    pewien sposób pierwotne i nie mamy nad nimi (bezpośredniej) kontroli.

    Jeżeli chodzi o reguły eliminacji, to są one, poza niewielką ilością
    reguł pierwotnych, w pewnym sensie wtórne —
    możemy budować je z dopasowania do wzorca i rekursji strukturalnej i
    to właśnie te dwie ostatnie idee są w Coqu ideami pierwotnymi. Jeżeli
    chodzi o kontrolę, to możemy swobodnie dodawać nowe reguły eliminacji
    za pomocą twierdzeń lub definiując je bezpośrednio.

    Działanie takie jest, w przypadku nieco bardziej zaawansowanych
    twierdzeń niż dotychczas widzieliśmy, bardzo częste. Ba! Częste
    jest także tworzenie reguł eliminacji dla każdej funkcji z osobna,
    perfekcyjnie dopasowanych do kształtu jej rekursji. Jest to nawet
    bardzo wygodne, gdyż Coq potrafi automatycznie wygenerować dla nas
    takie reguły.

    Przykładem niestandardowej reguły może być reguła eliminacji dla
    list działająca "od tyłu": *)

(*
    A : Type, P : list A -> Prop,
    H : P [[]],
    H' : forall (h : A) (t : list A), P t -> P (t ++ [[h]])
    -------------------------------------------------------------
    forall l : list A, P l
*)

(** Póki co wydaje mi się, że udowodnienie słuszności tej reguły będzie dla
    nas za trudne. W przyszłości na pewno napiszę coś więcej na temat reguł
    eliminacji, gdyż ze względu na swój "otwarty" charakter są one z punktu
    widzenia praktyki najważniejsze.

    Tymczasem na otarcie łez zajmijmy się inną, niestandardową regułą dla
    list. *)

(** **** Ćwiczenie *)

(** Udowodnij, że reguła dla list "co dwa" jest słuszna. Zauważ, że komenda
    [Fixpoint] może służyć do podawania definicji rekurencyjnych nie tylko
    "ręcznie", ale także za pomocą taktyk.

    Wskazówka: użycie hipotezy indukcyjnej [list_ind_2] zbyt wcześnie
    ma podobne skutki co wywołanie rekurencyjne na argumencie, który
    nie jest strukturalnie mniejszy. *)

Module EliminationRules.

Require Import List.
Import ListNotations.

Fixpoint list_ind_2
  (A : Type) (P : list A -> Prop)
  (H0 : P []) (H1 : forall x : A, P [x])
  (H2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
    (l : list A) : P l.
(* begin hide *)
Proof.
  destruct l as [| x [| y t]]; auto.
  apply H2. apply list_ind_2; auto.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Napisz funkcję [apply], odpowiadającą regule eliminacji dla funkcji
    (niezależnych). Udowodnij jej specyfikację.

    Uwaga: notacja "$$" na oznaczenie aplikacji funkcji pochodzi z języka
    Haskell i jest tam bardzo często stosowana, gdyż pozwala zaoszczędzić
    stawiania zbędnych nawiasów. *)

(* begin hide *)
Definition apply {A B : Type} (f : A -> B) (x : A) : B := f x.
(* end hide *)

Notation "f $ x" := (apply f x) (at level 5).

Theorem apply_spec :
  forall (A B : Type) (f : A -> B) (x : A), f $ x = f x.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

End EliminationRules.

(** ** Reguły obliczania *)

(** Poznawszy reguły wprowadzania i eliminacji możemy zadać sobie pytanie:
    jakie są między nimi związki? Jedną z odpowiedzi na to pytanie dają
    reguły obliczania, które określają, w jaki sposób reguły eliminacji
    działają na obiekty stworzone za pomocą reguł wprowadzania. Zobaczmy
    o co chodzi na przykładzie. *)

(*
    A : Type, B : Type, x : A |- e : B, t : A
    -----------------------------------------
    (fun x : A => e) t ≡ e{x/t}
*)

(** Powyższa reguła nazywa się "redukcja beta". Mówi ona, jaki efekt ma
    aplikacja funkcji zrobionej za pomocą lambda abstrakcji do argumentu,
    przy czym aplikacja jest regułą eliminacji dla funkcji, a lambda
    abstrakcja — regułą wprowadzania.

    Możemy odczytać ją tak: jeżeli [A] i [B] są typami, zaś [e] termem
    typu [B], w którym występuje zmienna wolna [x] typu [A], to wyrażenie
    [(fun x : A => e) t] redukuje się (symbol ≡) do [e], w którym w miejsce
    zmiennej [x] podstawiono term [t].

    Zauważ, że zarówno symbol ≡ jak i notacja [e{x/t}] są tylko nieformalnymi
    zapisami i nie mają żadnego znaczenia w Coqu.

    Nie jest tak, że dla każdego typu jest tylko jedna reguła obliczania.
    Jako, że reguły obliczania pokazują związek między regułami eliminacji
    i wprowadzania, ich ilość można przybliżyć prostym wzorem:

    ## reguł obliczania = ## reguł eliminacji * ## reguł wprowadzania,

    gdzie ## to nieformalny symbol oznaczający "ilość". W Coqowej praktyce
    zazwyczaj oznacza to, że reguł obliczania jest nieskończenie wiele,
    gdyż możemy wymyślić sobie nieskończenie wiele reguł eliminacji.
    Przykładem typu, który ma więcej niż jedną regułę obliczania dla danej
    reguły eliminacji, jest [bool]: *)

(*
    P : bool -> Type, x : P true, y : P false
    -----------------------------------------
    bool_rect P x y true ≡ x

    P : bool -> Type, x : P true, y : P false
    -----------------------------------------
    bool_rect P x y false ≡ y
*)

(** Typ [bool] ma dwie reguły wprowadzania pochodzące od dwóch konstruktorów,
    a zatem ich związki z regułą eliminacji [bool_rect] będą opisywać dwie
    reguły obliczania. Pierwsza z nich mówi, że [bool_rect P x y true]
    redukuje się do [x], a druga, że [bool_rect P x y false] redukuje się do
    [y].

    Gdyby zastąpić w nich regułe [bool_rect] przez nieco prostszą regułę, w
    której nie występują typy zależne, to można by powyższe reguły zapisać
    tak: *)

(*
    A : Type, x : A, y : A
    -----------------------------------------
    if true then x else y ≡ x

    A : Type, x : A, y : A
    -----------------------------------------
    if false then x else y ≡ y
*)

(** Wygląda dużo bardziej znajomo, prawda?

    Na zakończenie wypadałoby napisać, skąd biorą się reguły obliczania. W
    nieco mniej formalnych pracach teoretycznych na temat teorii typów są
    one zazwyczaj uznawane za byty podstawowe, z których następnie wywodzi
    się reguły obliczania takich konstrukcji, jak np. [match].

    W Coqu jest na odwrót. Tak jak reguły eliminacji pochodzą od dopasowania
    do wzorca i rekursji, tak reguły obliczania pochdzą od opisanych już
    wcześniej reguł redukcji (beta, delta, jota i zeta), a także konwersji
    alfa. *)

(** **** Ćwiczenie *)

(** Napisz reguły obliczania dla liczb naturalnych oraz list (dla reguł
    eliminacji [nat_ind] oraz [list_ind]). *)

(* begin hide *)

(*  Liczbt naturalne.

    P : nat -> Prop, H0 : P 0, HS : forall n : nat, P n -> P (S n)
    --------------------------------------------------------------
    nat_ind P H0 HS 0 ≡ H0

    P : nat -> Prop, H0 : P 0, HS : forall n : nat, P n -> P (S n), n : nat
    -----------------------------------------------------------------------
    nat_ind P H0 HS (S n) ≡ HS n (nat_ind P H0 HS n)

    Listy.

    A : Type, P : list A -> Prop, Hnil : P [],
    Hcons : forall (h : A) (t : list A), P t -> P (h :: t)
    ------------------------------------------------------
    list_ind A P Hnil Hcons [] ≡ Hnil

    A : Type, P : list A -> Prop, Hnil : P [],
    Hcons : forall (h : A) (t : list A), P t -> P (h :: t),
    h : A, t : list A
    -------------------------------------------------------
    list_ind A P Hnil Hcons (h :: t) ≡
    Hcons h t (list_ind A P Hnil Hcons t) *)

(* end hide *)

(** ** Reguły unikalności *)

(** Kolejną odpowiedzią na pytanie o związki między regułami wprowadzania
    i eliminacji są reguły unikalności. Są one dualne do reguł obliczania
    i określają, w jaki sposób reguły wprowadzania działają na obiekty
    pochodzące od reguł eliminacji. Przyjrzyjmy się przykładowi. *)

(*
    A : Type, B : Type, f : A -> B
    ------------------------------
    (fun x : A => f x) ≡ f
*)

(** Powyższa reguła unikalności dla funkcji jest nazywana "redukcją eta".
    Stwierdza ona, że funkcja stworzona za pomocą abstrakcji [fun x : A],
    której ciałem jest aplikacja [f x] jest definicyjnie równa funkcji [f].
    Regułą wprowadzania dla funkcji jest oczywiście abstrakcja, a regułą
    eliminacji — aplikacja.

    Reguły unikalności różnią się jednak dość mocno od reguł obliczania,
    gdyż zamiast równości definicyjnej ≡ mogą czasem używać standardowej,
    zdaniowej równości Coqa, czyli [=]. Nie do końca pasuje też do nich
    stwierdzenie, że określają działanie reguł wprowadzania na reguły
    eliminacji, gdyż zamiast reguł eliminacji mogą w nich występować
    inne byty, zdefiniowane jednak za pomocą reguł eliminacji. Zobaczmy
    o co chodzi na przykładzie. *)

(*
    A : Type, B : Type, p : A * B
    --------------------------------
    (fst p, snd p) = p
*)

(** Powyższa reguła głosi, że para, której pierwszym elementem jest pierwszy
    element pary [p], a drugim elementem — drugi element pary [p], jest w
    istocie równa parze [p]. W Coqu możemy ją wyrazić (i udowodnić) tak: *)

Theorem prod_uniq :
  forall (A B : Type) (p : A * B),
    (fst p, snd p) = p.
Proof.
  destruct p. cbn. trivial.
Qed.

(** Podsumowując, reguły unikalności występują w dwóch rodzajach:
    - dane nam z góry, niemożliwe do wyrażenia bezpośrednio w Coqu i
      używające równości definicyjnej, jak w przypadku redukcji eta
      dla funkcji
    - możliwe do wyrażenia i udowodnienia w Coqu, używające zwykłej
      równości, jak dla produktów i w ogólności dla typów induktywnych *)

(** **** Ćwiczenie *)

(** Sformułuj reguły unikalności dla funkcji zależnych ([forall]), sum
    zależnych ([sigT]) i [unit] (zapisz je w notacji z poziomą kreską).
    Zdecyduj, gdzie w powyższej klasyfikacji mieszczą się te reguły.
    Jeżeli to możliwe, wyraź je i udowodnij w Coqu. *)

(* begin hide *)

(*
    A : Type, P : A -> Type, f : forall x : A, P x
    ----------------------------------------------
    (fun x : A => f x) ≡ f
*)

(*
    A : Type, P : A -> Type, p : {x : A & P x}
    ------------------------------------------
    (projT1 p, projT2 p) = p
*)

(*
    u : unit
    --------
    u = tt
*)

(** Reguła dla funkcji jest pierwszego typu, zaś reguły dla sum zależnych i
    [unit] są drugiego typu. *)

Theorem sigT_uniq :
  forall (A : Type) (P : A -> Type) (p : {x : A & P x}),
    existT P (projT1 p) (projT2 p) = p.
Proof.
  intros. destruct p. cbn. f_equal.
Qed.

Theorem unit_uniq :
  forall u : unit, u = tt.
Proof.
  destruct u. trivial.
Qed.

(* end hide *)

(** * Metateoria *)

(* begin hide *)
(** TODO: Podrozdział "Metateoria" zakłada, że omówiono wcześniej pojęcie
    TODO: postaci normalnej i silnej normalizowalności. *)
(* end hide *)

(** Zbliżamy się powoli do końca rozdziału. Z jednej strony sporo się
    nauczyliśmy, ale z drugiej strony fakt ten może budzić dość spory
    niepkój. No bo niby skąd mamy wiedzieć, że cała ta logika (i teoria
    typów też) to nie są zupełne bzdury?

    Pisząc ściślej: skąd np. mamy pewność, że logika konstruktywna nie
    jest sprzeczna, tzn. nie można w niej udowodnić [False]? A jakim
    sposobem ustalić, czy przypadkiem nie zrobiłem cię w konia pisząc,
    że nie da się udowodnić prawa wyłączonego środka?

    W niniejszym podrozdziale spróbujemy udzielić krótkiej i zwięzłej
    (a co za tym idzie, bardzo zgrubnej i średnio precyzyjnej) odpowiedzi
    na te pytania. Zacznijmy od paru kluczowych uwag. *)

(** ** Preliminaria *)

(** Najpierw będziemy chcieli udowodnić, że logika konstruktywna jest
    niesprzeczna. Co w tym przypadku oznacza słowo "udowodnić"? Aż do
    teraz dowodziliśmy twierdzeń _w Coqu/w logice konstruktywnej_, ale
    teraz będziemy chcieli coś udowodnić _o Coqu/o logice konstruktywnej_.

    Ta różnica jest bardzo istotna: jeżeli chcemy udowodnić coś o Coqu,
    to nie możemy zrobić tego w Coqu. Wynika to z jednego z twierdzeń
    Gödla, które w uproszczeniu mówi, że jeżeli dany system logiczny
    potrafi wyrazić arytmetykę liczb naturalnych (no wiesz, dodawanie,
    mnożenie i takie tam), to system ten nie może udowodnić swojej
    własnej niesprzeczności.

    Jeżeli przeraża cię powyższy akapit, to... taś taś ptaszku, będzie
    dobrze. Parafrazując: żeby udowodnić, że system logiczny nie jest
    sprzeczny, musimy to zrobić w systemie logicznym, który jest od
    niego silniejszy.

    Oczywiście wnikliwy umysł wnet dostrzeże tutaj pewien problem.
    Gdy już udowodnimy w silniejszym systemie, że słabszy system
    jest niesprzeczny, to jak mamy się upewnić, czy nasze twierdzenie
    nie jest przypadkiem gówno warte, np. dlatego, że silniejszy system
    jest sprzeczny?

    W tym celu wypadałoby udowodnić również niesprzeczność silniejszego
    systemu. Zgodnie z powyższym rozumowaniem trzeba w tym celu mieć
    jeszcze silniejszy system i on również powinien być niesprzeczny, bo
    inaczej z absolutnej matematycznej pewności nici.

    Myślę, że widzisz już, dokąd to wszystko zmierza. Tego typu problem
    w filozofii nazywa się _regressus ad infinitum_, co po naszemu znaczy
    po prostu "cofanie się w nieskończoność". Niestety w naszym logicznym
    kontekście nie ma on żadnego rozwiązania.

    Trochę terminologii: słabszy system (ten, którego niesprzeczności
    chcemy dowieść), bywa zazwyczaj nazywany "teorią" lub "językiem", a
    silniejszy (ten, w którym dowodzimy) to "metateoria" lub "metajęzyk".
    Dla zmylenia przeciwnika określeniem "metateoria" określa się także
    zbiór właściwości tego słabszego systemu (a zatem np. niesprzeczność
    logiki konstruktywnej jest jej właściwością metateoretyczną).

    Uwaga: nie bój się terminologii i żargonu, one nie gryzą.

    W praktyce kiedy poważni matematycy (a raczej informatycy i logicy,
    bo matematycy sensu stricto to straszne miernoty w kwestii logiki)
    chcą udowodnić niesprzeczność jakiegoś systemu formalnego, to po
    prostu nie przejmują się niesprzecznością metateorii, w której
    dowodzą. Zazwyczaj taki dowód i tak nie jest sformalizowany, więc
    zwykłe błędy w rozumowaniu są większym problemem, niż sprzeczność
    metateorii. Praktycznym uzasadnieniem na sensowność takiego
    postępowania może być to, że w ulubionej metateorii dowodzącego od
    dawna nie znaleziono sprzeczności (np. w teorii zbiorów ZFC, której
    używa się w takich przypadkach najcześciej, nie znaleziono jej przez
    100 lat, więc wydaje się być dość bezpieczna).

    Teoretycznie, co z tego wychodzi, to względny dowód niesprzeczności,
    czyli twierdzenie postaci "jeżeli metateoria jest niesprzeczna, to
    teoria jest niesprzeczna", które w praktyce traktuje się jako
    absolutny dowód niesprzeczności.

    Dobra, wystarczy już tego ględzenia. W naszym przypadku po prostu
    zignorujemy problemy filozoficzne i przyjrzymy się nieformalnemu
    dowodowi na to, że logika konstruktywna jest niesprzeczna. *)

(** ** Niesprzeczność *)

(** Dowód jest banalnie prosty. Załóżmy, że istnieje jakiś dowód fałszu.

    Przypomnijmy sobie, że Coq jest językiem silnie normalizowalnym.
    Znaczy to, że wszystkie termy obliczają się do postaci normalnej,
    czyli termu, który jest ostatecznym wynikiem obliczeń i nie może
    zostać "jeszcze bardziej obliczony".

    Ponieważ zdania są typami, to ich certyfikaty również podlegają
    prawom rządzącym obliczeniami. Jak wyglądają certyfikaty na [False]?
    Cóż, teoretycznie mogą być postaci np. [f x], gdzie [f : P -> False],
    zaś [x : P]. Prawdziwe pytanie brzmi jednak: jak wyglądają postacie
    normalne certyfikatów na [False]?

    Przypomnijmy, że dla większości typów (a zatem także dla zdań)
    termy w postaci normalnej to te, które pojawiają się w regułach
    wprowadzania i nie inaczej jest dla [False], a ponieważ [False]
    nie ma reguły wprowadzania, to nie ma żadnego certyfikatu na [False],
    który byłby w postaci normalnej.

    Ale zaraz! Zgodnie z początkowym założeniem mamy jakiś ceryfikat na
    [False], a zatem na mocy silnej normalizowalności oblicza się on do
    certyfikatu na [False] w postaci normalnej, a to oznacza sprzeczność.
    Wobec tego początkowe założenie było błędne i nie może istnieć żaden
    certyfikat na [False].

    Słowem: nie da się udowodnić fałszu, a zatem logika konstruktywna
    jest niesprzeczna. *)

(** ** Niedowodliwość prawa wyłączonego środka *)

(** Podobnie przebiega dowód na niedowodliwość prawa wyłączonego środka.
    Zacznijmy od założenia _a contrario_, że mamy certyfikat na prawo
    wyłączonego środka, czyli [LEM : forall P : Prop, P \/ ~ P].

    Ponieważ Coq jest silnie normalizowalny, to nasz certyfikat oblicza
    się do certyfikatu w postaci normalnej. Jak wygląda postać normalna
    dla naszego certyfikatu? Postacie normalne certyfikatów na implikację
    [P -> Q] są postaci [fun p : P => q], a certyfikatów na dysjunkcję
    [P \/ Q] są postaci [or_introl p] lub [or_intror q].

    Wobec tego nasz certyfikat może mieć jedną z dwóch postaci:
    [fun P : Prop => or_introl p], gdzie [p : P] to certyfikat na [p],
    lub [fun P : Prop => or_intror np], gdzie [np : ~ P] to certyfikat
    na [~ P]. Rozważmy dwa przypadki.

    Jeżeli [LEM] ma pierwszą z tych dwóch postaci, to oznacza to w
    zasadzie, że wszystkie zdania są prawdziwe! No bo patrz: jeżeli
    przyjrzymy się [LEM False], to widzimy, że przyjmuje on postać
    [or_introl p], gdzie [p] jest certyfikatem na [False], ale wiemy
    już, że [False] nie da się udowodnić.

    Podobnie gdy [LEM] ma drugą z tych postaci. Wtedy [LEM True] jest
    postaci [or_intror p], gdzie [p] to certyfikat na [True -> False],
    a zatem [p I] to certyfikat na [False], ale znów - fałszu nie da
    się udowodnić!

    Ponieważ w obu przypadkach uzyskaliśmy sprzeczność, a [LEM] nie
    może być żadnej innej postaci, konkluzja jest oczywista: początkowe
    założenie było błędne i certyfikat na prawo wyłączonego środka nie
    istnieje. *)

(** ** Konkluzja *)

(** Silna normalizowalność jest jedną z kluczowych metateoretycznych
    właściwości logik i języków programowania. Wynikają z niej nie
    tylko inne metateoretyczne właściwości tradycyjnie uznawane za
    ważniejsze, jak niesprzeczność, ale także bardziej ciekawostkowe,
    jak niedowodliwość prawa wyłączonego środka.

    Nie przejmuj się, jeżeli nie do końca (albo wcale) rozumiesz
    powyższe wywody (szczególnie preliminaria) lub dowody. Ich
    rozumienie nie jest niezbędne do skutecznego dowodzenia ani
    programowania. Ba! Wydaje mi się, że jest całkiem na odwrót:
    żeby zrozumieć je na intuicyjnym poziomie, potrzeba sporo
    praktycznego doświadczenia w programowaniu i dowodzeniu.
    Jeżeli go nabędziesz, powyższe wywody i dowody nagle staną
    się łatwe, miłe i przyjemne (i puszyste i mięciutkie!).
    Wróć do nich za jakiś, żeby się o tym przekonać. *)

(** * Parametryczność *)

(* begin hide *)

(** TODO: Odkłamać kwestię i wyjaśnić polimorfizmu.
    Najlepiej zrobić to za pomocą podziału na funkcje parametryczne
    (czyli takie, które na wszystkich typach działają tak samo) oraz
    ezoteryczną homoklasyczną magię, która wszystko to psuje. *)

(** Niech [A B : Type]. Zadajmy sobie następujące pytanie: ile jest funkcji
    typu [A -> B]? Żeby ułatwić sobie zadanie, ograniczmy się jedynie do
    typów, które mają skończoną ilość elementów.

    Nietrudno przekonać się, że ich ilość to |B|^|A|, gdzie ^ oznacza
    potęgowanie, zaś |T| to ilość elementów typu [T] (ta notacja nie ma
    nic wspólnego z Coqiem — zaadaptowałem ją z teorii zbiorów jedynie
    na potrzeby tego podrozdziału).

    Udowodnić ten fakt możesz (choć póki co nie w Coqu) posługując się
    indukcją po ilości elementów typu [A]. Jeżeli [A] jest pusty, to
    jest tylko jedna taka funkcja, o czym przekonałeś się już podczas
    ćwiczeń w podrozdziale o typie [Empty_set]. *)

(** **** Ćwiczenie *)

(** Udowodnij (nieformalnie, na papierze), że w powyższym akapicie nie
    okłamałem cię. *)

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie możliwe funkcje typu [unit -> unit], [unit -> bool]
    i [bool -> bool]. *)

(** Postawmy sobie teraz trudniejsze pytanie: ile jest funkcji typu
    [forall A : Type, A -> A]? W udzieleniu odpowiedzi pomoże nam
    parametryczność — jedna z właściwości Coqowego polimorfizmu.

    Stwierdzenie, że polimorfizm w Coqu jest parametryczny, oznacza, że
    funkcja biorąca typ jako jeden z argumentów działa w taki sam sposób
    niezależnie od tego, jaki typ przekażemy jej jako argument.

    Konsekwencją tego jest, że funkcje polimorficzne nie wiedzą (i nie
    mogą wiedzieć), na wartościach jakiego typu operują. Wobec tego
    elementem typu [forall A : Type, A -> A] nie może być funkcja, która
    np. dla typu [nat] stale zwraca [42], a dla innych typów po prostu
    zwraca przekazany jej argument.

    Stąd konkludujemy, że typ [forall A : Type, A -> A] ma tylko jeden
    element, a mianowicie polimorficzną funkcję identycznościową. *)

Definition id' : forall A : Type, A -> A :=
  fun (A : Type) (x : A) => x.

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie elementy następujących typów lub udowodnij, że
    istnienie choć jednego elementu prowadzi do sprzeczności:
    - [forall A : Type, A -> A -> A]
    - [forall A : Type, A -> A -> A -> A]
    - [forall A B : Type, A -> B]
    - [forall A B : Type, A -> B -> A]
    - [forall A B : Type, A -> B -> B]
    - [forall A B : Type, A -> B -> A * B]
    - [forall A B : Type, A -> B -> sum A B]
    - [forall A B C : Type, A -> B -> C]
    - [forall A : Type, option A -> A]
    - [forall A : Type, list A -> A] *)

Lemma no_such_fun :
  (forall A B : Type, A -> B) -> False.
Proof.
  intros. exact (X nat False 42).
Qed.

Lemma no_such_fun_2 :
  (forall A B C : Type, A -> B -> C) -> False.
Proof.
  intro H. apply (H True True); trivial.
Qed.

Lemma no_such_fun_3 :
  (forall A : Type, option A -> A) -> False.
Proof.
  intro H. apply H. exact None.
Qed.

Lemma no_such_fun_4 :
  (forall A : Type, list A -> A) -> False.
Proof.
  intro H. apply H. exact nil.
Qed.
(* end hide *)