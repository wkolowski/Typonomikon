(** * C: Podstawy teorii typów - TODO *)

(** Uwaga: ten rozdział jest póki co posklejany z fragmentów innych
    rozdziałów. Czytając go, weź na to poprawkę. W szczególności zawiera on
    zadania, których nie będziesz w stanie zrobić, bo niezbędny do tego
    materiał jest póki co w kolejnym rozdziale. Możesz więc przeczytać
    część teoretyczną, a zadania pominąć (albo w ogóle pominąć cały ten
    rozdział). *)

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
    Czasami używa się też nazwy "sort", bo określenie "jest sortu" jest
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
    uniwersa, jako typy, także są termami. Jakiego zatem typu są uniwersa?
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

(** W tym podrozdziale przyjrzymy się wszystkim pięciu typom reguł. Zobaczymy
    jak wyglądają, skąd się biorą i do czego służą. Podrozdział będzie miał
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

    Powyższa reguła nazywana jest "lambda abstrakcją" (gdyż zazwyczaj jest
    zapisywana przy użyciu symbolu λ zamiast słowa kluczowego [fun], jak
    w Coqu). Nie przejmuj się, jeżeli jej. Znajomość reguł wprowadzania nie
    jest nam potrzebna, by skutecznie posługiwać się Coqiem.

    Należy też dodać, że reguła ta jest nieco uproszczona. Pełniejszy
    opis teoretyczny induktywnego rachunku konstrukcji można znaleźć
    w rozdziałach 4 i 5 manuala: https://coq.inria.fr/refman/toc.html *)

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
      przez pattern matching, ale bez rekurencji. Niektóre typy nie mają
      rekurencyjnych reguł eliminacji.
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
    możemy budować je z pattern matchingu i rekursji strukturalnej i to
    właśnie te dwie ostatnie idee są w Coqu ideami pierwotnymi. Jeżeli
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
    jakie są między nimi związki? Jedną z odpowiedzi na to pytanie dają
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
    [(fun x : A => e) t] redukuje się (symbol ≡) do [e], w którym w miejsce
    zmiennej [x] podstawiono term [t].

    Zauważ, że zarówno symbol ≡ jak i notacja [e{x/t}] są tylko nieformalnymi
    zapisami i nie mają żadnego znaczenia w Coqu.

    Nie jest tak, że dla każdego typu jest tylko jedna reguła obliczania.
    Jako, że reguły obliczania pokazują związek między regułami eliminacji
    i wprowadzania, ich ilość można przybliżyć prostym wzorem:

    ## reguł obliczania = ## reguł eliminacji * ## reguł wprowadzania,

    gdzie ## to nieformalny symbol oznaczający "ilość". W Coqowej praktyce
    zazwyczaj oznacza to, że reguł obliczania jest nieskończenie wiele,
    gdyż możemy wymyślić sobie nieskończenie wiele reguł eliminacji.
    Przykładem typu, który ma więcej niż jedną regułę obliczania dla danej
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
    a zatem ich związki z regułą eliminacji [bool_rect] będą opisywać dwie
    reguły obliczania. Pierwsza z nich mówi, że [bool_rect P x y true]
    redukuje się do [x], a druga, że [bool_rect P x y false] redukuje się do
    [y].

    Gdyby zastąpić w nich regułe [bool_rect] przez nieco prostszą regułę, w
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

    Na zakończenie wypadałoby napisać, skąd biorą się reguły obliczania. W
    nieco mniej formalnych pracach teoretycznych na temat teorii typów są
    one zazwyczaj uznawane za byty podstawowe, z których następnie wywodzi
    się reguły obliczania takich konstrukcji, jak np. [match].

    W Coqu jest na odwrót. Tak jak reguły eliminacji pochodzą od pattern
    matchingu i rekursji, tak reguły obliczania pochdzą od opisanych już
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

(** Kolejną odpowiedzią na pytanie o związki między regułami wprowadzania
    i eliminacji są reguły unikalności. Są one dualne do reguł obliczania
    i określają, w jaki sposób reguły wprowadzania działają na obiekty
    pochodzące od reguł eliminacji. Przyjrzyjmy się przykładowi. *)

(*
    A : Type, B : Type, f : A -> B
    ------------------------------
    (fun x : A => f x) ≡ f
*)

(** Powyższa reguła unikalności dla funkcji jest nazywana "redukcją eta".
    Stwierdza ona, że funkcja stworzona za pomocą abstrakcji [fun x : A],
    której ciałem jest aplikacja [f x] jest definicyjnie równa funkcji [f].
    Regułą wprowadzania dla funkcji jest oczywiście abstrakcja, a regułą
    eliminacji — aplikacja.

    Reguły unikalności różnią się jednak dość mocno od reguł obliczania,
    gdyż zamiast równości definicyjnej ≡ mogą czasem używać standardowej,
    zdaniowej równości Coqa, czyli [=]. Nie do końca pasuje też do nich
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