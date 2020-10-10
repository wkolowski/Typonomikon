(** * D2: Rekursja i indukcja *)

(* begin hide *)
(*
TODO 1: Rekursja zagnieżdżona, zarówno w sensie zagnieżdżonych wywołań
TODO 1: rekurencyjnych, jak i dopasowania wyniku wywołania rekurencyjnego
TODO 2: rekursja prymitywna
TODO 3: rekursja wyższego rzędu (częściowo zaaplikowane wywołania rekurencyjne)
TODO 4: rekursja korekursjowa
TODO 5: opisać indukcję wykresową stosunkowo szybko, od razu gdy pojawi
TODO 5: się temat customowych reguł indukcyjnych
TODO 6: zbadać temat indukcji wykresowej dla złożenia funkcji (być może
TODO 6: może tu pomóc "fuzja" - taka optymalizacja jak w GHC czy gdzieś)
TODO 7: induktywna dziedzina dla funkcji niedeterministycznych zawiera także
TODO 7: informację o porządku ewaluacji
TODO 8: uogólniona funkcja McCarthy'ego: if n > k then n else f(f(n + 1, k), k)
*)
(* end hide *)

(** W poprzednim rozdziale dość dogłębnie zapoznaliśmy się z mechanizmem
    definiowania induktywnych typów i rodzin typów. Nauczyliśmy się też
    definiować funkcje operujące na ich elementach za pomocą dopasowania
    do wzorca oraz rekursji.

    Indukcja i rekursja są ze sobą bardzo ściśle powiązane. Obie opierają
    się na autoreferencji, czyli odnoszeniu się do samego siebie:
    - liczba naturalna to zero lub następnik liczby naturalnej
    - długość listy złożonej z głowy i ogona to jeden plus długość ogona *)

(** Można użyć nawet mocniejszego stwierdzenia: indukcja i rekursja są
    dokładnie tym samym zjawiskiem. Skoro tak, dlaczego używamy na jego
    opisanie dwóch różnych słów? Cóż, jest to zaszłość historyczna, jak
    wiele innych, które napotkaliśmy. Rozróżniamy zdania i typy/specyfikacje,
    relacje i rodziny typów, dowody i termy/programy etc., choć te pierwsze
    są specjalnymi przypadkami tych drugich. Podobnie indukcja pojawiła się
    po raz pierwszy jako technika dowodzenia faktów o liczbach naturalnych,
    zaś rekursja jako technika pisania programów.

    Dla jasności, terminów tych będziemy używać w następujący sposób:
    - indukcja będzie oznaczać metodę definiowania typów oraz
      metodę dowodzenia
    - rekursja będzie oznaczać metodę definiowania funkcji *)

(** W tym rozdziale zbadamy dokładniej rekursję: poznamy różne jej rodzaje,
    zobaczymy w jaki sposób za jej pomocą można zrobić własne niestandardowe
    reguły indukcyjne, poznamy rekursję (i indukcję) dobrze ufundowaną oraz
    zobaczymy, w jaki sposób połączyć indukcję i rekursję, by móc dowodzić
    poprawności pisanych przez nas funkcji wciśnięciem jednego przycisku
    (no, prawie).

    Zanim jednak to nastąpi, rzućmy okiem na rekursję z dwóch odmiennych
    perspektyw. *)

(** * Rekursja jako najlepszość *)

(** Znamy już podstawowe typy induktywne, jak liczby naturalne oraz
    listy elementów typu [A]. Wiemy też, że ich induktywność objawia
    się głównie w tym, że możemy definiować funkcje przez rekursję
    strukturalną po argumentach tych typów oraz dowodzić przez indukcję.

    W takim podejściu indukcja i sama induktywność typów induktywnych
    wydają się być czymś w rodzaju domina - wystarczy popchnąć pierwsze
    kilka kostek (przypadki bazowe) i zapewnić, że pozostałe kostki są
    dobrze ułożone (przypadki rekurencyjne), aby zainicjować reakcję
    łańcuchową, która będzie przewracać kostki w nieskończoność.

    Nie jest to jednak jedyny sposób patrzenia na typy induktywne. W tym
    podrozdziale spróbuję przedstawić inny sposób patrzenia, w którym typ
    induktywny to najlepszy typ do robienia termów o pewnym kształcie, a
    rekursja to zmiana kształtu z lepszego na gorszy, ale bardziej
    użyteczny.

    Żeby móc patrzeć z tej perspektywy musimy najpierw ustalić, czym
    jest kształt. Uwaga: "kształt" nie jest pojęciem technicznym i nie
    ma ścisłej definicji - używam tego słowa, żeby ułatwić pracę twojej
    wyobraźni.

    Czym jest kształt termu? Najprościej rzecz ujmując każdy term jest
    drzewkiem, którego korzeniem jest jakiś konstrukt językowy (stała,
    konstruktor, uprzednio zdefiniowana funkcja, dopasowanie do wzorca,
    [let], lub cokolwiek innego), a jego poddrzewa to argumenty tego
    konstruktu.

    Dla przykładu, termy typu [nat] mogą mieć takie kształty:
    - [0] - stała
    - [S (S (S 0))] - konstruktor
    - [plus 0 5], [mult 0 5] - uprzednio zdefiniowana funkcja
    - [if andb false false then 42 else S 42] - [if]
    - [match 0 with | 0 => 666 | S _ => 123] - dopasowanie do wzorca
    - [length [true; false]] - uprzednio zdefiniowana funkcja
    - [let x := Prop in 16] - [let]
    - ... i wiele, wiele innych!

    Tak wiele różnych sposobów robienia termów to niesamowite bogactwo,
    więc żeby zgodnie z przysłowiem od tego przybytku nie rozbolała nas
    głowa, musimy pomyśleć o nich w nieco bardziej jednorodny sposób.
    Rozwiązanie jest na szczęście bajecznie proste: zauważ, że wszystkie
    powyższe konstrukty językowe można po prostu zawinąć w funkcję, która
    bierze pewną liczbę argumentów (być może zero) i zwraca coś typu
    [nat].

    To jednak nie w pełni mityguje przyszły-niedoszły ból głowy. O ile
    mamy teraz jednorodny sposób myślenia o kształtach termów, to i tak
    kształtów tych mogą być olbrzymie ilości. Z tego powodu dokonamy
    samoograniczenia i zamiast o wszystkich możliwych kształtach termów
    będziemy wybiórczo skupiać naszą uwagę tylko na tych kształtach,
    które akurat będą nas interesować.

    Dla przykładu, możemy interesować się termami typu [nat] zrobionymi
    wyłącznie za pomocą:
    - konstruktorów [0] i [S]
    - konstruktora [0], stałej [1] oraz funkcji [plus 2]
    - funkcji [plus] i stałych [5] oraz [42]
    - funkcji [mult] i stałej [1]
    - funkcji [length : list nat -> nat] *)

(** **** Ćwiczenie *)

(** Narysuj jakieś nietrywialne termy typu [nat] o takich kształtach. *)

(* begin hide *)
Module wut.
Require Import List.
Import ListNotations.

Definition hehe : nat :=
  length [@length nat []; length [@length nat []; @length nat []]].
End wut.
(* end hide *)

(** **** Ćwiczenie *)

(** Liczbę [n] da się wyrazić za pomocą termu [t], jeżeli [t] oblicza
    się do [n], tzn. komenda [Compute t] daje w wyniku [n].

    Pytanie: termy o których z powyższych kształtów mogą wyrazić
    wszystkie liczby naturalne? *)

(** **** Ćwiczenie *)

(** Liczba [n] ma unikalną reprezentację za pomocą termów o danym
    kształcie, gdy jest tylko jeden term [t], który reprezentuje [n].

    Pytanie: które z powyższych sposobów unikalnie reprezentują
    wszystkie liczby naturalne? *)

(** Sporo już osiągnęliśmy w wyklarowywaniu pojęcia kształtu, ale
    zatrzymajmy się na chwilę i zastanówmy się, czy jest ono zgodne
    z naszymi intuicjami.

    Okazuje się, że otóż nie do końca, bo w naszej obecnej formulacji
    kształty [(0, plus)] oraz [(1, mult)] są różne, podczas gdy obrazki
    (narysuj je!) jasno pokazują nam, że np. [plus 0 (plus 0 0)] oraz
    [mult 1 (mult 1 1)] wyglądają bardzo podobnie, tylko nazwy są różne.

    Dlatego też modyfikujemy nasze pojęcie kształtu - teraz kształtem
    zamiast stałych i funkcji, jak [0] i [plus], nazywać będziemy typy
    tych stałych i funkcji. Tak więc kształtem termów zrobionych z [0]
    i [plus] będzie [nat] (bo [0 : nat]) i [nat -> nat -> nat] (bo
    [plus : nat -> nat -> nat]). Teraz jest już jasne, że [1] i [mult]
    dają dokładnie ten sam kształt, bo typem [1] jest [nat], zaś typem
    [mult] jest [nat -> nat -> nat].

    Zauważmy, że można nasze pojęcie kształtu jeszcze troszkę uprościć:
    - po pierwsze, każdą stałą można traktować jako funkcję biorącą
      argument typu [unit], np. możemy [0 : nat] reprezentować za pomocą
      funkcji [Z : unit -> nat] zdefiniowanej jako
      [Z := fun _ : unit => 0]
    - po drugie, funkcje biorące wiele argumentów możemy reprezentować za
      pomocą funkcji biorących jeden argument, np.
      [plus : nat -> nat -> nat] możemy reprezentować za pomocą
      [plus' : nat * nat -> nat], który jest zdefiniowany jako
      [plus' := fun '(n, m) => plus n m]
    - po trzecie, ponieważ kodziedzina wszystkich funkcji jest taka
      sama (w naszym przypadku [nat]), możemy połączyć wiele funkcji w
      jedną, np. [0] i [plus] możemy razem reprezentować jako
      [Zplus : unit + nat * nat -> nat], zdefiniowaną jako
      [Zplus := fun x => match x with | inl _ => 0 | inr (n, m) => plus n m end]

    Dzięki tym uproszczeniom (albo utrudnieniom, zależy kogo spytacie)
    możemy teraz jako kształt traktować nie funkcje albo same ich typy,
    lecz tylko jeden typ, który jest dziedziną takiej połączonej funkcji.
    Tak więc zarówno [(0, plus)] jak i [(1, mult)] są kształtu
    [unit + nat * nat]. Ma to sporo sensu: drzewa reprezentujące te termy
    są albo liściem (reprezentowanym przez [unit]), albo węzłem, który
    rozgałęzia się na dwa poddrzewa (reprezentowanym przez [nat * nat]).

    Ale to jeszcze nie wszystko. Przecież [nat] to nie jedyny typ, w
    którym można robić termy o kształcie [unit + nat * nat]. Jeżeli
    przyjrzymy się, jak wyglądają termy zrobione za pomocą ([true, andb])
    albo [(false, orb)], to okaże się, że... mają one dokładnie ten sam
    kształt, mimo że według naszej definicji ich kształt to
    [unit + bool * bool], czyli niby coś innego.

    Ostatnim stadium ewolucji naszego pojęcia kształtu jest taki oto
    zestaw definicji:
    - kształt to funkcja [F : Type -> Type]
    - realizacją kształtu [F] jest typ [X] oraz funkcja [f : F X -> X]

    Widzimy teraz, że [(0, plus)], [(1, mult)], [(true, andb)] oraz
    [(false, orb)] nie są kształtami, lecz realizacjami kształtu
    [F := fun X : Type => 1 + X * X].

    Pora powoli zmierzać ku konkluzji. Na początku powiedzieliśmy, że
    typ induktywny to najlepszy typ do robienia termów o pewnym kształcie.
    Jakim kształcie, zapytasz pewnie, i jak objawia się owa najlepszość?
    Czas się tego dowiedzieć.

    Definiując typ induktywny podajemy jego konstruktory, a całą resztę,
    czyli możliwość definiowania przez dopasowanie do wzorca i rekursję,
    reguły eliminacji etc. dostajemy za darmo. Nie dziwota więc, że to
    właśnie konstruktory są realizacją kształtu, którego dany typ jest
    najlepszym przykładem.

    Napiszmy to jeszcze raz, dla jasności: typ induktywny to najlepszy
    sposób robienia termów o kształcie realizowanym przez jego
    konstruktory.

    W naszym [nat]owym przykładzie oznacza to, że [nat] jest najlepszym
    sposobem robienia termów o kształcie [F := fun X => unit + X], czyli
    termów w kształcie "sznurków" (konstruktor [S] to taki supełek na
    sznurku, a [0] reprezentuje koniec sznurka). Są też inne realizacje
    tego sznurkowego kształtu, jak np. stała [42 : nat] i funkcja
    [plus 8 : nat -> nat] albo stała [true : bool] i funkcja
    [negb : bool -> bool], albo nawet zdanie [False : Prop] oraz
    negacja [not : Prop -> Prop], ale żadna z nich nie jest najlepsza.

    Jak objawia się najlepszość typu induktywnego? Ano, dwojako:
    - po pierwsze, objawia się w postaci rekursora, który bierze jako
      argument docelową realizację danego kształtu i przerabia term
      typu induktywnego, podmieniając najlepszą realizację na docelową
    - po drugie, rekursor jest unikalny, czyli powyższa podmiana
      realizacji odbywa się w jedyny słuszny sposób

    Żeby nie być gołosłownym, zobaczmy przykłady: *)

Fixpoint nat_rec' {X : Type} (z : X) (s : X -> X) (n : nat) : X :=
match n with
    | 0 => z
    | S n' => s (nat_rec' z s n')
end.

(** Tak wygląda rekursor dla liczb naturalnych. Widzimy, że "zmiana
    realizacji" termu o danym kształcie intuicyjnie polega na tym, że
    bierzemy term i zamieniamy [0] na [z], a [S] na [s], czyli dla
    przykładu liczba [4] (czyli [S (S (S (S 0)))]) zostanie zamieniona
    na [s (s (s (s z)))]. Jeszcze konkretniejszy przykład:
    [nat_rec' true negb] zamieni liczbę [S (S (S (S 0)))] w
    [negb (negb (negb (negb true)))]. Oczywiście term ten następnie
    oblicza się do [true]. *)

(** **** Ćwiczenie *)

(** Mamy [nat_rec' true negb : nat -> bool], a zatem zmiana realizacji
    sznurka z [(0, S)] na [(true, negb)] odpowiada sprawdzeniu jakiejś
    właściwości liczb naturalnych. Jakiej?

    Pisząc wprost: zdefiniuj bezpośrednio przez rekursję taką funkcję
    [f : nat -> bool], że [forall n : nat, nat_rec' true negb n = f n]
    (oczywiście musisz udowodnić, że wszystko się zgadza). *)

(* begin hide *)

Fixpoint even (n : nat) : bool :=
match n with
    | 0 => true
    | S n' => negb (even n')
end.

Lemma solution :
  forall n : nat,
    nat_rec' true negb n = even n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

(* end hide *)

(** Uwaga: Coq domyślnie generuje dla typu "rekursor", ale ma on na
    myśli coś innego, niż my: *)

Check nat_rec.
(* ===> nat_rec :
          forall P : nat -> Set,
            P 0 ->
            (forall n : nat, P n -> P (S n)) ->
              forall n : nat, P n *)

(** Coqowe [nat_rec] to w zasadzie to samo, co [nat_ind], czyli reguła
    indukcji, tyle że kodziedziną motywu nie jest [Prop], lecz [Set]
    (możesz myśleć, że [Set] to to samo co [Type]).

    Podobieństwo naszego [nat_rec'] oraz reguły indukcji nie jest
    przypadkowe - myślenie o typach induktywnych w przedstawiony wyżej
    sposób jest najlepszym sposobem na spamiętanie wszystkich możliwych
    reguł rekursji, indukcji i tympodobnych. A robi się to tak (naszym
    przykładem tym razem będzie typ [list A]).

    Krok pierwszy: każda lista to albo [nil : list A] albo
    [cons : A -> list A -> list A] zaaplikowany do głowy [h : A] i
    ogona [t : list A].

    Krok drugi: skoro tak, to [list A] jest najlepszym sposobem na
    robienie termów w kształcie [(nil, cons)].

    Krok trzeci: wobec tego mamy (a raczej musimy sobie zrobić)
    rekursor [list_rec'], który, gdy damy mu inną realizację kształtu
    [F := fun X => unit + A * X], to podmieni on [nil] i [cons]y w
    dowolnej liście [l] na tą inną realizację. Jego typ wygląda tak: *)

Definition list_rec'_type : Type :=
  forall
    (A : Type)        (* parametr [list] *)
    (P : Type)        (* inna realizacja kształtu - typ *)
    (n : P)           (* inna realizacja kształtu - [nil] *)
    (c : A -> P -> P) (* inna realizacja kształtu - [cons] *)
    (l : list A),     (* lista, w której chcemy zrobić podmianę *)
      P.              (* wynik podmiany *)

(** Krócej można ten typ zapisać tak: *)

Definition list_rec'_type' : Type :=
  forall A P : Type, P -> (A -> P -> P) -> list A -> P.

(** Implementacja jest banalna: *)

Fixpoint list_rec'
  {A P : Type} (n : P) (c : A -> P -> P) (l : list A) : P :=
match l with
    | nil => n (* podmieniamy [nil] na [n]... *)
    | cons h t => c h (list_rec' n c t) (* ... a [cons] na [c] *)
end.

(** Krok czwarty: żeby uzyskać regułę indukcji, bierzemy rekursor i
    zamieniamy [P : Type] na [P : list A -> Prop]. Żeby uzyskać
    najbardziej ogólną regułę eliminacji, używamy [P : list A -> Type]. *)

Definition list_ind'_type : Type :=
  forall
    {A : Type}
    {P : list A -> Prop}
    (n : P nil)
    (c : forall (h : A) (t : list A), P t -> P (cons h t))
    (l : list A), P l.

(** Oczywiście musimy też dostosować typy argumentów. Może to prowadzić
    do pojawienia się nowych argumentów. [c] w rekursorze miało typ
    [A -> P -> P]. Pierwszy argument typu [A] musimy nazwać [h], żeby
    móc go potem użyć. Ostatnie [P] to konkluzja, która musi być postaci
    [P (cons h t)], ale [t : list A] nigdzie nie ma, więc je dodajemy.
    Pierwsze [P] zmienia się w hipotezę indukcyjną [P t]. *)

(** Krok piąty: definicja reguły indukcji jest prawie taka sama jak
    poprzednio (musimy uwzględnić pojawienie się [t : list A] jako
    argumentu w [c]. Poza tym drobnym detalem zmieniają się tylko
    typy: *)

Fixpoint list_ind'
  {A : Type}
  {P : list A -> Prop}
  (n : P nil)
  (c : forall (h : A) (t : list A), P t -> P (cons h t))
  (l : list A)
    : P l :=
match l with
    | nil => n
    | cons h t => c h t (list_ind' n c t)
end.

(** Włala, mamy regułę indukcji.

    Na sam koniec wypadałoby jeszcze opisać drobne detale dotyczące
    najlepszości. Czy skoro [nat] jest najlepszym typem do robienia
    termów w kształcie sznurków, to znaczy, że inne realizacje tego
    kształtu są gorsze? I w jaki sposób objawia się ich gorszość?

    Odpowiedź na pierwsze pytanie jest skomplikowańsza niż bym chciał:
    [nat] jest najlepsze, ale inne typy też mogą być najlepsze.
    Rozważmy poniższy typ: *)

Inductive nat' : Type :=
    | Z' : nat'
    | S' : nat' -> nat'.

(** Jako, że [nat'] jest typem induktywnym, to jest najlepszym sposobem
    robienia termów w kształcie [F := fun X => unit + X]. Ale jak to?
    Przecież najlepsze dla tego kształtu jest [nat]! Tak, to prawda.
    Czy zatem [nat'] jest gorsze? Nie: oba te typy, [nat] i [nat'],
    są najlepsze.

    Wynika stąd ciekawa konkluzja: [nat'] to w zasadzie to samo co
    [nat], tylko inaczej nazwane. Fakt ten łatwo jest udowodnić:
    mając [nat]owy sznurek możemy za pomocą [nat_rec'] przerobić
    go na [nat']owy sznurek. Podobnie [nat']owy sznurek można
    za pomocą [nat'_rec'] przerobić na [nat]owy sznurek. Widać na
    oko, że obie te funkcje są swoimi odwrotnościami, a zatem typy
    [nat] i [nat'] są izomorficzne, czyli mają takie same elementy
    i takie same właściwości. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcje [f : nat -> nat'] i [g : nat -> nat'],
    które spełniają
    [forall n : nat, g (f n) = n] oraz
    [forall n : nat', f (g n) = n]. Nie musisz w tym celu używać
    [nat_rec'] ani [nat'_rec'] (no chyba, że chcesz). *)

(* begin hide *)
Module ex.

Fixpoint f (n : nat) : nat' :=
match n with
    | 0 => Z'
    | S n' => S' (f n')
end.

Fixpoint g (n : nat') : nat :=
match n with
    | Z' => 0
    | S' n' => S (g n')
end.

Lemma fg :
  forall n : nat, g (f n) = n.
Proof.
  induction n; cbn; rewrite ?IHn; reflexivity.
Qed.

Lemma gf :
  forall n : nat', f (g n) = n.
Proof.
  induction n; cbn; rewrite ?IHn; reflexivity.
Qed.

End ex.
(* end hide *)

(** Drugie pytanie brzmiało: w czym objawia się brak najlepszości innych
    realizacji danego kształtu? Odpowiedź jest prosta: skoro najlepszość
    to unikalny rekursor, to brak najlepszości oznacza brak unikalnego
    rekursora. Przeżyjmy to na przykładzie:

    Używając rekursora dla [nat] możemy podmienić [S] na negację, a
    [0] na [false], i otrzymać dzięki temu funkcję sprawdzającą, czy
    długość sznurka (czyli liczby naturalnej) jest nieparzysta. Czy
    dla innych realizacji tego samego kształtu też możemy tak zrobić?

    Nie zawsze. Rozważmy typ [unit] wraz ze stałą [tt] i funkcją
    [f := fun _ => tt], które realizują ten sam kształt co [nat],
    [0] i [S]. Zauważmy, że [tt = f tt], a zatem różne sznurki
    obliczają się do tej samej wartości. Jest to sytuacja zgoła
    odmienna od [nat]owej - różne ilości [S]ów dają różne liczby
    naturalne.

    Gdybyśmy mieli dla tej realizacji rekursor podmieniający [f] na
    jakąś funkcję [g], zaś [tt] na stałą [x], to niechybnie doszłoby
    do katastrofy. Dla przykładu, gdybyśmy próbowali tak jak wyżej
    sprawdzić, czy długość sznurka jest nieparzysta, zamieniając [tt]
    na [false], zaś [f] na [negb], to wynikiem zamiany dla [tt] byłoby
    [false], zaś dla [f tt] byłoby to [negb false = true]. To jednak
    prowadzi do sprzeczności, bo [tt = f tt]. Wyniki podmiany dla
    sznurków obliczających się do równych wartości musza być takie
    same.

    Oczywiście [unit], [tt] i [f] to bardzo patologiczna realizacja
    sznurkowego kształtu. Czy są jakieś mniej patologiczne realizacje,
    które umożliwiają podmiankę, która pozwala sprawdzić nieparzystość
    długości sznurka?

    Tak. Przykładem takiej realizacji jest... [bool], [false] i [negb]
    (a rzeczona podmianka, to w tym przypadku po prostu funkcja
    identycznościowa).

    Czy znaczy to, że [bool], [false] i [negb] to najlepsza realizacja
    sznurkowego kształtu? Nie - da się znaleźć całą masę podmianek,
    które [nat] umożliwia, a [bool], [false] i [negb] - nie (joł, sprawdź
    to - wcale nie kłamię).

    Cóż, to by było na tyle. W ramach pożegnania z tym spojrzeniem na
    typy induktywne napiszę jeszcze tylko, że nie jest ono skuteczne
    zawsze i wszędzie. Działa jedynie dla prostych typów zrobionych
    z enumeracji, rekurencji i parametrów. Żeby myśleć w ten sposób
    np. o indeksowanych rodzinach typów trzeba mieć nieco mocniejszą
    wyobraźnię. *)

(** **** Ćwiczenie *)

(** Rozważmy poniższe typy:
    - [unit]
    - [bool]
    - [option A]
    - [A * B]
    - [A + B]
    - [exists x : A, P x]
    - [nat]
    - [list A]

    Dla każdego z nich:
    - znajdź kształt, którego jest on najlepszą realizacją
    - napisz typ rekursora
    - zaimplementuj rekursor
    - zaimplementuj bezpośrednio za pomocą rekursora jakąś ciekawą
      funkcję
    - z typu rekursora wyprowadź typ reguły indukcji (oczywiście bez
      podglądania za pomocą komendy [Print]... nie myśl też o białym
      niedźwiedziu)
    - zaimplementuj regułę indukcji
    - spróbuj bezpośrednio użyć reguły indukcji, by udowodnić jakiś
      fakt na temat zaimplementowanej uprzednio za pomocą rekursora
      funkcji *)

(* begin hide *)
Module solutions.

Open Scope type.

Definition unit_shape : Type -> Type :=
  fun _ : Type => unit.

Definition unit_rec_type : Type :=
  forall A : Type, A -> unit -> A.

Definition unit_rec' {A : Type} (x : A) (_ : unit) : A := x.

Definition const_true : unit -> bool := unit_rec' true.

Definition unit_ind_type : Type :=
  forall P : unit -> Prop, P tt -> forall u : unit, P u.

Definition unit_ind'
  {P : unit -> Prop} (p : P tt) (u : unit) : P u :=
match u with
    | tt => p
end.

Definition bool_shape : Type -> Type :=
  fun _ : Type => unit + unit.

Definition bool_rec_type : Type :=
  forall P : Type, P -> P -> bool -> P.

Definition bool_rec'
  {P : Type} (t f : P) (b : bool) : P :=
match b with
    | true => t
    | false => f
end.

Definition rnegb : bool -> bool := bool_rec' false true.

Definition bool_ind_type : Type :=
  forall P : bool -> Prop,
    P true -> P false -> forall b : bool, P b.

Definition bool_ind'
  {P : bool -> Prop} (t : P true) (f : P false) (b : bool) : P b :=
match b with
    | true => t
    | false => f
end.

Definition rnegb_rnegb :
  forall b : bool, rnegb (rnegb b) = b :=
    bool_ind' eq_refl eq_refl.

Definition option_shape (A : Type) : Type -> Type :=
  fun _ : Type => option A.

Definition option_rec_type : Type :=
  forall A P : Type, P -> (A -> P) -> option A -> P.

Definition option_rec'
  {A P : Type} (n : P) (s : A -> P) (o : option A) : P :=
match o with
    | None => n
    | Some a => s a
end.

Definition option_ind_type : Type :=
  forall (A : Type) (P : option A -> Type),
    P None -> (forall a : A, P (Some a)) ->
      forall o : option A, P o.

Definition option_ind'
  {A : Type} {P : option A -> Type}
  (n : P None) (s : forall a : A, P (Some a))
  (o : option A) : P o :=
match o with
    | None => n
    | Some a => s a
end.

Definition prod_shape (A B : Type) : Type -> Type :=
  fun _ : Type => A * B.

Definition prod_rec_type : Type :=
  forall (A B P : Type), (A -> B -> P) -> A * B -> P.

Definition prod_rec'
  {A B P : Type} (f : A -> B -> P) (x : A * B) : P :=
match x with
    | (a, b) => f a b
end.

Definition rswap {A B : Type} : A * B -> B * A :=
  prod_rec' (fun a b => (b, a)).

Definition prod_ind_type : Type :=
  forall (A B : Type) (P : A * B -> Prop),
    (forall (a : A) (b : B), P (a, b)) ->
      forall x : A * B, P x.

Definition prod_ind'
  {A B : Type} {P : A * B -> Prop}
  (f : forall (a : A) (b : B), P (a, b))
  (x : A * B) : P x :=
match x with
    | (a, b) => f a b
end.

Definition rswap_rswap :
  forall {A B : Type} (x : A * B),
    rswap (rswap x) = x
  := fun {A B : Type} => prod_ind' (fun _ _ => eq_refl).

Definition sum_shape (A B : Type) : Type -> Type :=
  fun _ : Type => A + B.

Definition sum_rec_type : Type :=
  forall A B P : Type,
    (A -> P) -> (B -> P) -> A + B -> P.

Definition sum_rec'
  {A B P : Type} (f : A -> P) (g : B -> P) (x : A + B) : P :=
match x with
    | inl a => f a
    | inr b => g b
end.

Definition sswap {A B : Type} : A + B -> B + A :=
  @sum_rec' A B _ inr inl.

Definition sum_ind_type : Type :=
  forall (A B : Type) (P : A + B -> Prop),
    (forall a : A, P (inl a)) ->
    (forall b : B, P (inr b)) ->
      forall x : A + B, P x.

Definition sum_ind'
  {A B : Type} {P : A + B -> Prop}
  (l : forall a : A, P (inl a))
  (r : forall b : B, P (inr b))
  (x : A + B)
    : P x :=
match x with
    | inl a => l a
    | inr b => r b
end.

Definition sswap_sswap :
  forall (A B : Type) (x : A + B),
    sswap (sswap x) = x
  := fun A B => sum_ind' (fun _ => eq_refl) (fun _ => eq_refl).

Definition nat_shape : Type -> Type :=
  fun X : Type => unit + X.

Definition nat_rec_type : Type :=
  forall P : Type, P -> (P -> P) -> nat -> P.

Check @nat_rec'.

(** TODO: reszta tych pierdół. *)

End solutions.

(* end hide *)

(* begin hide *)
Module wuut.

Axioms
  (N : Type)
  (Z : N)
  (S : N -> N).

Definition N_rec : Type :=
  forall {X : Type} (z : X) (s : X -> X),
    {f : N -> X |
      f Z = z /\
      (forall n : N, f (S n) = s (f n)) /\
      (forall g : N -> X,
        g Z = z ->
        (forall n : N, g (S n) = s (g n)) ->
          forall n : N, g n = f n)
    }.

Definition N_ind : Type :=
  forall
    {P : N -> Type}
    (z : P Z) (s : forall n : N, P n -> P (S n)),
      {f : forall n : N, P n |
        f Z = z /\
        forall n : N, f (S n) = s n (f n)
      }.

Lemma N_ind_rec :
  N_ind -> N_rec.
Proof.
  unfold N_ind.
  intros N_ind P z s.
  destruct (N_ind (fun _ => P) z (fun _ => s)) as (f & HZ & HS).
  exists f. repeat split.
    assumption.
    assumption.
    intros g HZ' HS' n. apply (N_ind (fun n => g n = f n)).
      rewrite HZ, HZ'. reflexivity.
      intros m H. rewrite HS, HS', H. reflexivity.
Qed.

Unset Universe Checking.

Lemma N_rec_ind :
  N_rec -> N_ind.
Proof.
  unfold N_rec.
  intros N_rec P z s.
Abort.

End wuut.
(* end hide *)

(** * Reguły eliminacji (TODO) *)

(** * Jak działa taktyka [induction] (TODO) *)

(** * Rodzaje rekursji *)

(** Funkcja może w swej definicji odwoływać się do samej siebie na różne
    sposoby. Najważniejszą klasyfikacją jest klasyfikacja ze względu na
    dozwolone argumenty w wywołaniu rekurencyjnym:
    - Rekursja strukturalna to taka, w której funkcja wywołuje siebie
      na argumentach będących podtermami argumentów z obecnego wywołania.
    - W szczególności rekursja prymitywna to taka, w której funkcja wywołuje
      siebie jedynie na bezpośrednich podtermach argumentu głównego z obecnego
      wywołania.
    - Rekursja dobrze ufundowana to taka, w której funkcja wywołuje siebie
      jedynie na argumentach "mniejszych", gdzie o tym, które argumenty są
      mniejsze, a które większe, decyduje pewna relacja dobrze ufundowana.
      Intuicyjnie relacja dobrze ufundowana jest jak drabina: schodząc po
      drabinie w dół kiedyś musimy schodzenie zakończyć. Nie możemy schodzić
      w nieskończoność. *)

(** Mniej ważną klasyfikacją jest klasyfikacja ze względu na... cóż, nie
    wiem jak to ładnie nazwać:
    - Rekursja bezpośrednia to taka, w której funkcja f wywołuje siebie
      samą bezpośrednio.
    - Rekursja pośrednia to taka, w której funkcja f wywołuje jakąś inną
      funkcję g, która wywołuje f. To, że f nie wywołuje samej
      siebie bezpośrednio nie oznacza wcale, że nie jest rekurencyjna.
    - W szczególności, rekursja wzajemna to taka, w której funkcja f
      wywołuje funkcję g, a g wywołuje f.
    - Rzecz jasna rekursję pośrednią oraz wzajemną można uogólnić na dowolną
      ilość funkcji. *)

(** Oczywiście powyższe dwie klasyfikacje to tylko wierzchołek góry lodowej,
    której nie ma sensu zdobywać, gdyż naszym celem jest posługiwanie się
    rekursją w praktyce, a nie dzielenie włosa na czworo. Wobec tego
    wszystkie inne rodzaje rekursji (albo nawet wszystkie możliwe rodzaje
    w ogóle) będziemy nazywać rekursją ogólną.

    Z rekursją wzajemną zapoznaliśmy się już przy okazji badania indukcji
    wzajemnej w poprzednim rozdziale. W innych funkcyjnych językach
    programowania używa się jej zazwyczaj ze względów estetycznych, by móc
    elegancko i czytelnie pisać kod, ale jak widzieliśmy w Coqu jest ona
    bardzo upierdliwa, więc raczej nie będziemy jej używać. Skupmy się
    zatem na badaniu rekursji strukturalnej, dobrze ufundowanej i ogólnej. *)

(** **** Ćwiczenie *)

(** Przypomnij sobie podrozdział o indukcji wzajemnej. Następnie wytłumacz,
    jak przetłumaczyć definicję funkcji za pomocą rekursji wzajemnej na
    definicję, która nie używa rekursji wzajemnej. *)

(** * Rekursja prymitywna (TODO) *)

(* begin hide *)
(** Tutaj opisać to, co w Agdzie zwie się "rekursją prymitywną", czyli taką,
    która dokładnie pasuje do kształtu indukcji w typie, a zatem można ją
    bezpośrednio przetłumaczyć na regułę indukcji. Co więcej, pojęcie to
    wydaje się być całkiem użyteczne w kontekście metody Bove-Capretta oraz
    mówienia o "kształcie rekursji" czy "kształcie indukcji". *)
(* end hide *)

(** Wiemy już, że rekursja ogólna prowadzi do sprzeczności, a jedyną legalną
    formą rekursji jest rekursja prymitywna (i niektóre formy rekursji
    strukturalnej, o czym dowiemy się później). Funkcje rekurencyjne, które
    dotychczas pisaliśmy, były prymitywnie rekurencyjne, więc potrafisz
    już całkiem sprawnie posługiwać się tym rodzajem rekursji. Pozostaje
    nam zatem jedynie zbadać techniczne detale dotyczące sposobu realizacji
    rekursji prymitywnej w Coqu. W tym celu przyjrzyjmy się ponownie
    definicji dodawania: *)

Print plus.
(* plus =
   fix plus (n m : nat) {struct n} : nat :=
     match n with
     | 0 => m
     | S p => S (plus p m)
     end
        : nat -> nat -> nat *)

(** Możemy zaobserwować parę rzeczy. Pierwsza, techniczna sprawa: po
    [=] widzimy nieznany nam konstrukt [fix]. Pozwala on tworzyć
    anonimowe funkcje rekruencyjne, tak jak [fun] pozwala tworzyć
    anonimowe funkcje nierekurencyjne. Funkcje zdefiniowane komendami 
    [Fixpoint] i [Definition] są w jęzku termów Coqa reprezentowane
    odpowiednio za pomocą [fix] i [fun].

    Po drugie: za listą argumentów, a przed zwracanym typem, występuje
    adnotacja [{struct n}]. Wskazuje ona, który z argumentów funkcji
    jest argumentem głównym. Dotychczas gdy definiowaliśmy funkcje
    rekurencyjne nigdy nie musieliśmy jej pisać, bo Coq zawsze domyślał
    się, który argument ma być główny. W poetyckiej polszczyźnie argument
    główny możemy wskazać mówiąc np., że "funkcja plus zdefiniowana jest
    przez rekursję po pierwszym argumencie" albo "funkcja plus zdefinowana
    jest przez rekursję po n".

    Czym jest argument główny? Spróbuję wyjasnić to w sposób operacyjny:
    - jako argument główny możemy wskazać dowolny argument, którego typ
      jest induktywny
    - Coq wymusza na nas, aby argumentem głównym wywołania rekurencyjnego
      był podterm argumentu głównego z obecnego wywołania

    Dlaczego taki zabieg chroni nas przed sprzecznością? Przypomnij sobie,
    że termy typów induktywnych muszą być skończone. Parafrazując: są to
    drzewa o skończonej wysokości. Ich podtermy są od nich mniejsze, więc
    w kolejnych wywołaniach rekurencyjnych argument główny będzie malał,
    aż w końcu jego rozmiar skurczy się do zera. Wtedy rekursja zatrzyma
    się, bo nie będzie już żadnych podtermów, na których można by zrobić
    wywołanie rekurencyjne.

    Żeby lepiej zrozumieć ten mechanizm, zbadajmy najpierw relację bycia
    podtermem dla typów induktywnych. Relację tę opisują dwie proste zasady:
    - po pierwsze, jeżeli dany term został zrobiony jakimś konstruktorem,
      to jego podtermami są rekurencyjne argumenty tego konstruktora.
      Przykład: [0] jest podtermem [S 0], zaś [nil] podtermem [cons 42 nil].
    - po drugie, jeżeli [t1] jest podtermem [t2], a [t2] podtermem [t3],
      to [t1] jest podtermem [t3] — własność ta nazywa się przechodniością.
      Przykład: [S 0] jest podtermem [S (S 0)], a zatem [0] jest podtermem
      [S (S 0)]. Podobnie [nil] jest podtermem [cons 666 (cons 42 nil)] *)

(** **** Ćwiczenie *)

(** Zdefiniuj relacje bycia podtermem dla liczb naturalnych i list. *)

(* begin hide *)
Inductive subterm_nat : nat -> nat -> Prop :=
    | subterm_nat_S : forall n : nat, subterm_nat n (S n)
    | subterm_nat_trans' : forall x y z : nat,
        subterm_nat x y -> subterm_nat y z -> subterm_nat x z.

Inductive subterm_list {A : Type} : list A -> list A -> Prop :=
    | subterm_list_cons : forall (h : A) (t : list A),
        subterm_list t (h :: t)
    | subterm_list_trans' : forall x y z : list A,
        subterm_list x y -> subterm_list y z -> subterm_list x z.

Inductive trans_clos {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | trans_clos_step : forall x y : A, R x y -> trans_clos R x y
    | trans_clos_trans : forall x y z : A,
        R x y -> trans_clos R y z -> trans_clos R x z.

Inductive subterm_nat_base : nat -> nat -> Prop :=
    | subterm_nat_base_c : forall n : nat, subterm_nat_base n (S n).

Definition subterm_nat' : nat -> nat -> Prop :=
    trans_clos subterm_nat_base.

Inductive subterm_list_base {A : Type} : list A -> list A -> Prop :=
    | subterm_list_base_c : forall (h : A) (t : list A),
        subterm_list_base t (h :: t).

Definition subterm_list' {A : Type} : list A -> list A -> Prop :=
    trans_clos subterm_list_base.
(* end hide *)

(** Udowodnij, że przytoczone wyżej przykłady nie są oszustwem.
    Komenda [Goal] jest wygodna, gdyż używając jej nie musimy
    nadawać twierdzeniu nazwy. Użycie [Qed] zapisze twierdzenie
    jako [Unnamed_thm], [Unnamed_thm0], [Unnamed_thm1] etc. *)

Goal subterm_nat 0 (S 0).
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

Goal subterm_list nil (cons 42 nil).
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

(* begin hide *)
Goal subterm_list' nil (cons 42 nil).
Proof. do 2 constructor. Qed.
(* end hide *)

(* begin hide *)
Goal subterm_nat' 0 (S 0).
Proof. do 2 constructor. Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij, że relacje [subterm_nat] oraz [subterm_list] są antyzwrotne
    i przechodnie. Uwaga: to może być całkiem trudne. *)

(* begin hide *)
Require Import Arith.

Lemma subterm_nat_lt :
  forall n m : nat, subterm_nat n m -> n < m.
Proof.
  induction 1.
    apply le_n.
    apply lt_trans with y; assumption.
Qed.
(* end hide *)

Lemma subterm_nat_antirefl :
  forall n : nat, ~ subterm_nat n n.
(* begin hide *)
Proof.
  do 2 intro. apply Nat.lt_irrefl with n. apply subterm_nat_lt. assumption.
Qed.
(* end hide *)

Lemma subterm_nat_trans :
  forall a b c : nat,
    subterm_nat a b -> subterm_nat b c -> subterm_nat a c.
(* begin hide *)
Proof.
  intros. econstructor; eassumption.
Qed.
(* end hide *)

(* begin hide *)
Lemma subterm_nat'_lt :
  forall n m : nat, subterm_nat' n m -> n < m.
Proof.
  induction 1.
    inversion H; subst. apply le_n.
    inversion H; subst. apply lt_trans with (S x).
      apply Nat.lt_succ_diag_r.
      assumption.
Qed.

Lemma subterm_nat'_antirefl :
  forall n : nat, ~ subterm_nat' n n.
Proof.
  do 2 intro. apply Nat.lt_irrefl with n. apply subterm_nat'_lt. assumption.
Qed.

Lemma subterm_nat'_trans :
  forall a b c : nat,
    subterm_nat' a b -> subterm_nat' b c -> subterm_nat' a c.
Proof.
  intros a b c H. revert c. induction H; intros.
    apply trans_clos_trans with y; assumption.
    apply trans_clos_trans with y.
      assumption.
      apply IHtrans_clos. assumption.
Qed.
(* end hide *)

(* begin hide *)
Lemma subterm_list_length :
  forall (A : Type) (l1 l2 : list A),
    subterm_list l1 l2 -> length l1 < length l2.
Proof.
  induction 1; cbn.
    apply le_n.
    eapply lt_trans; eassumption.
Qed.
(* end hide *)

Lemma subterm_list_antirefl :
  forall (A : Type) (l : list A), ~ subterm_list l l.
(* begin hide *)
Proof.
  repeat intro. eapply Nat.lt_irrefl, subterm_list_length. eassumption.
Qed.
(* end hide *)

Lemma subterm_list_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    subterm_list l1 l2 -> subterm_list l2 l3 ->
      subterm_list l1 l3.
(* begin hide *)
Proof.
  intros. eapply subterm_list_trans'; eassumption.
Qed.
(* end hide *)

(* begin hide *)
Lemma subterm_list'_length :
  forall (A : Type) (l1 l2 : list A),
    subterm_list' l1 l2 -> length l1 < length l2.
Proof.
  induction 1.
    inversion H; subst. apply le_n.
    inversion H; subst; cbn in *. apply lt_trans with (length (h :: x)).
      cbn. apply le_n.
      cbn. exact IHtrans_clos.
Qed.

Lemma subterm_list'_antirefl :
  forall (A : Type) (l : list A), ~ subterm_list' l l.
Proof.
  repeat intro. eapply Nat.lt_irrefl, subterm_list'_length. eassumption.
Qed.

Lemma subterm_list'_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    subterm_list' l1 l2 -> subterm_list' l2 l3 -> subterm_list' l1 l3.
Proof.
  intros A l1 l2 l3 H. revert l3. induction H; intros.
    apply trans_clos_trans with y; assumption.
    apply trans_clos_trans with y.
      assumption.
      apply IHtrans_clos. assumption.
Qed.
(* end hide *)

(** Jak widać, podtermy liczby naturalnej to liczby naturalne, które są od
    niej mniejsze, zaś podtermy listy to jej ogon, ogon ogona i tak dalej.
    Zero i lista pusta nie mają podtermów, gdyż są to przypadki bazowe,
    pochodzące od konstruktorów, które nie mają argumentów rekurencyjnych.

    Dla każdego typu induktywnego możemy zdefiniować relację bycia podtermem
    podobną do tych dla liczb naturalnych i list. Zauważmy jednak, że nie
    możemy za jednym zamachem zdefiniować relacji bycia podtermem dla
    wszystkich typów induktywnych, gdyż nie możemy w Coqu powiedzieć czegoś
    w stylu "dla wszystkich typów induktywnych". Możemy powiedzieć jedynie
    "dla wszystkich typów".

    Coq nie generuje jednak automatycznie takiej relacji, gdy definiujemy
    nowy typ induktywny. W jaki zatem sposób Coq sprawdza, czy jeden term
    jest podtermem drugiego? Otóż... w sumie, to nie sprawdza. Rzućmy okiem
    na następujący przykład: *)

Fail Fixpoint weird (n : nat) : unit :=
match n with
    | 0 => tt
    | S n' => weird 0
end.

(** Definicja zdaje się być poprawna: [0] to przypadek bazowy, a gdy [n]
    jest postaci [S n'], wywołujemy funkcję rekurencyjnie na argumencie
    [0]. [0] jest podtermem [S n'], a zatem wszystko powinno być dobrze.
    Dostajemy jednak następujący komunikat o błędzie: *)

(* Recursive definition of weird is ill-formed.
   In environment
   weird : nat -> unit
   n : nat
   n' : nat
   Recursive call to weird has principal argument equal to 
   "0" instead of "n'". *)

(** Komunikat ten głosi, że argumentem głównym wywołania rekurencyjnego jest
    [0], podczas gdy powinno być nim [n']. Wynika stąd jasno i wyraźnie, że
    jedynymi legalnymi argumentami w wywołaniu rekurencyjnym są te podtermy
    argumentu głównego, które zostają ujawnione w wyniku dopasowania do
    wzorca. Coq nie jest jednak głupi - jest głupszy, niż ci się wydaje, o
    czym świadczy poniższy przykład. *)

Fail Fixpoint fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n') => fib n' + fib (S n')
end.

(** Funkcja ta próbuje policzyć n-tą liczbę Fibonacciego:
    https://en.wikipedia.org/wiki/Fibonacci_number, ale
    słabo jej to wychodzi, gdyż dostajemy następujący błąd: *)

(* Recursive definition of fib is ill-formed.
   In environment
   fib : nat -> nat
   n : nat
   n0 : nat
   n' : nat
   Recursive call to fib has principal argument equal to 
   "S n'" instead of one of the following variables: 
   "n0" "n'". *)

(** Mimo, że [S n'] jest podtermem [S (S n')], który pochodzi z dopasowania
    do wzorca, to Coq nie jest w stanie zauważyć tego faktu. W komunikacie
    o błędzie pojawia się za to tajemnicza zmienna [n0], której w naszym
    kodzie nigdzie nie ma. Sposobem na poradzenie sobie z problemem jest
    pokazanie Coqowi palcem, o co nam chodzi: *)

Fixpoint fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n' as n'') => fib n' + fib n''
end.

(** Tym razem Coq widzi, że [S n'] jest podtermem [S (S n')], gdyż explicite
    nadaliśmy temu termowi nazwę [n''], używając do tego klauzli [as].

    Ufff...  udało nam się przebrnąć przez techniczne detale działania
    rekursji strukturalnej. Mogłoby się wydawać, że jest ona mechanizmem
    bardzo upośledzonym, ale z doświadczenia wiesz już, że w praktyce
    omówione wyżej problemy występują raczej rzadko.

    Mogłoby się też wydawać, że skoro wywołania rekurencyjne możemy robić
    tylko na bezpośrednich podtermach dopasowanych we wzorcu, to nie da się
    zdefiniować prawie żadnej ciekawej funkcji. Jak zobaczymy w kolejnych
    podrozdziałach, wcale tak nie jest. Dzięki pewnej sztuczce za pomocą
    rekursji strukturalnej można wyrazić rekursję dobrze ufundowaną, która
    na pierwszy rzut oka jest dużo potężniejsza i daje nam wiele możliwości
    definiowania różnych ciekawych funkcji. *)

(** **** Ćwiczenie (dzielenie) *)

(** Zdefiniuj funkcję [div], która implementuje dzielenie całkowitoliczbowe.
    Żeby uniknąć problemów z dzieleniem przez [0], [div n m] będziemy
    interpretować jako [n] podzielone przez [S m], czyli np. [div n 0]
    to n/1, [div n 1] to n/2 etc. Uwaga: to ćwiczenie pojawia się właśnie
    w tym miejscu nieprzypadkowo. *)

(* begin hide *)
Fail Fixpoint div (n m : nat) : nat :=
  if n <? m
  then n
  else div (n - m) m.
(* end hide *)

(** * Rekursja monotoniczna *)

Require Import X3.

(** Czas na omówienie pewnej ciekawej, ale średnio użytecznej formy rekursji
    (z pamięci nie jestem w stanie przytoczyć więcej niż dwóch sztampowych
    przykładów jej użycia), a jest nią rekursja monotoniczna (zwana też
    czasem rekursją zagnieżdżoną, ale nie będziemy używać tej nazwy, gdyż
    dotychczas używaliśmy jej na określenie rekursji, w której arguemntem
    wywołania rekurencyjnego jest wynik innego wywołania rekurencyjnego).

    Cóż to za zwierzątko, rekursja monotoniczna? Żeby się tego dowiedzieć,
    przypomnijmy sobie najpierw, jak technicznie w Coqu zrealizowana jest
    rekursja strukturalna. *)

Fixpoint plus (n : nat) : nat -> nat :=
match n with
    | 0 => fun m : nat => m
    | S n' => fun m : nat => S (plus n' m)
end.

(** Tak oto definicja funkcji plus, lecz zapisana nieco inaczej, niż gdy
    widzieliśmy ją ostatnim razem. Tym razem prezentujemy ją jako funkcję
    biorącą jeden argument typu [nat] i zwracającą funkcję z typu [nat] w
    typ [nat]. *)

Definition plus' : nat -> nat -> nat :=
  fix f (n : nat) : nat -> nat :=
  match n with
      | 0 => fun m : nat => m
      | S n' => fun m : nat => S (f n' m)
  end.

(** Ale komenda [Fixpoint] jest jedynie cukrem syntaktycznym - funkcję [plus]
    możemy równie dobrze zdefiniować bez niej, posługując się jedynie komendą
    [Definition], a wyrażeniem, które nam to umożliwia, jest [fix]. [fix]
    działa podobnie jak [fun], ale pozwala dodatkowo nadać definiowanej przez
    siebie funkcji nazwę, dzięki czemu możemy robić wywołania rekurencyjne.

    Czym więc jest rekursja monotoniczna? Z rekursją monotoniczną mamy do
    czynienia, gdy za pomocą [fix]a (czyli przez rekursję) definiujemy
    funkcję, która zwraca inną funkcję, i ta zwracana funkcja także jest
    zdefiniowana za pomocą [fix]a (czyli przez rekursję). Oczywiście to
    tylko pierwszy krok - wynikowa funkcja również może zwracać funkcję,
    która jest zdefiniowana za pomocą [fix]a i tak dalej.

    Widać zatem jak na dłoni, że [plus] ani [plus'] nie są przykładami
    rekursji monotonicznej. Wprawdzie definiują one za pomocą [fix]a
    (lub komendy [Fixpoint]) funkcję, która zwraca inną funkcję, ale ta
    zwracana funkcja nie jest zdefiniowana za pomocą [fix]a, lecz za
    pomocą [fun], a więc nie jest rekurencyjna.

    Podsumowując: rekursja jest monotoniczna, jeżeli w definicji
    funkcji pojawiają się co najmniej dwa wystąpienia [fix], jedno
    wewnątrz drugiego (przy czym rzecz jasna [Fixpoint] też liczy
    się jako [fix]).

    No to skoro już wiemy, czas zobaczyć przykład jakiejś funkcji, która
    jest zdefiniowana przez rekursję monotoniczną. *)

Fail Fixpoint ack (n m : nat) : nat :=
match n, m with
    | 0, m => S m
    | S n', 0 => ack n' 1
    | S n', S m' => ack n' (ack (S n') m')
end.

(* ===> The command has indeed failed with message:
        Cannot guess decreasing argument of fix. *)

(** Powyższa funkcja zwana jest funkcją Ackermanna, gdyż wymyślił ją...
    zgadnij kto. Jest ona całkiem sławna, choć z zupełnie innych powodów
    niż te, dla których my się jej przyglądamy. Nie oblicza ona niczego
    specjalnie użytecznego - jej wynikami są po prostu bardzo duże liczby.
    Jeżeli nie wierzysz, spróbuj policzyć ręcznie [ack 4 2] - zdziwisz się.

    Jak widać, Coq nie akceptuje powyższej definicji. Winny temu jest rzecz
    jasna kształt rekursji. Dla [n] równego [0] zwracamy [S m], co jest ok.
    Dla [n] postaci [S n'] i [m] równego [0] robimy wywołanie rekurencyjne
    na [n'] i [1], co również jest ok. Jednak jeżeli [n] i [m] odpowednio
    są postaci [S n'] i [S m'], to robimy wywołanie rekurencyjne postaci
    [ack n' (ack (S n') m')]. W wewnętrznym wywołaniu rekurencyjnym pierwszy
    argument jest taki sam jak obecny. Gdyby argumentem głównym był drugi
    argument, to jest tym bardziej źle, gdyż w zewnętrznym wywołaniu
    rekurencyjnym nie jest nim [m'], lecz [ack (S n') m']. Nie ma się więc
    co dziwić, że Coq nie może zgadnąć, który argument ma być argumentem
    głównym.

    Mimo, że Coq nie akceptuje tej definicji, to wydaje się ona być całkiem
    spoko. Żaden z argumentów nie może wprawdzie posłużyć nam za argument
    główny, ale jeżeli rozważymy ich zachowanie jako całość, to okazuje się,
    że w każdym wywołaniu rekurencyjnym mamy dwie możliwości:
    - albo pierwszy argument się zmniejsza
    - albo pierwszy argument się nie zmienia, ale drugi argument się
      zmniejsza

    Możemy z tego wywnioskować, że jeżeli wywołamy [ack] na argumentach
    [n] i [m], to w ogólności najpierw [m] będzie się zmniejszał, ale
    ponieważ musi kiedyś spaść do zera, to wtedy [n] będzie musiał się
    zmniejszyć. Oczywiście wtedy w kolejnym wywołaniu zaczynamy znowu z
    jakimś [m], które potem się zmniejsza, aż w końcu znowu zmniejszy
    się [n] i tak dalej, aż do chwili, gdy [n] spadnie do zera. Wtedy
    rekursja musi się skończyć.

    Jednym z typowych zastosowań rekursji zagnieżdżonej jest radzenie
    sobie z takimi właśnie przypadkami, w których mamy ciąg argumentów
    i pierwszy maleje, lub pierwszy stoi w miejscu a drugi maleje i tak
    dalej. Zobaczmy więc, jak techniki tej można użyć do zdefiniowania
    funkcji Ackermanna. *)

Fixpoint ack (n : nat) : nat -> nat :=
match n with
    | 0 => S
    | S n' =>
        fix ack' (m : nat) : nat :=
        match m with
            | 0 => ack n' 1
            | S m' => ack n' (ack' m')
        end
end.

(** Zauważmy przede wszystkim, że nieco zmienia się wygląd typu naszej
    funkcji. Jest on wprawdzie dokładnie taki sam ([nat -> nat -> nat]),
    ale zapisujemy go inaczej. Robimy to by podkreslić, że wynikiem [ack]
    jest funkcja. W przypadku gdy [n] jest postaci [S n'] zdefiniowana
    jest ona za pomocą [fix]a tak, jak wyglądają dwie ostatnie klauzule
    dopasowania z oryginalnej definicji, ale z wywołaniem [ack (S n') m']
    zastąpionym przez [ack' m']. Tak więc funkcja [ack'] reprezentuje
    częściową aplikację [ack n]. *)

(* begin hide *)
Lemma ack_ind :
  forall
    (P : nat -> nat -> nat -> Prop)
    (P0 : forall m : nat, P 0 m (S m))
    (PS0 : forall n' : nat, P n' 1 (ack n' 1) -> P (S n') 0 (ack (S n') 0))
    (PSS : forall n' m' : nat,
      P (S n') m' (ack (S n') m') ->
      P n' (ack (S n') m') (ack n' (ack (S n') m')) ->
      P (S n') (S m') (ack (S n') (S m'))),
        forall n m : nat, P n m (ack n m).
Proof.
  induction n as [| n'].
    cbn. apply P0.
    induction m as [| m'].
      apply PS0. apply IHn'.
      apply PSS.
        apply IHm'.
        apply IHn'.
Qed.
(* end hide *)

Lemma ack_eq :
  forall n m : nat,
    ack n m =
    match n, m with
        | 0, _ => S m
        | S n', 0 => ack n' 1
        | S n', S m' => ack n' (ack (S n') m')
    end.
Proof.
  destruct n, m; reflexivity.
Qed.

Lemma ack_big :
  forall n m : nat,
    m < ack n m.
Proof.
(* begin hide *)
  apply ack_ind.
    do 2 constructor.
    intros. cbn. lia.
    intros. rewrite ack_eq. lia.
Restart.
(* end hide *)
  induction n as [| n'].
    cbn. intro. apply le_n.
    induction m as [| m'].
      cbn. apply lt_trans with 1.
        apply le_n.
        apply IHn'.
      specialize (IHn' (ack (S n') m')).
        rewrite ack_eq. lia.
Qed.

Lemma ack_big' :
  forall n1 n2 : nat, n1 <= n2 ->
    forall m1 m2 : nat, m1 <= m2 ->
      ack n1 m1 <= ack n2 m2.
Proof.
  induction 1.
    induction 1.
      reflexivity.
      rewrite IHle. destruct n1.
        cbn. apply le_S, le_n.
        rewrite (ack_eq (S n1) (S m)).
          pose (ack_big n1 (ack (S n1) m)). lia.
    induction 1.
      destruct m1.
        cbn. apply IHle. do 2 constructor.
        rewrite (ack_eq (S m) (S m1)).
          rewrite (IHle (S m1) (ack (S m) m1)).
            reflexivity.
            apply ack_big.
      rewrite (ack_eq (S m)). apply IHle. apply le_trans with (S m0).
        apply le_S. exact H0.
        apply ack_big.
Qed.

(** **** Ćwiczenie *)

Require Import Arith.

(** Zdefiniuj funkcję [merge] o typie
    [forall (A : Type) (cmp : A -> A -> bool), list A -> list A -> list A],
    która scala dwie listy posortowane według porządku wyznaczanego przez
    [cmp] w jedną posortowaną listę. Jeżeli któraś z list posortowana nie
    jest, wynik może być dowolny.

    Wskazówka: dlaczego niby to ćwiczenie pojawia się w podrozdziale o
    rekursji zagnieżdżonej? *)

(* begin hide *)
Fixpoint merge
  {A : Type} (cmp : A -> A -> bool) (l1 : list A) : list A -> list A :=
match l1 with
  | [] => fun l2 : list A => l2
  | h1 :: t1 =>
      fix merge' (l2 : list A) : list A :=
        match l2 with
          | [] => l1
          | h2 :: t2 =>
              if cmp h1 h2
              then h1 :: merge cmp t1 l2
              else h2 :: merge' t2
        end
end.
(* end hide *)

Compute merge leb [1; 4; 6; 9] [2; 3; 5; 8].
(* ===> = [[1; 2; 3; 4; 5; 6; 8; 9]]
        : list nat *)

(** Obie listy są posortowane według [leb], więc wynik też jest. *)

Compute merge leb [5; 3; 1] [4; 9].
(* ===> = [[4; 5; 3; 1; 9]]
        : list nat *)

(** Pierwsza lista nie jest posortowana według [leb], więc wynik jest
    z dupy. *)

(** **** Ćwiczenie *)

(** Skoro już udało ci się zdefiniować [merge], to udowodnij jeszcze parę
    lematów, cobyś nie miał za dużo wolnego czasu. *)

Lemma merge_eq :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A},
    merge cmp l1 l2 =
    match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | h1 :: t1, h2 :: t2 =>
            if cmp h1 h2
            then h1 :: merge cmp t1 l2
            else h2 :: merge cmp l1 t2
    end.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      reflexivity.
      destruct (cmp h1 h2); cbn.
        rewrite IHt1. reflexivity.
        rewrite IHt2. reflexivity.
Qed.
(* end hide *)

Lemma merge_nil_l :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A},
    merge cmp [] l = l.
Proof.
  reflexivity.
Qed.

Lemma merge_nil_r :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A},
    merge cmp l [] = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma Permutation_merge :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 : list A},
    Permutation (merge f l1 l2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite app_nil_r. reflexivity.
      destruct (f h1 h2).
        rewrite IHt1. reflexivity.
        rewrite IHt2. rewrite perm_swap.
          constructor. rewrite Permutation_app_comm.
            rewrite (Permutation_app_comm _ t1 (h2 :: t2)). reflexivity.
Qed.
(* end hide *)

Lemma merge_length :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 : list A},
    length (merge f l1 l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite <- plus_n_O. reflexivity.
      destruct (f h1 h2); cbn.
        rewrite IHt1. cbn. reflexivity.
        rewrite IHt2. rewrite plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma merge_map :
  forall {A B : Type} {cmp : B -> B -> bool} {f : A -> B} {l1 l2 : list A},
      merge cmp (map f l1) (map f l2) =
      map f (merge (fun x y : A => cmp (f x) (f y)) l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      reflexivity.
      destruct (cmp (f h1) (f h2)); cbn.
        rewrite <- IHt1. cbn. reflexivity.
        rewrite IHt2. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma merge_rev :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A},
    merge cmp l1 l2 = rev (merge (fun x y : A => cmp y x) (rev l1) (rev l2)).
Proof.
  induction l1 as [| h1 t1]; cbn.
    intros. rewrite rev_inv. reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite merge_eq. case_eq (rev t1 ++ [h1]); intros.
        apply (f_equal length) in H. rewrite length_app, plus_comm in H.
          inversion H.
        rewrite <- H, rev_app, rev_inv. cbn. reflexivity.
      rewrite IHt1, IHt2. case_eq (cmp h1 h2); intros.
Abort.
(* end hide *)

Lemma merge_replicate :
  forall {A : Type} {cmp : A -> A -> bool} {x y : A} {n m : nat},
    merge cmp (replicate n x) (replicate m y) =
    if cmp x y
    then replicate n x ++ replicate m y
    else replicate m y ++ replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    destruct (cmp x y); try reflexivity.
      intros. rewrite app_nil_r. reflexivity.
    induction m as [| m']; cbn.
      destruct (cmp x y).
        rewrite app_nil_r. reflexivity.
        reflexivity.
      case_eq (cmp x y); intro eq.
        rewrite merge_eq. destruct n'; cbn.
          reflexivity.
          specialize (IHn' (S m')). cbn in IHn'.
            rewrite eq, <- IHn' in *. reflexivity.
        rewrite IHm', eq. reflexivity.
Qed.
(* end hide *)

Fixpoint ins
  {A : Type} (cmp : A -> A -> bool) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => if cmp x h then x :: h :: t else h :: ins cmp x t
end.

Lemma merge_ins_l :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A} {x : A},
    merge cmp [x] l = ins cmp x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (cmp x h).
      reflexivity.
      rewrite <- IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma merge_ins_r :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A} {x : A},
    merge cmp l [x] = ins cmp x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (cmp h x), (cmp x h).
Abort.
(* end hide *)

Lemma merge_ins' :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A} {x : A},
    merge cmp (ins cmp x l1) (ins cmp x l2) =
    ins cmp x (ins cmp x (merge cmp l1 l2)).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    induction l2 as [| h2 t2]; cbn.
      reflexivity.
      intro. case_eq (cmp x h2); cbn; intros.
        destruct (cmp x x).
          reflexivity.
          rewrite H. reflexivity.
        rewrite H, IHt2. reflexivity.
    induction l2 as [| h2 t2]; cbn; intros.
      case_eq (cmp x h1); cbn; intros eq.
        destruct (cmp x x).
          destruct (cmp h1 x).
            admit.
            reflexivity.
          rewrite eq. reflexivity.
        rewrite eq. destruct (cmp h1 x).
Abort.
(* end hide *)

Lemma merge_all_true :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A} {x : A},
    all (fun y : A => cmp x y) l = true ->
      merge cmp [x] l = x :: l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    case_eq (cmp x h); intros eq.
      reflexivity.
      rewrite eq in H. cbn in H. inversion H.
Qed.
(* end hide *)

Lemma merge_ind :
  forall {A : Type} (P : list A -> list A -> list A -> Prop)
    {f : A -> A -> bool},
      (forall l : list A, P [] l l) ->
      (forall l : list A, P l [] l) ->
      (forall (h1 h2 : A) (t1 t2 r : list A),
        f h1 h2 = true ->
          P t1 (h2 :: t2) r -> P (h1 :: t1) (h2 :: t2) (h1 :: r)) ->
      (forall (h1 h2 : A) (t1 t2 r : list A),
        f h1 h2 = false ->
          P (h1 :: t1) t2 r -> P (h1 :: t1) (h2 :: t2) (h2 :: r)) ->
      forall l1 l2 : list A, P l1 l2 (merge f l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    apply H.
    induction l2 as [| h2 t2]; cbn.
      apply H0.
      case_eq (f h1 h2); intros.
        apply H1.
          assumption.
          apply IHt1.
        apply H2.
          assumption.
          apply IHt2.
Defined.
(* end hide *)

Lemma merge_filter :
  forall {A : Type} {cmp : A -> A -> bool} {p : A -> bool} {l1 l2 : list A},
    merge cmp (filter p l1) (filter p l2) =
    filter p (merge cmp l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn in *.
      destruct (p h1); cbn.
        reflexivity.
        rewrite merge_eq. destruct (filter p t1); reflexivity.
      case_eq (p h1); case_eq (p h2); case_eq (cmp h1 h2);
      intros eq1 eq2 eq3;
      repeat (cbn in *; rewrite ?eq1, ?eq2, ?eq3 in *); cbn.
        rewrite <- IHt1. cbn. rewrite eq2. reflexivity.
        rewrite IHt2. reflexivity.
        Focus 2. rewrite IHt2. reflexivity.
        Focus 2. rewrite <- IHt1. cbn. rewrite eq2. reflexivity.
        Focus 4. rewrite IHt2. reflexivity.
Restart.
  intros until p.
  apply (merge_ind (fun l1 l2 r : list A =>
    merge cmp (filter p l1) (filter p l2) = filter p r));
  cbn; intros.
    reflexivity.
    rewrite merge_eq. destruct (filter p l); reflexivity.
    destruct (p h1), (p h2); cbn; rewrite ?H.
      rewrite H0. reflexivity.
      rewrite <- H0. destruct t2; cbn.
        admit.
Abort.
(* end hide *)

(** * Rekursja polimorficzna *)

Module Nested.

Inductive Nested (A : Type) : Type :=
  Epsilon | Cons (h : A) (t : Nested (list A)).

Arguments Epsilon {A}.
Arguments Cons    {A} _ _.

Inductive Nested' : Type -> Type :=
    | Epsilon' : forall A : Type, Nested' A
    | Cons' : forall A : Type, A -> Nested' (list A) -> Nested' A.

Check Nested_ind.
Check Nested'_ind.

Fixpoint len {A : Type} (l : Nested A) : nat :=
match l with
    | Epsilon => 0
    | Cons _ t => 1 + len t
end.

End Nested.

Module Seq.

Inductive Seq (A : Type) : Type :=
    | SNil : Seq A
    | SCons : A -> Seq (A * A) -> Seq A.

Arguments SNil  {A}.
Arguments SCons {A} _ _.

Fixpoint size {A : Type} (s : Seq A) : nat :=
match s with
    | SNil => 0
    | SCons _ t => 1 + 2 * size t
end.

End Seq.

Module Nested2.

Inductive Nested (A : Type) : Type :=
    | Singl : A -> Nested A
    | Nestd : Nested (list A) -> Nested A.

End Nested2.

(** * Rząd rżnie głupa, czyli o pierwszym i wyższym rzędzie (TODO) *)

(** * Rekursja wyższego rzędu (TODO) *)

(** Pozostaje kwestia rekursji wyższego rzędu. Co to takiego? Ano dotychczas
    wszystkie nasze wywołania rekurencyjne były konkretne, czyli zaaplikowane
    do argumentów.

    Mogłoby się wydawać, że jest to jedyny możliwy sposób robienia wywołań
    rekurencyjnych, jednak nie jest tak. Wywołania rekurencyjne mogą mieć
    również inną, wyższorzędową postać, a mianowicie - możemy przekazać
    funkcję, którą właśnie definiujemy, jako argument do innej funkcji.

    Dlaczego jest to wywołanie rekurencyjne, skoro nie wywołujemy naszej
    funkcji? Ano dlatego, że tamta funkcja, która dostaje naszą jako
    argument, dostaje niejako możliwość robienia wywołań rekurencyjnych.
    W zależności od tego, co robi ta funkcja, wszystko może być ok (np.
    gdy ignoruje ona naszą funkcję i w ogóle jej nie używa) lub śmiertelnie
    niebezpieczne (gdy próbuje zrobić wywołanie rekurencyjne na strukturalnie
    większym argumencie).

    Sztoby za dużo nie godoć, bajszpil: *)

Inductive Tree (A : Type) : Type :=
    | Node : A -> list (Tree A) -> Tree A.

Arguments Node {A} _ _.

(** [Tree] to typ drzew niepustych, które mogą mieć dowolną (ale skończoną)
    ilość poddrzew. Spróbujmy zdefiniować funkcję, która zwraca lustrzane
    odbicie drzewa. *)

Unset Guard Checking.
Fixpoint mirror {A : Type} (t : Tree A) {struct t} : Tree A :=
match t with
    | Node x ts => Node x (map mirror (rev ts))
end.
Set Guard Checking.

(** Nie jest to zbyt trudne. Rekurencyjnie odbijamy wszystkie poddrzewa za
    pomocą [map mirror], a następnie odwracamy kolejność poddrzew z użyciem
    [rev]. Chociaż poszło gładko, to mamy tu do czynienia z czymś, czego
    wcześniej nie widzieliśmy. Nie ma tu żadnego wywołania rekurencyjnego,
    a mimo to funkcja działa ok. Dlaczego? Właśnie dlatego, że wywołania
    rekurencyjne są robione przez funkcję [map]. Mamy więc do czynienia z
    rekursją wyższego rzędu. *)

Inductive mirrorG {A : Type} : Tree A -> Tree A -> Prop :=
  | mirrorG_0 :
      forall (x : A) (ts rs : list (Tree A)),
        mirrorsG ts rs -> mirrorG (Node x ts) (Node x (rev rs))

with mirrorsG {A : Type} : list (Tree A) -> list (Tree A) -> Prop :=
  | mirrorsG_nil :
      mirrorsG [] []
  | mirrorsG_cons :
      forall (t t' : Tree A) (ts ts' : list (Tree A)),
        mirrorG t t' -> mirrorsG ts ts' ->
          mirrorsG (t :: ts) (t' :: ts').

Require Import Equality.

Lemma mirrorG_correct :
  forall {A : Type} (t : Tree A),
    mirrorG t (mirror t).
Proof.
  fix IH 2.
  destruct t. cbn. rewrite map_rev. constructor.
  induction l as [| t ts].
    cbn. constructor.
    cbn. constructor.
      apply IH.
      apply IHts.
Qed.

Compute mirror (Node 0 [Node 1 [Node 5 []; Node 6 []; Node 7 []]; Node 2 []; Node 3 []]).

Module mirror.

Inductive mirrorD {A : Type} : Tree A -> Type :=
    | mirrorD' :
        forall (x : A) (ts : list (Tree A)),
          mirrorsD (rev ts) -> mirrorD (Node x ts)

with mirrorsD {A : Type} : list (Tree A) -> Type :=
    | mirrorsD_nil :
        mirrorsD []
    | mirrorsD_cons :
        forall (t : Tree A) (ts : list (Tree A)),
          mirrorD t -> mirrorsD ts -> mirrorsD (t :: ts).

Inductive mapG
  {A B : Type} (f : A -> B -> Type) : list A -> list B -> Type :=
    | mapG_nil  :
        mapG f [] []
    | mapG_cons :
        forall (a : A) (b : B) (la : list A) (lb : list B),
          f a b -> mapG f la lb -> mapG f (a :: la) (b :: lb).

Inductive mirrorG2 {A : Type} : Tree A -> Tree A -> Prop :=
  | mirrorG2' :
      forall (x : A) (ts ts' : list (Tree A)),
        mapG mirrorG2 ts ts' -> mirrorG2 (Node x ts) (Node x (rev ts')).

Lemma mirrorG2_correct :
  forall {A : Type} (t : Tree A),
    mirrorG2 t (mirror t).
Proof.
  fix IH 2.
  destruct t. cbn. rewrite map_rev. constructor.
  induction l as [| t ts].
    cbn. constructor.
    cbn. constructor.
      apply IH.
      apply IHts.
Qed.

End mirror.

(** Inny przykład: *)

Inductive Tree' (A : Type) : Type :=
    | Node' : A -> forall {B : Type}, (B -> Tree' A) -> Tree' A.

Arguments Node' {A} _ _ _.

(** Tym razem mamy drzewo, które może mieć naprawdę dowolną ilość poddrzew,
    ale jego poddrzewa są nieuporządkowane. *)

Fixpoint mirror' {A : Type} (t : Tree' A) : Tree' A :=
match t with
    | Node' x B ts => Node' x B (fun b : B => mirror' (ts b))
end.

(** * Rekursja strukturalna (TODO) *)

(** * Rekursja ogólna *)

(** W Coqu rekursja ogólna nie jest dozwolona. Powód jest banalny: prowadzi
    ona do sprzeczności. W celu zobrazowania spróbujmy zdefiniować za pomocą
    taktyk następującą funkcję rekurencyjną: *)

Fixpoint loop (u : unit) : False.
Proof.
  apply loop. assumption.
Fail Qed.
Abort.

(** Przyjrzyjmy się uważnie definicji funkcji [loop]. Mimo, że udało
    nam się ujrzeć znajomy napis "No more subgoals", próba użycia
    komendy [Qed] kończy się błędem.

    Fakt, że konstruujemy funkcję za pomocą taktyk, nie ma tu żadnego
    znaczenia, lecz służy jedynie lepszemu zobrazowaniu, dlaczego rekursja
    ogólna jest grzechem. Dokładnie to samo stałoby się, gdybyśmy próbowali
    zdefiniować [loop] ręcznie: *)

Fail Fixpoint loop (u : unit) : False := loop u.

(** Gdyby tak się nie stało, możliwe byłoby skonstruowanie dowodu [False]: *)

Fail Definition the_universe_explodes : False := loop tt.

(** Aby chronić nas przed tą katastrofą, Coq nakłada na rekurencję
    ograniczenie: argument główny wywołania rekurencyjnego musi być
    strukturalnym podtermem argumentu głównego obecnego wywołania.
    Innymi słowy, dozwolona jest jedynie rekursja strukturalna.

    To właśnie napisane jest w komunikacie o błędzie, który dostajemy,
    próbując przeforsować powyższe definicje: *)

(* Recursive definition of loop is ill-formed.
   In environment
   loop : unit -> False
   u : unit
   Recursive call to loop has principal argument equal to
   "u" instead of a subterm of "u".
   Recursive definition is: "fun u : unit => loop u". *)

(** Wywołanie rekurencyjne [loop] jest nielegalne, gdyż jego argumentem
    jest [u], podczas gdy powinien być nim jakiś podterm [u].

    Zanim jednak dowiemy się, czym jest argument główny, czym są podtermy
    i jak dokładnie Coq weryfikuje poprawność naszych definicji funkcji
    rekurencyjnych, wróćmy na chwilę do indukcji. Jak się zaraz okaże,
    nielegalność rekursji ogólnej wymusza również pewne ograniczenia w
    definicjach induktywnych. *)

(** **** Ćwiczenie *)

(** Ograniczenia nakładane przez Coqa sprawiają, że wszystkie napisane
    przez nas funkcje rekurencyjne muszą się kiedyś zatrzymać i zwrócić
    ostateczny wynik swojego działania. Tak więc nie możemy w Coqu pisać
    funkcji nieterminujących, czyli takich, które się nie zatrzymują.

    Rozważ bardzo interesujące pytanie filozoficzne: czy funkcje, które
    nigdy się nie zatrzymują (lub nie zatrzymują się tylko dla niektórych
    argumentów) mogą być w ogóle do czegokolwiek przydatne?

    Nie daj się wpuścić w maliny. *)

(** * Rekursja po paliwie *)

(** Rekursja dobrze ufundowana to sirius byznys, więc zanim się nią zajmiemy
    wypadałoby nauczyć się robić robotę na odwal, byle działało. Jakkolwiek
    nie brzmi to zbyt profesjonalnie, dobrze jest mieć tego typu narzędzie
    w zanadrzu, choćby w celu szybkiego prototypowania. Czasem zdarza się
    też, że tego typu luźne podejście do problemu jest jedynym możliwym, bo
    nikt nie wie, jak to zrobić porządnie.

    Narzędziem, o którym mowa, jest coś, co ja nazywam "rekursją po paliwie".
    Pozwala ona zasymulować definicję dowolnej funkcji o typie
    [A1 -> ... -> An -> B] (w tym nawet częściowej czy nieterminującej, co
    już samo w sobie jest ciekawe) za pomocą funkcji o typie
    [nat -> A1 -> ... -> An -> option B].

    Trik jest dość banalny: argument typu [nat] jest argumentem głównym,
    po którym robimy rekursję. Jest on naszym "paliwem", które spalamy
    przy każdym wywołaniu rekurencyjnym. Jeżeli paliwo się nam skończy,
    zwracamy [None]. Jeżeli jeszcze starcza paliwa, możemy zdefiniować
    funkcję tak jak zamierzaliśmy, ale mamy też obowiązki biurokratyczne
    związane ze sprawdzaniem, czy wyniki wywołań rekurencyjnych to [None]
    czy [Some].

    Coby za dużo nie godoć, przykład. *)

Require Import List.
Import ListNotations.

Require Import Nat.

(** Będą nam potrzebne notacje dla list oraz funkcja [even], która sprawdza,
    czy liczba naturalna jest parzysta. Będziemy chcieli zdefiniować funkcję
    Collatza. Gdyby Coq wspierał rekursję ogólną, jej definicja wyglądałaby
    tak: *)

Fail Fixpoint collatz (n : nat) : list nat :=
match n with
    | 0 | 1 => [n]
    | _ => n :: if even n then collatz (div2 n) else collatz (1 + 3 * n)
end.

(** Jest to bardzo wesoła funkcja. Przypadki bazowe to [0] i [1] - zwracamy
    wtedy po prostu listę z jednym elementem, odpowiednio [[0]] lub [[1]].
    Ciekawiej jest dla [n] większego od 1. [n] zostaje głową listy, zaś w
    kwestii ogona mamy dwa przypadki. Jeżeli [n] jest parzyste, to argumentem
    wywołania rekurencyjnego jest [n] podzielone przez [2], zaś w przeciwnym
    przypadku jest to [1 + 3 * n].

    Funkcja ta nie ma żadnego ukrytego celu. Została wymyślona dla zabawy,
    a przyświecające jej pytanie to: czy funkcja ta kończy pracę dla każdego
    argumentu, czy może jest jakiś, dla którego się ona zapętla?

    O ile funkcja jest prosta, o tyle odpowiedź jest bardzo skomplikowana i
    dotychczas nikt nie potrafił jej udzielić. Sprawdzono ręcznie (czyli za
    pomocą komputerów) bardzo dużo liczb i funkcja ta zawsze kończyła pracę,
    ale nikt nie umie udowodnić, że dzieje się tak dla wszystkich liczb. *)

Fixpoint collatz (fuel n : nat) : option (list nat) :=
match fuel with
    | 0 => None
    | S fuel' =>
        match n with
            | 0 | 1 => Some [n]
            | _ =>
                if even n
                then
                  match collatz fuel' (div2 n) with
                      | Some l => Some (n :: l)
                      | None => None
                  end
                else
                  match collatz fuel' (1 + 3 * n) with
                      | Some l => Some (n :: l)
                      | None => None
                  end
        end
end.

(** Definicja funkcji [collatz] za pomocą rekursji po paliwie wygląda dość
    groźnie, ale tak naprawdę jest całkiem banalna.

    Ponieważ oryginalna funkcja była typu [nat -> list nat], to ta nowa musi
    być typu [nat -> nat -> option (list nat)]. Tym razem zamiast dopasowywać
    [n] musimy dopasować paliwo, czyli [fuel]. Dla [0] zwracamy [None], a gdy
    zostało jeszcze trochę paliwa, przechodzimy do właściwej części definicji.
    W przypadkach bazowych zwracamy [[n]], ale  musimy zawinąć je w [Some]. W
    pozostałych przypadkach sprawdzamy, czy [n] jest parzyste, a następnie
    doklejamy odpowiedni ogon, ale musimy dopasować wywołania rekurencyjne
    żeby sprawdzić, czy zwracają one [None] czy [Some]. *)

Compute collatz 10 5.
(* ===> = Some [[5; 16; 8; 4; 2; 1]]
        : option (list nat) *)

Compute collatz 2 5.
(* ===> = None
        : option (list nat) *)

(** Zaimplementowana za pomocą rekursji po paliwie funkcja oblicza się bez
    problemu, oczywiście o ile wystarczy jej paliwa. W powyższych przykładach
    [10] jednostek paliwa wystarcza, by obliczyć wynik dla [5], ale [2]
    jednostki paliwa to za mało. Jak więc widać, ilość potrzebnego paliwa
    zależy od konkretnej wartości na wejściu.

    Interpretacja tego, czym tak naprawdę jest paliwo, nie jest zbyt
    trudna. Jest to maksymalna głębokość rekursji, na jaką może pozwolić
    sobie funkcja. Czym jest głębokość rekursji? Możemy wyobrazić sobie
    drzewo, którego korzeniem jest obecne wywołanie, a poddrzewami są
    drzewa dla wywołań rekurencyjnych. Głębokość rekursji jest po prostu
    głębokością (czyli wysokością) takiego drzewa.

    W przypadku funkcji [collatz] głębokość rekursji jest równa długości
    zwróconej listy (gdy funkcja zwraca [Some]) lub większa niż ilość
    paliwa (gdy funkcja zwraca [None]).

    Powyższe rozważania prowadzą nas do techniki, która pozwala z funkcji
    zrobionej rekursją po paliwie zrobić normalną, pełnoprawną funkcję.
    Wystarczy znaleźć "funkcję tankującą"
    [fill_tank : A1 -> ... -> An -> nat], która oblicza, ile paliwa
    potrzeba dla danych argumentów wejściowych. Funkcja ta powinna mieć
    tę własność, że gdy nalejemy tyle paliwa, ile ona każe (lub więcej),
    zawsze w wyniku dostaniemy [Some].

    Trudnością, z którą nikt dotychczas w przypadku funkcji [collatz] nie
    potrafił się uporać, jest właśnie znalezienie funkcji tankującej. Jak
    więc widać, rekursja po paliwie nie zawsze jest fuszerką czy środkiem
    prototypowania, lecz czasem bywa faktycznie przydatna do reprezentowania
    funkcji, których inaczej zaimplementować się nie da. *)

(** **** Ćwiczenie *)

(** Zdefiniuj za pomocą rekursji po paliwie funkcję [divFuel], która jest
    implementacją dzielenia (takiego zwykłego, a nie sprytnego jak ostatnio,
    tzn. [divFuel fuel n 0] jest niezdefiniowane). *)

(* begin hide *)
Fixpoint divFuel (fuel n m : nat) : option nat :=
match fuel with
    | 0 => None
    | S fuel' =>
        if ltb n m
        then Some 0
        else
          match divFuel fuel' (n - m) m with
              | Some r => Some (S r)
              | None => None
          end
end.
(* end hide *)

(** **** Ćwiczenie *)

(** Sporą zaletą rekursji po paliwie jest to, że definicje zrobionych za
    jej pomocą funkcji są jasne i czytelne (przynajmniej w porównaniu do
    rekursji dobrze ufundowanej, o czym już niedługo się przekonamy). To
    z kolei pozwala nam w dość łatwy sposób dowodzić interesujących nas
    właściwości tych funkcji.

    Udowodnij kilka oczywistych właściwości dzielenia:
    - [divFuel ? n 1 = Some n], tzn. [n/1 = n]. Ile potrzeba paliwa?
    - [divFuel ? n n = Some 1], tzn. [n/n = 1]. Ile potrzeba paliwa?
    - przy dzieleniu przez [0] nigdy nie starcza paliwa. *)

(* begin hide *)
Require Import Arith.

Lemma divFuel_1 :
  forall n : nat,
    divFuel (S n) n 1 = Some n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite Nat.sub_0_r. cbn in IHn'. destruct n' as [| n''].
      cbn. reflexivity.
      rewrite IHn'. reflexivity.
Qed.

Lemma divFuel_0 :
  forall fuel n : nat,
    divFuel fuel n 0 = None.
Proof.
  induction fuel as [| fuel']; cbn; intro.
    reflexivity.
    rewrite IHfuel'. reflexivity.
Qed.

Lemma divFuel_n :
  forall n : nat,
    divFuel 2 (S n) (S n) = Some 1.
Proof.
  intro n. unfold divFuel.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.sub_diag.
  cbn. reflexivity.
Qed.

(* end hide *)

(** **** Ćwiczenie (lemat o tankowaniu) *)

(** Pokaż, że jeżeli wystarcza nam paliwa do obliczenia wyniku, ale
    zatankujemy jeszcze trochę, to dalej będzie nam wystarczać.
    Wniosek: tankującemu nie dzieje się krzywda. *)

(* begin hide *)

(* TODO *)

Lemma tank_filling_lemma :
  forall fuel n m r : nat,
      divFuel fuel n (S m) = Some r -> divFuel (S fuel) n (S m) = Some r.
Proof.
  induction fuel as [| fuel']; cbn.
    inversion 1.
    destruct m as [| m']; intros.
      destruct (n <=? 0).
        assumption.
        destruct n; cbn.
          cbn in H. destruct fuel'; cbn in H.
            inversion H.
            assumption.
          destruct n; cbn.
            destruct fuel'; cbn in H.
              inversion H.
              assumption.
            cbn in H. rewrite Nat.sub_0_r. admit.
      destruct (n <=? S m').
        assumption.
        cbn in *.
Abort.

Lemma tank_filling_lemma :
  forall fuel fuel',
    fuel <= fuel' -> forall n m r : nat,
      divFuel fuel n m = Some r -> divFuel fuel' n m = Some r.
Proof.
  intros fuel fuel'.
  induction 1 as [| fuel' H IH]; intros.
    assumption.
    cbn. destruct m; cbn.
      rewrite divFuel_0 in H0. inversion H0.
      destruct fuel; cbn in H0.
        inversion H0.
        case_eq (n <=? m); intros.
          rewrite H1 in H0. assumption.
          case_eq (divFuel fuel (n - S m) (S m)); intros.
            rewrite H2, H1 in H0. cbn in IH.
Abort.

(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij, że funkcji [collatz] dla wejść o postaci [pow 2 n] (czyli
    potęg dwójki) wystarczy [S n] jednostek paliwa.

    Uwaga (trochę złośliwa): jeśli napotkasz trudności w trakcie dowodzenia
    (a moje uwagi przecież nie biorą się znikąd), to pamiętaj, że mają one
    charakter arytmetyczny, tzn. są związane z użyciem w definicji funkcji
    takich jak [pow] czy [div2], nie są zaś spowodowane jakimiś problemami
    z samą techniką, jaką jest rekursja po paliwie. *)

(* begin hide *)

Lemma pow2_n_SS :
  forall n : nat, exists m : nat, pow 2 (S n) = S (S m).
Proof.
  induction n as [| n']; cbn.
    exists 0. reflexivity.
    destruct IHn' as [m IH]. cbn in IH. rewrite IH. cbn.
      exists (m + (S (S (m + 0)))). reflexivity.
Qed.

Lemma even_pow_2 :
  forall n : nat,
    even (2 ^ S n) = true.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    {
      cbn in IHn'.
      rewrite Nat.even_add,
              IHn',
              Nat.add_assoc, Nat.even_add, <- Nat.add_assoc,
              IHn'.
      cbn.
      reflexivity.
    }
Qed.

Arguments pow _ : simpl never.

Lemma div2_pow_2 :
  forall n : nat,
    div2 (2 ^ S n) = 2 ^ n.
Proof.
  intros. apply Nat.div2_double.
Qed.

Lemma collatz_pow2 :
  forall n : nat,
    exists (h : nat) (t : list nat),
      collatz (S n) (pow 2 n) = Some (h :: t).
Proof.
  cbn.
  induction n as [ | | n'] using nat_ind_2.
    compute. exists 1, []. reflexivity.
    compute. exists 2, [1]. reflexivity.
    destruct (pow2_n_SS (S n')) as [m eq]. rewrite eq, <- eq.
      rewrite even_pow_2, div2_pow_2. cbn.
        destruct (pow2_n_SS n') as [m' eq']. rewrite eq', <- eq'.
          rewrite even_pow_2, div2_pow_2.
            destruct IHn' as (h & t & IH).
              exists (2 ^ S (S n')), (2 ^ S n' :: h :: t).
                rewrite IH. reflexivity.
Qed.

(* end hide *)

(** * Rekursja dobrze ufundowana *)

(** Typy induktywne są jak domino - każdy term to jedna kostka, indukcja
    i rekursja odpowiadają zaś temu co tygryski lubią najbardziej, czyli
    reakcji łańcuchowej przewracającej wszystkie kostki.

    Typ [unit] to jedna biedna kostka, zaś [bool] to już dwie biedne
    kostki - [true] i [false]. W obu przypadkach nie dzieje się nic
    ciekawego - żeby wszystkie kostki się przewróciły, musimy pchnąć
    palcem każdą z osobna.

    Typ [nat] jest już ciekawszy - są dwa rodzaje kostek, [0] i [S],
    a jeżeli pchniemy kostkę [0] i między kolejnymi kostkami jest
    odpowiedni odstęp, to równy szlaczek kolejnych kostek przewracać
    się będzie do końca świata.

    Podobnie dla typu [list A] mamy dwa rodzaje kostek - [nil] i [cons],
    ale kostki rodzaju [cons] mają różne kolory - są nimi elementy typu
    [A]. Podobnie jak dla [nat], jeżeli pchniemy kostkę [nil] i odstępy
    między kolejnymi kostkami są odpowiednie, to kostki będą przewracać
    się w nieskończoność. Tym razem jednak zamiast jednego szaroburego
    szlaczka będzie multum kolorowych szlaczków o wspólnych początkach
    (no chyba, że [A = unit] - wtedy dostaniemy taki sam bury szlaczek
    jak dla [nat]).

    Powyższe malownicze opisy przewracających się kostek domina bardziej
    przywodzą na myśl indukcję, niż rekursję, chociaż wiemy już, że jest
    to w sumie to samo. Przyjmują one perspektywę "od przodu" - jeżeli
    przewrócimy początkową kostkę i niczego nie spartaczyliśmy, kolejne
    kostki będą przewracać się już same.

    Co to znaczy, że niczego nie spartaczyliśmy, pytasz? Tutaj przydaje
    się spojrzenie na nasze domino "od tyłu". Żeby kostka domina się
    przewróciła, muszą przewrócić się na nią wszystkie bezpośrednio
    poprzedzające ją kostki, a żeby one się przewróciły, to przewrócić
    muszą się wszystkie poprzedzające je kostki i tak dalej. W związku
    z tym możemy powiedzieć, że kostka jest dostępna, jeżeli dostępne
    są wszystkie kostki ją poprzedzające.

    Jeszcze jeden drobny detal: kiedy dostępne są kostki, które nie mają
    żadnych poprzedzających kostek? Odpowiedź: zawsze, a dowodem na to
    jest nasz palec, który je przewraca.

    W ten oto wesoły sposób udało nam się uzyskać definicję elementu
    dostępnego oraz relacji dobrze ufundowanej. *)

Inductive Acc {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
    | Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

(** Kostki domina reprezentuje typ [A], zaś relacja [R] to sposób ułożenia
    kostek, a [x] to pewna konkretna kostka domina. Konstruktor [Acc_intro]
    mówi, że kostka [x] jest dostępna w układzie domina [R], jezeli każda
    kostka [y], która poprzedza ją w układzie [R], również jest dostępna.

    Mniej poetycko: element [x : A] jest [R]-dostępny, jeżeli każdy
    [R]-mniejszy od niego element [y : A] również jest [R]-dostępny. *)

Definition well_founded {A : Type} (R : A -> A -> Prop) : Prop :=
  forall x : A, Acc R x.

(** Układ kostek reprezentowany przez [R] jest niespartaczony, jeżeli każda
    kostka domina jest dostępna.

    Mniej poetycko: relacja [R] jest dobrze ufundowana, jeżeli każde [x : A]
    jest [R]-dostępne.

    Uwaga: typem naszego układu kostek nie jest [A -> A -> Prop], lecz
    [A -> A -> Type], a zatem [R] jest tak naprawdę indeksowaną rodziną
    typów, a nie relacją. Różnica między relacją i rodziną typów jest
    taka, że relacja, gdy dostanie argumenty, zwraca zdanie, czyli coś
    typu [Prop], a rodzina typów, gdy dostanie argumenty, zwraca typ,
    czyli coś typu [Type]. Tak więc pojęcie rodziny typów jest ogólniejsze
    niż pojęcie relacji. Ta ogólność przyda się nam za kilka chwil aby nie
    musieć pisać wszystkiego dwa razy. *)

(** **** Ćwiczenie *)

(** Sprawdź, czy relacje [<=], [<] są dobrze ufundowane. *)

(* begin hide *)
Lemma le_not_Acc :
  forall n : nat, Acc le n -> False.
Proof.
  induction 1. apply (H0 x). reflexivity.
Qed.

Lemma le_not_wf : ~ well_founded le.
Proof.
  unfold well_founded. intro.
  apply le_not_Acc with 0. apply H.
Qed.

Lemma wf_lt : well_founded lt.
Proof.
  unfold well_founded.
  induction x as [| n'].
    constructor. inversion 1.
    constructor. intros a Ha. constructor. intros b Hb.
      apply IHn'. apply Nat.lt_le_trans with a.
        assumption.
        apply le_S_n. assumption.
Defined.

(* end hide *)

(** **** Ćwiczenie *)

(** Pokaż, że relacja dobrze ufundowana jest antyzwrotna oraz zinterpretuj
    ten fakt (tzn. powiedz, o co tak naprawdę chodzi w tym stwierdzeniu). *)

(* begin hide *)
Lemma Acc_antirefl :
  forall (A : Type) (R : A -> A -> Prop) (x : A),
    Acc R x -> ~ R x x.
Proof.
  induction 1. intro. apply (H0 x); assumption.
Qed.
(* end hide *)

Lemma wf_antirefl :
  forall (A : Type) (R : A -> A -> Prop),
    well_founded R -> forall x : A, ~ R x x.
(* begin hide *)
Proof.
  unfold well_founded. intros.
  apply Acc_antirefl. apply H.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Sprawdź, czy dobrze ufundowana jest następująca relacja porządku:
    wszystkie liczby parzyste są mniejsze niż wszystkie liczby nieparzyste,
    zaś dwie liczby o tej samej parzystości porównujemy według zwykłego
    porządku [<]. *)

(* begin hide *)
(** TODO *)
(* end hide *)

(** **** Ćwiczenie *)

(** Sprawdź, czy dobrze ufundowana jest następująca relacja porządku
    (mam nadzieję, że obrazek jest zrozumiały):
    0 < 1 < ... < ω < ω + 1 < ... < 2 * ω

     Oczywiście najpierw musisz wymyślić, w jaki sposób zdefiniować taką
     relację. Uwaga: istnieje bardzo sprytne rozwiązanie. *)

(* begin hide *)
Module Ex.

Require Import Lia.

Inductive T : Type :=
    | from0 : nat -> T
    | fromω : nat -> T
    | ωω : T.

Definition R (x y : T) : Prop :=
match x, y with
    | from0 n, from0 m => n < m
    | from0 _, _ => True
    | fromω _, from0 _ => False
    | fromω n, fromω m => n < m
    | fromω _, _ => True
    | ωω, _ => False
end.

Lemma R_trans :
  forall a b c : T, R a b -> R b c -> R a c.
Proof.
  induction a as [n | n |];
  destruct b as [m | m |],
           c as [k | k |];
  cbn; lia.
Qed.

Lemma Acc_from0 :
  forall n : nat, Acc R (from0 n).
Proof.
  induction n as [| n']; cbn.
    constructor. destruct y; inversion 1.
    constructor. destruct y; inversion 1; subst.
      assumption.
      inversion IHn'. constructor. intros. apply H0.
        eapply R_trans; eauto.
Qed.

Lemma Acc_fromω :
  forall n : nat, Acc R (fromω n).
Proof.
  induction n as [| n']; cbn.
    constructor. destruct y; inversion 1. apply Acc_from0.
    constructor. destruct y; inversion 1; subst.
      apply Acc_from0.
      assumption.
      inversion IHn'. constructor. intros. apply H0.
        eapply R_trans; eauto.
Qed.

Lemma wf_R : well_founded R.
Proof.
  unfold well_founded.
  destruct x as [m | m |].
    apply Acc_from0.
    apply Acc_fromω.
    constructor. destruct y; inversion 1.
      apply Acc_from0.
      apply Acc_fromω.
Qed.

End Ex.
(* end hide *)

(** Nasza bajka powoli zbliża się do końca. Czas udowodnić ostateczne
    twierdzenie, do którego dążyliśmy: jeżeli układ kostek [R] jest
    niespartaczony (czyli gdy każda kostka jest dostępna), to każda
    kostka się przewraca. *)

Theorem well_founded_rect :
  forall
    (A : Type) (R : A -> A -> Prop)
    (wf : well_founded R) (P : A -> Type),
      (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
        forall x : A, P x.
Proof.
  intros A R wf P H x.
  unfold well_founded in wf. specialize (wf x).
  induction wf as [x _ IH].
  apply H. exact IH.
Defined.

(** Podobnie jak poprzednio, [A] to typ kostek domina, [R] to układ kostek,
    zaś [wf : well_founded R] to dowód na to, że układ jest niespartaczony.
    [P : A -> Type] to dowolna rodzina typów indeksowana przez [A], ale
    możemy myśleć, że [P x] znaczy "kostka x się przewraca". Mamy jeszcze
    hipotezę, która głosi, że kostka [x] przewraca się, gdy przewraca się
    każda kostka, która poprzedza ją w układzie [R].

    Dowód jest banalny. Zaczynamy od wprowadzenia zmiennych i hipotez do
    kontekstu. Następnie odwijamy definicję [well_founded]. Teraz hipoteza
    [wf] głosi, że każde [x : A] jest dostępne. Skoro tak, to specjalizujemy
    ją dla naszego konkretnego [x], które mamy w kontekście.

    Wiemy już zatem, że [x] jest dostępne. Jest to kluczowy fakt, gdyż
    oznacza to, że wszystkie kostki domina poprzedzające [x] również są
    dostępne. Co więcej, [Acc] jest zdefiniowane induktywnie, więc możemy
    pokazać, że [x] się przewraca, właśnie przez indukcję po dowodzie
    dostępności [x].

    Przypadek jest jeden (co nie znaczy, że nie ma przypadków bazowych -
    są nimi kostki domina, których nic nie poprzedza): musimy pokazać, że
    [x] się przewraca przy założeniu, że wszystkie poprzedzające je kostki
    również się przewracają. To, że [x] się przewraca, wynika z hipotezy
    [H]. Pozostaje nam jedynie pokazać, że przewraca się wszystko, co jest
    przed nim, ale to jest faktem na mocy hipotezy indukcyjnej [IH]. *)

Theorem well_founded_ind :
  forall
    (A : Type) (R : A -> A -> Prop)
    (wf : well_founded R) (P : A -> Type),
      (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
        forall x : A, P x.
Proof.
  intros A R wf P H x.
  apply (well_founded_rect _ _ wf _ H).
Qed.

(** Poprzednie twierdzenie, czyli [well_founded_rect], to twierdzenie o
    rekursji dobrze ufundowanej. Powyższe, czyli [well_founded_ind],
    które jest jego specjalizacją dla relacji binarnych (czyli bytów o
    typie [A -> A -> Prop]), możemy nazwać twierdzeniem o indukcji dobrze
    ufundowanej.

    Upewnij się, że dobrze rozumiesz oba twierdzenia, a także pojęcia
    dostępności i dobrego ufundowania, gdyż są one bardzo ważne przy
    rozwiązywaniu poważniejszych problemów.

    Co to są "poważniejsze problemy"? Mam oczywiście na myśli dowodzenie
    twierdzeń i definiowanie funkcji, którego nie da się zrobić za pomocą
    prostej indukcji albo banalnego dopasowania do wzorca. W tego typu
    sytuacjach nieodzowne będzie skorzystanie z indukcji i rekursji
    dobrze ufundowanej, o czym przekonamy się już natychmiast zaraz. *)

Require Import Lia.

Definition div : nat -> nat -> nat.
Proof.
  apply (@well_founded_rect nat lt wf_lt (fun _ => nat -> nat)).
  intros n IH m.
  destruct (le_lt_dec (S m) n).
    2: exact 0.
    refine (1 + IH (n - S m) _ m). abstract lia. Show Proof.
Defined.

(* begin hide *)

(** TODO: wprowadzić kombinator [abstract] za pierwszym razem, gdy użyta
    zostanie taktyka [lia]. *)

(* end hide *)

(** Poważniejszym problemem jest bowiem definicja dzielenia, z którą borykamy
    się od samiuśkiego początku niniejszego rozdziału. Powyższy kawałek kodu
    jest (nieudaną, jak się okaże) próbą uporania się z tym problemem.

    Definiować będziemy w trybie dowodzenia, gdyż przy posługiwaniu się
    rekursją dobrze ufundowaną zazwyczaj tak jest dużo łatwiej. Zaczynamy
    od zaaplikowania reguły rekursji dobrze ufundowanej dla typu [nat] i
    porządku [<] (no i rzecz jasna [wf_lt], czyli dowodu na to, że [lt]
    jest dobrze ufundowany - bez tego ani rusz). Po typach widać, że
    rekursja będzie się odbywać po pierwszym argumencie. Wprowadzamy też
    zmienne do kontekstu. *)

Check le_lt_dec.
(* ===> le_lt_dec : forall n m : nat, {n <= m} + {m < n} *)

(** Następnie musimy sprawdzić, czy dzielna (czyli [n]) jest mniejsza od
    dzielnika (czyli [S m] - zauważ, że definiujemy tutaj "sprytną" wersję
    dzielenia, tzn. [div n m] = [n/(m + 1)], żeby uniknąć problemów z
    dzieleniem przez [0]). Jeżeli tak, wynikiem jest [0]. Jeżeli nie,
    wynikiem jest wynik wywołania rekurencyjnego na argumencie [n - S m]
    powiększony o [1].

    Na koniec musimy jeszcze tylko pokazać, że argument wywołania
    rekurencyjnego, czyli [n - S m], jest mniejszy od argumentu
    obecnego wywołania, czyli [n]. Żeby za bardzo nie pobrudzić
    sobie rąk arytmetyką, zostawiamy ten cel taktyce [lia], ale
    zawijamy jej użycie w kombinator [abstract], który zapobiega
    "wylaniu się" rozumowania taktyki [lia] do definicji. *)

Print div.
(* ===>
  div =
  well_founded_rect nat lt wf_lt (fun _ : nat => nat -> nat)
    (fun (n : nat)
         (IH : forall y : nat, y < n -> nat -> nat)
         (m : nat) =>
    let s := le_lt_dec (S m) n in
      match s with
          | left l => 1 + IH (n - S m) (div_subproof n m l) m
          | right _ => 0
      end)
    : nat -> nat -> nat *)

Check div_subproof.
(* ===> div_subproof
          : forall n m : nat, S m <= n -> n - S m < n *)

Print div_subproof.
(* ===> dużo różnych głupot, szkoda pisać *)

(** Mówiąc wprost, taktyka [abstract lia] zamiast wstawiać do definicji
    całe rozumowanie, tak jak zrobiłaby to taktyka [lia], dowodzi sobie
    na boku odpowiedni lemat arytmetyczny, nazywa go [div_subproof] i
    dowodzi celu za jego pomocą. *)

Compute div 5 2.
(* ===> = 1 : nat *)

(** Jak widać, definicja przechodzi bez problemu, a nasza funkcja elegancko
    się oblicza (pamiętaj, że [div 5 2] to tak naprawdę [5/3], więc wynikiem
    faktycznie powinno być [1]).

    Jednak nie samymi definicjami żyje człowiek - czas trochę podowodzić.
    Spodziewamy się wszakże, że nasze dzielenie spełnia wszystkie
    właściwości, których się po nim spodziewamy, prawda? *)

Lemma div_0_r :
  forall n : nat, div n 0 = n.
Proof.
  apply (well_founded_ind _ _ wf_lt).
  intros. unfold div. cbn. (* O Jezu, a cóż to za wojacy? *)
Abort.

(** Niestety jednak, jak to w życiu, nie ma kolorowo.

    Powyższy lemat głosi, że [n/1 = n]. Ponieważ [div] jest zdefiniowane
    za pomocą rekursji dobrze ufundowanej, to dowodzić będziemy oczywiście
    za pomocą indukcji dobrze ufundowanej. Tak, będziemy dowodzić, hmmm...
    cóż... tylko jak?

    Sytuacja wygląda beznadziejnie. Nie żeby lemat był nieprawdziwy - co to,
    to nie. Po prostu próba odwinięcia definicji i policzenia czegokolwiek
    daje inny wynik, niż byśmy chcieli - część definicji ukryta dotychczas
    w [div_subproof] wylewa się i zaśmieca nam ekran.

    Problem nie pochodzi jednak od taktyki [lia] (ani od [abstract lia]).
    Jest on dużo ogólniejszy i polega na tym, że wewnątrz definicji funkcji
    pojawiają się dowody, które są wymagane przez [well_founded_rect], ale
    które zaorywują jej obliczeniową harmonię.

    Nie jesteśmy jednak (jeszcze) skazani na porażkę. Spróbujemy uporać się
    z tą przeszkodą dzięki _równaniu rekurencyjnemu_. Równanie rekurencyjne
    to lemat, którego treść wygląda dokładnie tak, jak pożądana przez nas
    definicja funkcji, ale która nie może służyć jako definicja z różnych
    powodów, np. dlatego że nie jest strukturalnie rekurencyjna. Dzięki
    równaniu rekurencyjnemu możemy użyć taktyki [rewrite] do przepisania
    wystąpień funkcji [div] do pożądanej postaci zamiast rozwijać je za
    pomocą taktyki [unfold] lub obliczać za pomocą [cbn]. *)

Lemma div_eq :
  forall n m : nat,
    div n m = if n <? S m then 0 else S (div (n - S m) m).
Proof.
  apply (well_founded_ind _ _ wf_lt (fun _ => forall m : nat, _)).
  intros. unfold div. cbn. (* O Jezu, a cóż to za hołota? *)
Admitted.

(** Powyższe równanie dokładnie opisuje, jak powinna zachowywać się funkcja
    [div], ale za definicję służyć nie może, gdyż Coq nie byłby w stanie
    rozpoznać, że [n - S m] jest podtermem [n]. Zauważ, że używamy tu [<?]
    (czyli [ltb]) zamiast [le_lt_dec]. Możemy sobie na to pozwolić, gdyż
    użycie [le_lt_dec] w faktycznej definicji wynikało jedynie z tego, że
    potrzebowaliśmy dowodu odpowiedniego faktu arytmetycznego, żeby użyć
    go jako argumentu wywołania rekurencyjnego.

    Niestety próba udowodnienia tego równania rekurencyjnego musi skończyć
    się taką samą porażką, jak próba udowodnienia [div_0_r]. Przyczyna jest
    taka sama jak ostatnio. Zresztą, naiwnym byłoby spodziewać się, że nam
    się uda - zarówno [div_0_r], jak i [div_eq] to nietrywialne właściwości
    funkcji [div], więc gdybyśmy potrafili udowodnić równanie rekurencyjne,
    to z dowodem [div_0_r] również poradzilibyśmy sobie bez problemu.

    Żeby jednak przekonać się o użyteczności równania rekurencyjnego, jego
    "dowód" kończymy za pomocą komendy [Admitted], która przerywa dowód i
    zamienia twierdzenie w aksjomat. Dzięki temu za chwilę zobaczymy, ile
    moglibyśmy zdziałać, mając równanie rekurencyjne. *)

Lemma div_0_r :
  forall n : nat, div n 0 = n.
Proof.
  apply (well_founded_ind _ _ wf_lt).
  intros n IH. rewrite div_eq.
  destruct (Nat.ltb_spec n 1).
    lia.
    rewrite IH; lia.
Qed.

(** Jak widać, dzięki równaniu rekurencyjnemu dowody przebiegają dość gładko.
    W powyższym zaczynamy od indukcji dobrze ufundowanej po [n] (przy użyciu
    relacji [<] i dowodu [wf_lt]), wprowadzamy zmienne do kontekstu, po czym
    przepisujemy równanie rekurencyjne. Po przeprowadzeniu analizy przypadków
    kończymy za pomocą rozumowań arytmetycznych, używając być może hipotezy
    indukcyjnej. *)

(** **** Ćwiczenie *)

(** Zgadnij, jakie jest polecenie tego ćwiczenia, a następnie wykonaj je. *)

Lemma div_n_n :
  forall n : nat, div (S n) n = 1.
(* begin hide *)
Proof.
  intros n.
  rewrite div_eq, Nat.ltb_irrefl, minus_diag.
  cbn. reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Sprawdź, czy dobrze ufundowane są relacje [le'] i [lt']. Uwaga:
    pierwsze zadanie jest bardzo łatwe, drugie jest piekielnie trudne.
    Jeżeli nie potrafisz rozwiązać go formalnie w Coqu, zrób to na
    kartce nieformalnie - będzie dużo łatwiej.*)

Definition le' (f g : nat -> nat) : Prop :=
  forall n : nat, f n <= g n.

Definition lt' (f g : nat -> nat) : Prop :=
  forall n : nat, f n < g n.

(* begin hide *)
Lemma not_wf_le' : ~ well_founded le'.
Proof.
  intro. apply (wf_antirefl _ _ H id).
  unfold le', id. intro. constructor.
Qed.

Lemma wf_lt' :
  well_founded lt'.
Proof.
  unfold well_founded.
  intro f.
  pose (n := f 0); assert (n = f 0) by reflexivity; clearbody n.
  revert n f H.
  apply (@well_founded_ind _ _ wf_lt
        (fun n => forall f, n = f 0 -> Acc lt' f)).
  intros n IH f Heq. constructor. intros g Hlt.
  unfold lt' in Hlt.
  apply IH with (g 0).
    specialize (Hlt 0). subst. assumption.
    reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Niech [B : Type] i niech [R : B -> B -> Prop] będzie relacją dobrze
    ufundowaną. Zdefiniuj po współrzędnych relację porządku na funkcjach
    o typie [A -> B] i rozstrzygnij, czy relacja ta jest dobrze ufundowana.

    Uwaga: w zależności od okoliczności to zadanie może być trudne lub
    łatwe. *)

(* begin hide *)
Module Ex'.

Definition funord
  (A : Type) {B : Type} (R : B -> B -> Prop) (f g : A -> B) : Prop :=
    forall x : A, R (f x) (g x).

Lemma Acc_antirefl :
  forall (A : Type) (R : A -> A -> Prop) (x : A),
    Acc R x -> ~ R x x.
Proof.
  induction 1. intro. apply (H0 x); assumption.
Qed.

Lemma wf_funord_empty :
  forall (A B : Type) (R : B -> B -> Prop),
    (A -> False) -> ~ well_founded (funord A R).
Proof.
  unfold well_founded.
  intros A B R Hempty H.
  pose (f := fun a : A => match Hempty a with end : B); clearbody f.
  apply (Acc_antirefl _ (funord A R) f).
    apply H.
    unfold funord. intro. contradiction.
Qed.

Lemma wf_funord_nonempty :
  forall (A B : Type) (R : B -> B -> Prop) (a : A),
    well_founded R -> well_founded (funord A R).
Proof.
  unfold well_founded.
  intros A B R a Hwf f.
  pose (b := f a).
  assert (b = f a) by reflexivity; clearbody b.
  revert b f H.
  apply (@well_founded_ind B R Hwf
    (fun b => forall f, b = f a -> Acc (funord A R) f)).
  intros b IH f Heq. constructor. intros g Hord.
  apply IH with (g a).
    unfold funord in Hord. specialize (Hord a). subst. apply Hord.
    reflexivity.
Qed.

End Ex'.
(* end hide *)

(** **** Ćwiczenie *)

(** Pokaż, że jeżeli kodziedzina funkcji [f : A -> B] jest dobrze ufundowana
    za pomocą relacji [R : B -> B -> Prop], to jej dziedzina również jest
    dobrze ufundowana. *)

Lemma wf_inverse_image :
  forall (A B : Type) (f : A -> B) (R : B -> B -> Prop),
    well_founded R -> well_founded (fun x y : A => R (f x) (f y)).
(* begin hide *)
Proof.
  unfold well_founded.
  intros A B f R H x.
  pose (b := f x). assert (b = f x) by reflexivity. clearbody b.
  specialize (H b). revert x H0. induction H. rename x into b.
  intros x Heq. constructor. intros.
  eapply H0. rewrite Heq.
    eauto.
    reflexivity.
Defined.
(* end hide *)

(** * Indukcja wykresowa *)

(** Skoro nie dla psa kiełbasa, to musimy znaleźć jakiś sposób na
    udowodnienie równania rekurencyjnego dla [div]. Zamiast jednak głowić
    się nad równaniami rekurencyjnymi albo nad funkcją [div], zastanówmy
    się w pełnej ogólności: jak dowodzić właściwości funkcji rekurencyjnych?

    No przez indukcję, czy to nie oczywiste? Jasne, ale jak dokładnie owa
    indukcja ma wyglądać? Odpowiedź jest prostsza niż można się spodziewać.
    Otóż gdy kupujesz but, ma on pasować do twojej stopy, zaś gdy kupujesz
    gacie, mają one pasować do twojej dupy. Podobnie jest z indukcją: jej
    kształt ma pasować do kształtu rekursji, za pomocą której zdefiniowana
    została funkcja.

    Czym jest "kształt" rekursji (i indukcji)? Jest to raczej poetyckie
    pojęcie, które odnosi się do tego, jak zdefiniowano funkcję - ile
    jest przypadków, podprzypadków, podpodprzypadków etc., w jaki sposób
    są w sobie zagnieżdżone, gdzie są wywołania rekurencyjne, ile ich
    jest i na jakich argumentach etc.

    Dowiedziawszy się, czym jest kształt rekursji i indukcji, powinniśmy
    zacząć szukać sposobu na dopasowanie kształtu indukcji w naszych
    dowodach do kształtu rekursji funkcji. Dotychczas indukcję zawsze
    robiliśmy po argumencie głównym, zaś z potencjalnymi niedopasowaniami
    kształtów radziliśmy sobie robiąc ad hoc analizy przypadków, które
    uznaliśmy za stosowne.

    I tutaj przyda nam się nieco konceptualnej spostrzegawczości. Zauważyć
    nam bowiem trzeba, że robiąc indukcję po argumencie głównym, kształt
    indukcji odpowiada kształtowi typu argumentu głównego. Skoro zaś mamy
    dopasować go do kształtu rekursji funkcji, to nasuwa nam się oczywiste
    pytanie: czy da się zdefiniować typ, który ma taki sam kształt, jak
    definicja danej funkcji?

    Odpowiedź brzmi: nie, ale da się zdefiniować rodzinę typów
    (a konkretniej pisząc, rodzinę zdań, czyli relację) o takiej właściwości.
    Owa relacja zwie się wykresem funkcji. Jaki ma to związek z bazgrołami
    znanymi ci ze szkoły (zakładam, że wiesz, że wykresem funkcji liniowej
    jest prosta, wykresem funkcji kwadratowej jest parabola, a wykresy sinusa
    i cosinusa to takie wesołe szlaczki)?

    To, co w szkole nazywa się wykresem funkcji, jest jedynie graficznym
    przedstawieniem prawdziwego wykresu, czyli relacji. Samo słowo "wykres",
    wywodzące się w oczywisty sposób od kreślenia, sugeruje, że myślenie o
    wykresie jak o obrazku było pierwsze, a koncepcja wykresu jako relacji
    jest późniejsza.

    W ramach ciekawostki być może warto napisać, że w dawnych czasach
    matematycy silnie utożsamiali funkcję z jej wykresem (w sensie
    obrazka) i przez to byty, których wykresu nie dało się narysować,
    nie były uznawane za funkcje.

    W nieco późniejszym czasie zaszły jednak niemałe zmiany i obecnie
    panującym zabobonem jest utożsamianie funkcji z wykresem (w sensie
    relacji), przez co za funkcje uznawane są także byty, których nie
    da się obliczyć lub nikt nie potrafi pokazać, że terminują (takich
    jak np. "funkcja" Collatza).

    Gdybyś zgłupiał od powyższych czterech akapitów, to przypominam, że
    dla nas zawarte w nich pojęcia oznaczają to:
    - Funkcja to byt, którego typem jest [A -> B] lub [forall x : A, B x].
      Można dać jej coś na wejściu i uzyskać wynik na wyjściu, tzn. można
      ją obliczyć. W Coqu wszystkie funkcje prędzej czy później kończą się
      obliczać.
    - Wykres funkcji to relacja opisująca związek argumentu funkcji z jej
      wynikiem. Każda funkcja ma wykres, ale nie każda relacja jest
      wykresem jakiejś funkcji.
    - Jeżeli typy [A] i [B] da się jakoś sensownie narysować, to możemy
      narysować obrazek przedstawiający wykres funkcji.*)

Definition is_graph
  {A B : Type} (f : A -> B) (R : A -> B -> Prop) : Prop :=
    forall (a : A) (b : B), R a b <-> f a = b.

(** Żeby było nam raźniej, tak wygląda formalna definicja stwierdzenia,
    że relacja [R] jest wykresem funkcji [f]. Uwaga: jeżeli funkcja
    bierze więcej niż jeden argument (tzn. ma typ [A1 -> ... -> An -> B]),
    to wtedy do powyższej definicji musimy wrzucić jej zmodyfikowaną
    wersję o typie [A1 * ... * An -> B]. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [graph_of], która każdej funkcji przyporządkowuje
    jej wykres. Następnie udowodnij, że faktycznie jest to wykres tej
    funkcji. *)

(* begin hide *)
Definition graph_of {A B : Type} (f : A -> B) : A -> B -> Prop :=
  fun (a : A) (b : B) => f a = b.
(* end hide *)

Lemma is_graph_graph_of :
  forall (A B : Type) (f : A -> B),
    is_graph f (graph_of f).
(* begin hide *)
Proof.
  compute. split; trivial.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Wymyśl typy [A] i [B] oraz relację o typie [A -> B -> Prop], która nie
    jest wykresem żadnej funkcji. Następnie udowodnij formalnie, że nie
    mylisz się. *)

(* begin hide *)
Definition complete (_ _ : bool) : Prop := True.

Lemma complete_not_graph :
  forall f : bool -> bool,
    ~ is_graph f complete.
Proof.
  unfold is_graph, complete. intros f H.
  destruct (H true (negb (f true))).
  specialize (H0 I).
  destruct (f true); inversion H0.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Pokaż, że wszystkie wykresy danej funkcji są równoważne w poniższym
    sensie. *)

Lemma graph_unique :
  forall {A B : Type} (f : A -> B) (R S : A -> B -> Prop),
    is_graph f R -> is_graph f S ->
      forall (a : A) (b : B), R a b <-> S a b.
(* begin hide *)
Proof.
  unfold is_graph.
  intros * HR HS; split; intros.
    rewrite HS, <- HR. assumption.
    rewrite HR, <- HS. assumption.
Qed.
(* end hide *)

(** Skoro już wiemy czym są wykresy funkcji, czas nauczyć się definiować
    induktywne wykresy o kształtach odpowiednich dla naszych niecnych
    celów. *)

Check div_eq.
(* ===> div_eq
        : forall n m : nat,
            div n m = if n <? S m then 0 else S (div (n - S m) m) *)

(** Zwróćmy tylko uwagę na fakt, że mówiąc o kształcie rekursji (lub po
    prostu o kształcie definicji) [div] nie mamy na myśli faktycznej
    definicji, która używa rekursji dobrze ufundowanej i jak już wiemy,
    jest dość problematyczna, lecz "docelowej" definicji, którą wyraża
    między innymi równanie rekurencyjne. *)

Inductive divG : nat -> nat -> nat -> Prop :=
    | divG_lt : forall {n m : nat}, n < S m -> divG n m 0
    | divG_ge :
        forall n m r : nat,
          n >= S m -> divG (n - S m) m r -> divG n m (S r).

(** [div] jest funkcją typu [nat -> nat -> nat], więc jej wykres to relacja
    typu [nat -> nat -> nat -> Prop]. Dwa pierwsze argumenty relacji
    reprezentują wejście, zaś ostatni argument reprezentuje wyjście, tzn.
    chcemy, żeby [divG n m r] było równoważne [div n m = r].

    Z równania rekurencyjnego widać, że mamy dwa przypadki, czyli konstruktory
    też będą dwa. Jeden odpowiada przypadkowi, gdy [n < S m], tzn. dzielna jest
    mniejsza niż dzielnik (pamiętaj, że [div n m] oznacza [n/(m + 1)], żeby
    uniknąć problemów z dzieleniem przez zero). Konkluzją jest wtedy
    [divG n m 0], tzn. argumentami są [n] i [m], zaś wynikiem jest [0].

    Drugi przypadek to przyadek rekurencyjny. Jeżeli [n >= S m], tzn. dzielna
    jest większa lub równa od dzielnika, to konkluzją jest [divG n m (S r)],
    tzn. argumentami są [n] i [m], zaś wynikiem dzielenia jest [S r]. Czym
    jest [r]? Jest ono skwantyfikowane w tym konstruktorze i pojawia się w
    przesłance [divG (n - S m) m r], która mówi, że wynikiem dzielenia
    [n - S m] przez [m] jest [r]. Przesłanka ta jest wykresowym odpowiednikiem
    wywołania rekurencyjnego. *)

(** **** Ćwiczenie *)

(** Mimo, że wszystkie wykresy danej funkcji są równoważne, to zdefiniować
    można je na wiele różnych sposobów. W zależności od sposobu definicja
    może być użyteczna lub nie, np. przy definicjach induktywnych dostajemy
    za darmo regułę indukcji.

    Podaj inną definicję wykresu funkcji [div], która nie używa typów
    induktywnych (ani nie odwołuje się do samej funkcji [div] - to byłoby
    za łatwe). Użyj kwantyfikatora egzystencjalnego, mnożenia, dodawania
    oraz relacji równości (i niczego więcej). Nazwij ją [divG'].

    Na razie nie musisz dowodzić, że wykres faktycznie jest wykresem [div]
    (póki co jest to za trudne), co oczywiście nie znaczy, że wolno ci się
    mylić - uzasadnij nieformalnie, że wykres faktycznie opisuje funkcję
    [div]. Do dowodu formalnego wrócimy później. *)

(* begin hide *)
Definition divG' (n m r : nat) : Prop :=
  exists q : nat, n = r * S m + q.
(* end hide *)

(** Mamy wykres. Fajnie, ale co możemy z nim zrobić? Jeszcze ważniejsze
    pytanie brzmi zaś: co powinniśmy z nim zrobić? *)

Lemma divG_det :
  forall n m r1 r2 : nat,
    divG n m r1 -> divG n m r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; inversion 1; subst.
    reflexivity.
    1-2: lia.
    f_equal. apply IHdivG. assumption.
Qed.

(** Pierwsza czynność po zdefiniowaniu wykresu, którą powinniśmy wykonać,
    to sprawdzenie, czy ów wykres jest relacją deterministyczną. Relacja
    deterministyczna to taka, której ostatni argument jest zdeterminowany
    przez poprzednie.

    Jeżeli wykres jest deterministyczny to dobrze, a jeżeli nie, to definicja
    na pewno jest błędna, bo wykres ma opisywać funkcję, a żadna funkcja nie
    może dla tych samych argumentów dawać dwóch różnych wyników. Relacjom
    deterministycznym (i nie tylko) przyjrzymy się dokładniej w rozdziale o
    relacjach.

    Dowód nie jest zbyt trudny. Robimy indukcję po dowodzie hipotezy
    [divG n m r1], ale musimy pamiętać, żeby wcześniej zgeneralizować
    [r2], bo w przeciwnym przypadku nasza hipoteza indukcyjna będzie
    za mało ogólna. *)

Lemma divG_correct :
  forall n m : nat,
    divG n m (div n m).
Proof.
  apply (well_founded_ind _ _ wf_lt (fun _ => forall m : nat, _)).
  intros n IH m.
  rewrite div_eq. destruct (Nat.ltb_spec0 n (S m)).
    constructor. assumption.
    constructor.
      lia.
      apply IH. lia.
Qed.

(** Kolejna rzecz do udowodnienia to twierdzenie o poprawności, które mówi,
    że [divG] faktycznie jest wykresem [div]. Zauważ, że moglibyśmy równie
    dobrze sformułować je za pomocą [is_graph], ale tak jak wyżej będzie
    praktyczniej.

    Dowód zaczynamy od indukcji dobrze ufundowanej, po czym wprowadzamy
    zmienne do kontekstu i... aj waj, cóż to takiego? Używamy równania
    rekurencyjnego do rozpisania [div], po czym kończymy przez rozważenie
    przypadków.

    Ten dowód pokazuje, że nie udało nam się osiągnąć celu, który sobie
    postawiliśmy, czyli udowodnienia [div_eq] za pomocą specjalnej reguły
    indukcji. Niestety, bez równania rekurencyjnego nie da się udowodnić
    twierdzenia o poprawności. Nie powinniśmy jednak za bardzo się tym
    przejmować - uszy do góry. Póki co dokończmy poszukiwań ostatecznej
    reguły indukcji, a tym nieszczęsnym równaniem rekurencyjnym zajmiemy
    się później. *)

Lemma divG_complete :
  forall n m r : nat,
    divG n m r -> r = div n m.
Proof.
  intros. apply divG_det with n m.
    assumption.
    apply divG_correct.
Qed.

(** Kolejną, ostatnią już rzeczą, którą powinniśmy zrobić z wykresem, jest
    udowodnienie twierdzenia o pełności, które głosi, że jeżeli argumentom
    [n] i [m] odpowiada na wykresie wynik [r], to [r] jest równe [div n m].
    Dowód jest banalny i wynika wprost z twierdzeń o determinizmie i
    poprawności.

    I po co nam to było? Ano wszystkie fikołki, które zrobiliśmy, posłużą
    nam jako lematy do udowodnienia reguły indukcji wykresowej dla [div].
    Co to za reguła, jak wygląda i skąd ją wziąć? *)

Check divG_ind.
(* ===>
  divG_ind :
    forall
      P : nat -> nat -> nat -> Prop,
      (forall n m : nat, n < S m -> P n m 0) ->
      (forall n m r : nat,
          n >= S m -> divG (n - S m) m r ->
            P (n - S m) m r -> P n m (S r)) ->
        forall n m r : nat, divG n m r -> P n m r *)

(** Pierwowzorem reguły indukcji wykresowej dla danej funkcji jest reguła
    indukcji jej wykresu. Reguła indukcji dla [div] to w sumie to samo co
    powyższa reguła, ale z [r] wyspecjalizowanym do [div n m]. Chcemy też
    pozbyć się niepotrzebnej przesłanki [divG n m r] (po podstawieniu za
    [r] ma ona postać [divG n m (div n m)]), gdyż nie jest potrzebna -
    jest zawsze prawdziwa na mocy twierdzenia [divG_correct]. *)

Lemma div_ind :
  forall
    (P : nat -> nat -> nat -> Prop)
    (Hlt : forall n m : nat, n < S m -> P n m 0)
    (Hge :
      forall n m : nat,
        n >= S m -> P (n - S m) m (div (n - S m) m) ->
          P n m (S (div (n - S m) m))),
      forall n m : nat, P n m (div n m).
Proof.
  intros P Hlt Hge n m.
  apply divG_ind.
    assumption.
    intros. apply divG_complete in H0. subst. apply Hge; assumption.
    apply divG_correct.
Qed.

(** Przydałaby się jednak także i filozoficzna interpretacja reguły. Pozwoli
    nam ona dowodzić zdań, które zależą od [n m : nat] i wyniku dzielenia,
    czyli [div n m].

    Są dwa przypadki, jak w docelowej definicji [div]. Gdy [n < S m], czyli
    dzielna jest mniejsza od dzielnika, wystarczy udowodnić [P n m 0], bo
    wtedy [div n m] wynosi [0]. W drugim przypadku, czyli gdy [n >= S m],
    wystarczy udowodnić [P n m (S (div (n - S m) m))] (bo taki jest wynik
    [div n m] dla [n >= S m]) przy założeniu, że [P] zachodzi dla [n - S m],
    [m] oraz [div (n - S m) m], bo takie są argumenty oraz wynik wywołania
    rekurencyjnego.

    Dowód jest prosty. Wprowadzamy zmienne do kontekstu, a następnie za pomocą
    zwykłego [apply] używamy reguły indukcji [divG_ind] - jako rzekło się
    powyżej, reguła [div_ind] nie jest niczym innym, niż lekką przeróbką
    [divG_ind].

    Mamy trzy podcele. Pierwszy odpowiada przesłance [Hlt]. Drugi to
    przesłanka [Hge], ale musimy wszędzie podstawić [div (n' - S m') m']
    za [r] - posłuży nam do tego twierdzenie o pełności. Trzeci to zbędna
    przesłanka [divG n m (div n m)], którą załatwiamy za pomocą twierdzenia
    o poprawności.

    Włala (lub bardziej wykwintnie: voilà)! Mamy regułę indukcji wykresowej
    dla [div]. Zobaczmy, co i jak można za jej pomocą udowodnić. *)

Lemma div_le :
  forall n m : nat,
    div n m <= n.
Proof.
  apply (div_ind (fun n m r : nat => r <= n)); intros.
    apply le_0_n.
    lia.
Qed.

(** **** Ćwiczenie *)

(** Udowodnij twierdzenie [div_le] za pomocą indukcji dobrze ufundowanej
    i równania rekurencyjnego, czyli bez użycia indukcji wykresowej. Jak
    trudny jest ten dowód w porównaniu do powyższego? *)

Lemma div_le' :
  forall n m : nat,
    div n m <= n.
(* begin hide *)
Proof.
  apply (well_founded_ind _ _ wf_lt (fun n => forall m : nat, _)).
  intros n IH m.
  rewrite div_eq. destruct (Nat.ltb_spec n (S m)).
    apply le_0_n.
    specialize (IH (n - S m) ltac:(lia) m). lia.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij za pomocą indukcji wykresowej, że twój alternatywny
    wykres funkcji [div] z jednego z poprzednich ćwiczeń faktycznie
    jest wykresem [div].

    Następnie udowodnij to samo za pomocą indukcji dobrze ufundowanej i
    równania rekurencyjnego. Która metoda dowodzenia jest lepsza (nie,
    to pytanie nie jest subiektywne - masz udzielić jedynej słusznej
    odpowiedzi). *)

Lemma divG'_div :
  forall n m : nat,
    divG' n m (div n m).
(* begin hide *)
Proof.
  apply (div_ind divG'); unfold divG'; intros.
    exists n. cbn. reflexivity.
    destruct H0 as [q IH]. exists q. cbn. lia.
Qed.
(* end hide *)

Lemma divG'_div' :
  forall n m : nat,
    divG' n m (div n m).
(* begin hide *)
Proof.
  apply (well_founded_ind _ _ wf_lt (fun _ => forall m : nat, _)).
  intros n IH m. unfold divG' in *.
  rewrite div_eq. destruct (Nat.ltb_spec n (S m)).
    exists n. cbn. reflexivity.
    destruct (IH (n - S m) ltac:(lia) m) as [q IHq].
      exists q. cbn. lia.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Napisz funkcję [split] o sygnaturze
    [split (n : nat) {A : Type} (l : list A) : option (list A * list A)],
    która rozdziela listę [l] na blok o długości [n] i resztę listy, lub
    zwraca [None] gdy lista jest za krótka.

    Następnie udowodnij dla tej funkcji regułę indukcji wykresowej i użyj
    jej do udowodnienia kilku lematów.

    Wszystkie te rzeczy przydadzą się nam w jednym z kolejnych zadań. *)

(* begin hide *)
Fixpoint split
  {A : Type} (n : nat) (l : list A) : option (list A * list A) :=
match n, l with
    | 0, _ => Some ([], l)
    | S _, [] => None
    | S n', h :: t =>
        match split n' t with
            | None => None
            | Some (l1, l2) => Some (h :: l1, l2)
        end
end.

Inductive splitG {A : Type} :
  nat -> list A -> option (list A * list A) -> Prop :=
    | splitG_0 :
        forall l : list A, splitG 0 l (Some ([], l))
    | splitG_1 :
        forall n : nat, splitG (S n) [] None
    | splitG_2 :
        forall (n' : nat) (h : A) (t : list A),
          splitG n' t None -> splitG (S n') (h :: t) None
    | splitG_3 :
        forall (n' : nat) (h : A) (t l1 l2 : list A),
          splitG n' t (Some (l1, l2)) ->
            splitG (S n') (h :: t) (Some (h :: l1, l2)).

Lemma splitG_det :
  forall (A : Type) (n : nat) (l : list A) (r1 r2 : option (list A * list A)),
    splitG n l r1 -> splitG n l r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H;
    inversion 1; subst; try reflexivity;
    specialize (IHsplitG _ H5); congruence.
Qed.

Lemma splitG_correct :
  forall (A : Type) (n : nat) (l : list A),
    splitG n l (split n l).
Proof.
  induction n as [| n']; cbn.
    constructor.
    destruct l as [| h t].
      constructor.
      case_eq (split n' t); intros.
        destruct p. constructor. rewrite <- H. apply IHn'.
        constructor. rewrite <- H. apply IHn'.
Qed.

Lemma splitG_complete :
  forall (A : Type) (n : nat) (l : list A) (r : option (list A * list A)),
    splitG n l r -> r = split n l.
Proof.
  intros. apply splitG_det with n l.
    assumption.
    apply splitG_correct.
Qed.

Lemma split_ind :
  forall
    {A : Type} (P : nat -> list A -> option (list A * list A) -> Prop)
    (H_0 : forall l : list A, P 0 l (Some ([], l)))
    (H_S_nil : forall n' : nat, P (S n') [] None)
    (H_S_cons_None :
      forall (n' : nat) (h : A) (t : list A),
        split n' t = None -> P n' t None -> P (S n') (h :: t) None)
    (H_S_cons_Some :
      forall (n' : nat) (h : A) (t l1 l2 : list A),
        split n' t = Some (l1, l2) -> P n' t (Some (l1, l2)) ->
          P (S n') (h :: t) (Some (h :: l1, l2))),
      forall (n : nat) (l : list A), P n l (split n l).
Proof.
  intros.
  apply splitG_ind.
    assumption.
    assumption.
    clear n l. intros. apply H_S_cons_None.
      apply splitG_complete in H. auto.
      assumption.
    intros. apply H_S_cons_Some.
      apply splitG_complete in H. auto.
      assumption.
    apply splitG_correct.
Qed.
(* end hide *)

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Lemma wf_lengthOrder :
  forall A : Type, well_founded (@lengthOrder A).
Proof.
  intros. apply (wf_inverse_image _ _ (@length A)). apply wf_lt.
Defined.

Lemma lengthOrder_split_aux :
  forall {A : Type} (n : nat) (l : list A) (l1 l2 : list A),
    split n l = Some (l1, l2) ->
      n = 0  \/ lengthOrder l2 l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    left. reflexivity.
    right. destruct l as [| h t]; cbn in *.
      inversion H.
      case_eq (split n' t).
        intros [l1' l2'] H'. rewrite H' in H. inversion H; subst.
          destruct (IHn' t l1' l2 H').
            rewrite H0 in *. cbn in *. inversion H'; subst.
              apply le_n.
            apply lt_trans with (length t).
              assumption.
              apply le_n.
        intro. rewrite H0 in H. inversion H.
Restart.
  intro A.
  apply (split_ind (fun n l r => forall l1 l2 : list A,
                                   r = Some (l1, l2) -> n = 0 \/ _));
  intros.
    left. reflexivity.
    inversion H.
    inversion H1.
    inversion H1; subst. right. destruct (H0 _ _ eq_refl).
      subst. inversion H. red. cbn. apply le_n.
      red. cbn. eapply lt_trans.
        exact H2.
        apply le_n.
Qed.
(* end hide *)

Lemma lengthOrder_split :
  forall (n : nat) (A : Type) (l : list A) (l1 l2 : list A),
    split (S n) l = Some (l1, l2) -> lengthOrder l2 l.
(* begin hide *)
Proof.
  intros. destruct (lengthOrder_split_aux _ _ _ _ H).
    inversion H0.
    assumption.
Qed.
(* end hide *)

(** * Metoda induktywnej dziedziny *)

(** Póki co nie jest źle - udało nam się wszakże wymyślić jedyną słuszną
    metodę dowodzenia właściwości funkcji rekurencyjnych. Jednak nasza
    implementacja kuleje przez to nieszczęsne równanie rekurencyjne. Jak
    możemy udowodnić je bez używania indukcji wykresowej?

    Żeby znaleźć odpowiedź na to pytanie, znowu przyda się nam trochę
    konceptualnej jasności. Na czym tak naprawdę polega problem? Jak
    pamiętamy, problem wynika z tego, że definiując [div] przez rekursję
    dobrze ufundowaną musieliśmy jednocześnie dowodzić, że wywołania
    rekurencyjne odbywają się na argumencie mniejszym od argumentu obecnego
    wywołania.

    Tak więc problemem jest połączenie w jednej definicji dwóch dość luźno
    powiązanych rzeczy, którymi są:
    - Docelowa definicja, która określa obliczeniowe zachowanie funkcji.
      Jej manifestacją jest nasze nieszczęsne równanie rekurencyjne. Bywa
      ona czasem nazywana aspektem obliczeniowym (albo algorytmicznym)
      funkcji.
    - Dowód terminacji, który zapewnia, że definicja docelowa jest legalna
      i nie prowadzi do sprzeczności. Jego manifestacją są występujące w
      definicji [div] dowody na to, że wywołanie rekurencyjne ma argument
      mniejszy od obecnego wywołania. Bywa on czasem nazywany aspektem
      logicznym funkcji. *)

(** Pani doktur, mamy diagnozę! Tylko co z nią zrobić? Czy jest jakaś metoda,
    żeby rozdzielić obliczeniowy i logiczny aspekt danej funkcji, a potem
    poskładać je do kupy?

    Pomyślmy najpierw nad aspektem obliczeniowym. Czy da się zdefiniować
    funkcję bezpośrednio za pomocą jej definicji docelowej, czyli równania
    rekurencyjnego? Żeby to zrobić, musielibyśmy mieć możliwość robienia
    rekursji o dokładnie takim kształcie, jaki ma mieć ta funkcja...

    Eureka! Przecież mamy coś, co pozwala nam na rekursję o dokładnie takim
    kształcie, a mianowicie induktywny wykres! Ale przecież wykres wiąże
    ze sobą argumenty i wynik, a my chcemy dopiero zdefiniować coś, co ów
    wynik obliczy... czyli nie eureka?

    Nie do końca. Możemy zmodyfikować definicję wykresu, wyrzucając z
    niej wszystkie wzmianki o wyniku, uzyskując w ten sposób predykat
    będący induktywną charakteryzacją dziedziny naszej funkcji. Dzięki
    niemu możemy zdefiniować zmodyfikowaną wersję funkcji, w której
    dodatkowym argumentem jest dowód na to, że argumenty należą do
    dziedziny.

    Logiczny aspekt funkcji, czyli dowód terminacji, sprowadza się w
    takiej sytuacji do pokazania, że wszystkie argumenty należą do
    dziedziny (czyli spełniają predykat dziedziny). Żeby zdefiniować
    oryginalną funkcję, wystarczy jedynie poskładać oba aspekty do
    kupy, czyli wstawić dowód terminacji do zmodyfikowanej funkcji.

    Żeby nie utonąć w ogólnościach, zobaczmy, jak nasz wspaniały
    wynalazek radzi sobie z dzieleniem. *)

Inductive divD : nat -> nat -> Type :=
    | divD_lt : forall n m : nat, n < S m -> divD n m
    | divD_ge :
        forall n m : nat,
          n >= S m -> divD (n - S m) m -> divD n m.

(** Tak wygląda predykat dziedziny dla dzielenia. Zauważmy, że tak naprawdę
    to nie jest to predykat, bo bierze dwa argumenty i co więcej nie zwraca
    [Prop], lecz [Type]. Nie będziemy się tym jednak przejmować - dla nas
    [divD] będzie "predykatem dziedziny". Zauważmy też, że nie jest to
    predykat dziedziny dla [div], lecz dla [div'], czyli zupełnie nowej
    funkcji, którą zamierzamy zdefiniować.

    Ok, przejdźmy do konkretów. [div'] ma mieć typ [nat -> nat -> nat],
    a zatem [divD] ma dwa indeksy odpowiadające dwóm argumentom [div'].
    Pierwszy konstruktor głosi, że jeżeli [n < S m], to oba te argumenty
    należą do dziedziny (bo będziemy chcieli w tym przypadku zwrócić [0]).
    Drugi konstruktor głosi, że jeżeli [n >= S m], to para argumentów [n]
    i [m] należy do dziedziny pod warunkiem, że para argumentów [n - S m]
    i [m] należy do dziedziny. Jest tak, gdyż w tym przypadku będziemy
    chcieli zrobić wywołanie rekurencyjne właśnie na [n - S m] oraz [m]. *)

Fixpoint div'_aux {n m : nat} (H : divD n m) : nat :=
match H with
    | divD_lt _ _ _ => 0
    | divD_ge _ _ _ H' => S (div'_aux H')
end.

(** Dzięki [divD] możemy zdefiniować funkcję [div'_aux], której typem jest
    [forall n m : nat, divD n m -> nat]. Jest to funkcja pomocnicza, która
    posłuży nam do zdefiniowania właściwej funkcji [div'].

    Ponieważ [divD] jest zdefiniowane induktywnie, docelowa definicja [div']
    jest strukturalnie rekurencyjna po argumencie [H : divD n m], mimo że nie
    jest strukturalnie rekurencyjna po [n] ani [m]. To właśnie jest magia
    stojąca za metodą induktywnej dziedziny - możemy sprawić, żeby każda (no,
    prawie), nawet najdziwniejsza rekursja była strukturalnie rekurencyjna po
    dowodzie należenia do dziedziny.

    Definicja jest banalna. Gdy natrafimy na konstruktor [divD_lt], zwracamy
    [0] (bo wiemy, że jednym z argumentów [divD_lt] jest dowód na to, że
    [n < S m]). Jeżeli trafimy na [divD_ge], to wiemy, że [n >= S m], więc
    robimy wywołanie rekurencyjne na [H' : divD (n - S m) m] i dorzucamy do
    wyniku [S].

    W ten sposób zdefiniowaliśmy obliczeniową część [div'], zupełnie nie
    przejmując się kwestią terminacji. *)

Lemma divD_all :
  forall n m : nat, divD n m.
Proof.
  apply (well_founded_rect nat lt wf_lt (fun _ => forall m : nat, _)).
  intros n IH m.
  destruct (le_lt_dec (S m) n).
    apply divD_ge.
      unfold ge. assumption.
      apply IH. abstract lia.
    apply divD_lt. assumption.
Defined.

(** Dowód terminacji jest bliźniaczo podobny do naszej pierwszej definicji
    [div]. Zaczynamy przez rekursję dobrze ufundowaną z porządkiem [lt] (i
    dowodem [wf_lt] na to, że [lt] jest dobrze ufundowany), wprowadzamy
    zmienne do kontekstu, po czym sprawdzamy, który z przypadków zachodzi.

    Jeżeli [n >= S m], używamy konstruktora [divD_ge]. [n >= S m] zachodzi
    na mocy założenia, zaś [n - S m] i [m] należą do dziedziny na mocy
    hipotezy indukcyjnej. Gdy [n < S m], [n] i [m] należą do dziedziny na
    mocy założenia. *)

Definition div' (n m : nat) : nat :=
  div'_aux (divD_all n m).

(** A oto i ostateczna definicja - wstawiamy dowód [divD_all] do funkcji
    pomocniczej [div'_aux] i uzyskujemy pełnoprawną funkcję dzielącą
    [div' : nat -> nat -> nat]. *)

Compute div' 666 7.
(* ===> = 83 : nat *)

(** Jak widać, wynik oblicza się bez problemu. Po raz kolejny przypominam,
    że [div' n m] oblicza [n/(m + 1)], nie zaś [n/m]. Przypominam też, że
    dowód [divD_all] koniecznie musimy zakończyć za pomocą komendy [Defined],
    a nie jak zazwyczaj [Qed], gdyż w przeciwnym przypadku funkcja [div'] nie
    mogłaby niczego obliczyć. *)

(* begin hide *)
(** TODO: sprawdzić, czy różnica między [Qed] i [Defined] została omówiona. *)
(* end hide *)

Lemma divG_div'_aux :
  forall (n m : nat) (d : divD n m),
    divG n m (div'_aux d).
Proof.
  induction d; cbn; constructor; assumption.
Qed.

Lemma divG_correct' :
  forall n m : nat,
    divG n m (div' n m).
Proof.
  intros. apply divG_div'_aux.
Qed.

(** Żeby udowodnić regułę indukcji wykresowej, będziemy potrzebowali tego
    samego co poprzednio, czyli twierdzeń o poprawności i pełności funkcji
    [div'] względem wykresu [divG]. Dowody są jednak dużo prostsze niż
    ostatnim razem.

    Najpierw dowodzimy, że funkcja pomocnicza [div'_aux] oblicza taki wynik,
    jakiego spodziewa się wykres [divG]. Dowód jest banalny, bo indukcja po
    [d : divD n m] ma dokładnie taki kształt, jakiego nam potrzeba. Właściwy
    dowód dla [div'] uzyskujemy przez wyspecjalizowanie [divG_div'_aux] do
    [div']. *)

Lemma divG_complete' :
  forall n m r : nat,
    divG n m r -> r = div' n m.
Proof.
  intros. apply divG_det with n m.
    assumption.
    apply divG_correct'.
Qed.

Lemma div'_ind :
  forall
    (P : nat -> nat -> nat -> Prop)
    (Hlt : forall n m : nat, n < S m -> P n m 0)
    (Hge :
      forall n m : nat, n >= S m ->
        P (n - S m) m (div' (n - S m) m) ->
          P n m (S (div' (n - S m) m))),
      forall n m : nat, P n m (div' n m).
Proof.
  intros P Hlt Hge n m.
  apply divG_ind.
    assumption.
    intros. apply divG_complete' in H0. subst. apply Hge; assumption.
    apply divG_correct'.
Qed.

(** Dowód pełności i dowód reguły indukcji wykresowej są dokładnie takie
    same jak poprzednio. Zauważ, że tym razem zupełnie zbędne okazało się
    równanie rekurencyjne, bez którego nie mogliśmy obyć się ostatnim
    razem. Jednak jeżeli chcemy, możemy bez problemu je udowodnić, i to
    nawet na dwa sposoby. *)

Lemma div'_eq :
  forall n m : nat,
    div' n m = if n <? S m then 0 else S (div' (n - S m) m).
Proof.
  intros. unfold div'. generalize (divD_all n m) as d.
  induction d; cbn.
    rewrite leb_correct.
      reflexivity.
      apply le_S_n. assumption.
    rewrite leb_correct_conv.
      f_equal. apply divG_det with (n - S m) m; apply divG_div'_aux.
      assumption.
Restart.
  intros. apply div'_ind; clear n m; intros; cbn.
    rewrite leb_correct.
      reflexivity.
      abstract lia.
    rewrite leb_correct_conv.
      reflexivity.
      abstract lia.
Qed.

(** Pierwszy, trudniejszy sposób, to zgeneralizowanie [divD_all n m]
    do dowolnego [d] oraz indukcja po [d] (to tak, jakbyśmy najpierw
    udowodnili tę regułę dla [div'_aux], a potem wyspecjalizowali do
    [div']).

    Drugi, łatwiejszy sposób, realizuje nasz początkowy pomysł, od którego
    wszystko się zaczęło: dowodzimy równania rekurencyjnego za pomocą reguły
    indukcji wykresowej. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [rot], która bierze liczbę [n] oraz listę i zwraca
    listę, w której bloki o długości dokładnie [n + 1] zostały odwrócone,
    np.

    [rot 0 [1; 2; 3; 4; 5; 6; 7] = [1; 2; 3; 4; 5; 6; 7]]

    [rot 1 [1; 2; 3; 4; 5; 6; 7] = [2; 1; 4; 3; 6; 5; 7]]

    [rot 2 [1; 2; 3; 4; 5; 6; 7] = [3; 2; 1; 6; 5; 4; 7]]

    Wskazówka: rzecz jasna użyj metody induktywnej dziedziny. Nie bez
    przyczyny także w jednym z poprzednich zadań kazałem ci zdefiniować
    funkcję [split], która odkraja od listy blok o odpowiedniej długości.

    Następnie zdefiniuj wykres funkcji [rot] i udowodnij jej regułę indukcji
    wykresowej oraz równanie rekurencyjne. Użyj jej, żeby pokazać, że [rot]
    jest inwolucją dla dowolnego [n], tzn. [rot n (rot n l) = l]. Uwaga:
    potrzebne będzie trochę lematów. *)

(* begin hide *)
Module rot.

Inductive rotD {A : Type} (n : nat) : list A -> Type :=
    | rotD_None :
        forall l : list A,
          split (S n) l = None -> rotD n l
    | rotD_Some :
        forall l l1 l2 : list A,
          split (S n) l = Some (l1, l2) ->
            rotD n l2 -> rotD n l.

Fixpoint rot_aux {A : Type} {n : nat} {l : list A} (d : rotD n l) : list A :=
match d with
    | rotD_None _ _ _ => l
    | rotD_Some _ _ l1 _ _ d' => rev l1 ++ rot_aux d'
end.

Lemma rotD_all :
  forall {A : Type} (n : nat) (l : list A), rotD n l.
Proof.
  intros A n.
  apply (@well_founded_rect _ _ (wf_lengthOrder A) (fun l => _)).
  intros l IH.
  case_eq (split (S n) l).
    intros [l1 l2] H. econstructor 2.
      eassumption.
      apply IH. eapply lengthOrder_split. eassumption.
    intro. constructor. assumption.
Defined.

Definition rot {A : Type} (n : nat) (l : list A) : list A :=
  rot_aux (rotD_all n l).

Compute rot 1 [1; 2; 3; 4; 5; 6; 7].

Inductive rotG {A : Type} (n : nat) : list A -> list A -> Prop :=
    | rotG_None :
        forall l : list A,
          split (S n) l = None -> rotG n l l
    | rotG_Some :
        forall l l1 l2 r : list A,
          split (S n) l = Some (l1, l2) ->
            rotG n l2 r -> rotG n l (rev l1 ++ r).

Lemma rotG_det :
  forall {A : Type} (n : nat) (l r1 r2 : list A),
    rotG n l r1 -> rotG n l r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; inversion 1; subst; try congruence.
    rewrite H in H2. inversion H2; subst. f_equal.
      apply IHrotG. assumption.
Qed.

Lemma rotG_correct :
  forall {A : Type} (n : nat) (l : list A),
    rotG n l (rot n l).
Proof.
  intros. unfold rot. generalize (rotD_all n l) as d.
  induction d; cbn.
    constructor. assumption.
    econstructor; eauto.
Qed.

Lemma rotG_complete :
  forall (A : Type) (n : nat) (l r : list A),
    rotG n l r -> r = rot n l.
Proof.
  intros. apply rotG_det with n l.
    assumption.
    apply rotG_correct.
Qed.

Lemma rot_ind :
  forall
    (A : Type) (n : nat) (P : list A -> list A -> Prop)
    (H_None :
      forall l : list A,
        split (S n) l = None -> P l l)
    (H_Some :
      forall l l1 l2 : list A,
        split (S n) l = Some (l1, l2) ->
          P l2 (rot n l2) -> P l (rev l1 ++ rot n l2)),
    forall l : list A, P l (rot n l).
Proof.
  intros.
  apply rotG_ind with n.
    assumption.
    intros. apply rotG_complete in H0. subst. apply H_Some; assumption.
    apply rotG_correct.
Qed.

Lemma rot_eq :
  forall {A : Type} (n : nat) (l : list A),
    rot n l =
    match split (S n) l with
        | None => l
        | Some (l1, l2) => rev l1 ++ rot n l2
    end.
Proof.
  intros A n.
  apply (rot_ind A n (fun l r => r = _)); intros.
    rewrite H. reflexivity.
    rewrite H. reflexivity.
Qed.

Lemma split_spec :
  forall {A : Type} (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) -> length l1 = n /\ l = l1 ++ l2.
Proof.
  intros A.
  apply (split_ind (fun n l r =>
    forall l1 l2, r = Some (l1, l2) -> length l1 = n /\ _));
  intros.
    inversion H; subst. auto.
    inversion H.
    inversion H1.
    inversion H1. specialize (H0 _ _ eq_refl). cbn. subst.
      firstorder congruence.
Qed.

Lemma split_app_length :
  forall {A : Type} (n : nat) (l1 l2 : list A),
    length l1 = n -> split n (l1 ++ l2) = Some (l1, l2).
Proof.
  intro A.
  apply (split_ind (fun n l1 r =>
    forall l2, length l1 = n -> split n (l1 ++ l2) = Some (l1, l2)));
  intros.
    destruct l; inversion H. reflexivity.
    inversion H.
    cbn. rewrite H0.
      reflexivity.
      inversion H1. reflexivity.
    cbn. rewrite H0.
      reflexivity.
      inversion H1. reflexivity.
Qed.

Lemma rot_rot :
  forall {A : Type} (n : nat) (l : list A),
    rot n (rot n l) = l.
Proof.
  intros A n.
  apply (rot_ind A n (fun l r => rot n r = l)); intros.
    rewrite rot_eq, H. reflexivity.
    apply split_spec in H. destruct H. subst.
      rewrite rot_eq, split_app_length.
        rewrite rev_involutive, H0. reflexivity.
        rewrite rev_length. assumption.
Qed.

End rot.
(* end hide *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [Eratosthenes : nat -> list nat], która dla
    danego [n] znajduje listę wszystkich liczb pierwszych, które są
    mniejsze lub równe [n].

    Jako funkcję pomocniczą zaimplementuj sito Eratosthenesa. Sito
    to funkcja [sieve : list nat -> list nat], która działa tak:
    - jeżeli wejście jest puste, zwróć listę pustą
    - jeżeli wejście ma głowę [h] i ogon [t], to wstaw [h] na początek
      wyniku i wywołaj się rekurencyjnie na ogonie [t] z odfiltrowanymi
      wszystkimi wielokrotnościami głowy [h]

    Jeżeli jako argument [sieve] podamy listę wszystkich liczb poczynając
    od pewnej liczby pierwszej [p] aż do [n], to otrzymamy listę liczb
    pierwszych między [p] i [n].

    Żeby sprawnie rozwiązać to zadanie, zgeneralizuj funkcję [sieve]
    na dowolny typ [A] i funkcję porównującą [cmp : A -> A -> bool]
    (tak będzie łatwiej) i użyj metody induktywnej dziedziny. *)

(* begin hide *)
Module sieve.

Inductive D {A : Type} (f : A -> A -> bool) : list A -> Type :=
    | D0 : D f []
    | D1 :
        forall (h : A) (t : list A),
          D f (filter (f h) t) -> D f (h :: t).

Arguments D0 {A f}.
Arguments D1 {A f} _ _ _.

Lemma D_all :
  forall (A : Type) (f : A -> A -> bool) (l : list A), D f l.
Proof.
  intros A f.
  apply (well_founded_rect _ _ (wf_lengthOrder A)).
  destruct x as [| h t]; intros IH.
    constructor.
    constructor. apply IH. clear IH. induction t as [| h' t']; cbn.
      constructor.
      destruct (f h h'); cbn in *.
        apply le_n_S. apply IHt'.
        apply le_S. apply IHt'.
Defined.

Fixpoint sieve'
  {A : Type} (f : A -> A -> bool)
  {l : list A} (d : D f l) : list A :=
match d with
    | D0 => []
    | D1 h t d' => h :: sieve' f d'
end.

Definition sieve
  {A : Type} (f : A -> A -> bool) (l : list A) : list A :=
    sieve' f (D_all A f l).

(**
TODO: zrobić porządek z [list] i [Datatypes.list], najlepiej po
TODO: prostu usunąć definicję [list] z rozdziału D5.
*)

Fixpoint any {A : Type} (f : A -> bool) (l : list A) : bool :=
match l with
    | [] => false
    | h :: t => f h || any f t
end.

Fixpoint iterate {A : Type} (f : A -> A) (x : A) (n : nat) : list A :=
match n with
    | 0 => []
    | S n' => x :: iterate f (f x) n'
end.

Definition divides (n m : nat) : bool :=
  any (fun k : nat => n * k =? m) (iterate S 0 (S m)).

Definition Eratosthenes (n : nat) : list nat :=
  sieve (fun n m => negb (divides n m)) (iterate S 2 n).

Compute Eratosthenes 100.

End sieve.
(* end hide *)

(** * Komenda [Function] *)

(** Odkryliśmy uniwersalną metodę definiowania funkcji i dowodzenia ich
    właściwości. Czego chcieć więcej?

    Po pierwsze, metoda definiowania nie jest uniwersalna (jeszcze), o czym
    przekonamy się w kolejnych podrozdziałach. Po drugie, mimo że metoda
    dowodzenia faktycznie jest uniwersalna, to komu normalnemu chciałoby
    się przy każdej funkcji tyle pisać? Jakieś wykresy, dziedziny, lematy,
    reguły indukcji, co to ma być?

    Czy w celu sprawnego definiowania i dowodzenia właściwości funkcji trzeba
    zoutsourcować cały proces i zatrudnić milion Hindusów? Na szczęście nie,
    gdyż bóg dał nam komendę [Function]. *)

Require Import Recdef.

(** Komenda ta żyje w module [Recdef], którego nazwa jest skrótem od słów
    "recydywista defraudator"... dobra, koniec żartów. *)

Function div'' (n m : nat) {measure id n} : nat :=
  if n <? S m then 0 else S (div'' (n - S m) m).
Proof.
  intros. unfold id. cbn in teq. apply leb_complete_conv in teq. lia.
Defined.
(* ===> div''_tcc is defined
        div''_terminate is defined
        div''_ind is defined
        div''_rec is defined
        div''_rect is defined
        R_div''_correct is defined
        R_div''_complete is defined *)

(** Definicja zaczyna się od słowa kluczowego [Function], następnie mamy
    nazwę funkcji i argumenty, tak jak w zwykłych definicjach za pomocą
    [Definition] czy [Fixpoint], a później tajemniczą klauzulę
    [{measure id n}], do której zaraz wrócimy, i zwracany typ. Ciało
    definicji wygląda dokładnie jak docelowa definicja.

    Jednak po kropce definicja nie kończy się - zamiast tego Coq każe nam
    udowodnić, że wywołanie rekurencyjne [div''] odbywa się na argumencie
    mniejszym niż [n]. Po zakończeniu dowodu funkcja zostaje zaakceptowana
    przez Coqa.

    To jednak nie koniec. Komenda [Function] nie tylko pozwala bezboleśnie
    zdefiniować [div''], ale też generuje dla nas całą masę różnych rzeczy:
    - [div''_tcc] to lemat, który mówi, że wszystkie wywołania rekurencyjne
      są na argumencie mniejszym od obecnego
    - [div''_terminate] to dowód tego, że funkcja terminuje (czyli że się
      nie zapętla). Jeżeli przyjrzysz się jego typowi, to zobaczysz, że
      jest podobny zupełnie do niczego. Wynika to z faktu, że komenda
      [Function] tak naprawdę nie używa metody induktywnej dziedziny, ale
      pewnej innej metody definiowania funkcji ogólnie rekurencyjnych.
      Nie powinno nas to jednak martwić - ważne, że działa.
    - [div''_ind] to reguła indukcji wykresowej dla [div'']. Jest też jej
      wariant [div''_rect], czyli "rekursja wykresowa", służąca raczej do
      definiowania niż dowodzenia.
    - [R_div''] to induktywnie zdefiniowany wykres funkcji [div'']. Zauważ
      jednak, że nie jest on relacją, a rodziną typów - nie wiem po co i
      nie ma co wnikać w takie detale.
    - [R_div''_correct] to twierdzenie o poprawności wykresu.
    - [R_div''_complete] to twierdzenie o pełności wykresu.
    - [div''_equation] to równanie rekurencyjne *)

(** Jak więc widać, nastąpił cud automatyzacji i wszystko robi się samo.
    To jednak nie koniec udogodnień. Zobaczmy, jak możemy udowodnić jakiś
    fakt o [div'']. *)

Lemma div''_le :
  forall n m : nat, div'' n m <= n.
Proof.
  intros. functional induction (div'' n m).
    apply le_0_n.
    apply leb_complete_conv in e. lia.
Defined.

(** Dowodzenie właściwości funkcji zdefiniowanych za pomocą [Function]
    jest bajecznie proste. Jeżeli wszystkie argumenty funkcji znajdują
    się w kontekście, to możemy użyć taktyki [functional induction
    (nazwa_funkcji argument_1 ... argument_n)], która odpala indukcję
    wykresową dla tej funkcji. Z powodu nazwy tej taktyki indukcja
    wykresowa bywa też nazywana indukcją funkcyjną.

    Wujek Dobra Rada: nigdy nie odwijaj definicji funkcji zdefiniowanych
    za pomocą [Function] ani nie próbuj ręcznie aplikować reguły indukcji
    wykresowej, bo skończy się to jedynie bólem i zgrzytaniem zębów.

    Na koniec wypadałoby jedynie dodać, że wcale nie złapaliśmy pana boga
    za nogi i komenda [Function] nie rozwiązuje wszystkich problemów
    pierwszego świata. W szczególności niektóre funkcje mogą być tak
    upierdliwe, że komenda [Function] odmówi współpracy z nimi. Radzeniu
    sobie z takimi ciężkimi przypadkami poświęcimy kolejne podrozdziały. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [rot] (i wszystkie funkcje pomocnicze) jeszcze raz,
    tym razem za pomocą komendy [Function]. Porównaj swoje definicje wykresu
    oraz reguły indukcji z tymi automatycznie wygenerowanymi. Użyj taktyki
    [functional induction], żeby jeszcze raz udowodnić, że [rot] jest
    inwolucją. Policz, ile pisania udało ci się dzięki temu zaoszczędzić.

    Czy w twoim rozwiązaniu są lematy, w których użycie indukcji funkcyjnej
    znacznie utrudnia przeprowadzenie dowodu? W moim poprzednim rozwiązaniu
    był jeden taki, ale wynikał z głupoty i już go nie ma. *)

(* begin hide *)
Module rotn_Function.

Require Import Recdef.

Require Import List.
Import ListNotations.

Function split
  {A : Type} (n : nat) (l : list A)
  : option (list A * list A) :=
match n, l with
    | 0, _ => Some ([], l)
    | S n', [] => None
    | S n', h :: t =>
        match split n' t with
            | None => None
            | Some (l1, l2) => Some (h :: l1, l2)
        end
end.

Lemma split_spec :
  forall {A : Type} (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) -> length l1 = n /\ l = l1 ++ l2.
Proof.
  intros A n l.
  functional induction (split n l); inversion 1; subst; cbn.
    split; reflexivity.
    destruct (IHo _ _ e1). subst. split; reflexivity.
Qed.

Lemma split_app_length :
  forall {A : Type} (n : nat) (l1 l2 : list A),
    length l1 = n -> split n (l1 ++ l2) = Some (l1, l2).
Proof.
  intros A n l.
  functional induction (split n l); inversion 1; subst; cbn.
    rewrite H. cbn. destruct l; inversion H. reflexivity.
    rewrite IHo; reflexivity.
    rewrite IHo; reflexivity.
Qed.

Lemma split_length_aux :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) ->
      n = 0 \/ length l2 < length l.
Proof.
  intros A n l.
  functional induction (split n l); inversion 1; subst.
    left. reflexivity.
    right. destruct (IHo _ _ e1).
      subst. cbn in e1. inversion e1; subst. cbn. apply le_n.
      cbn. lia.
Qed.

Lemma split_length :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split (S n) l = Some (l1, l2) -> length l2 < length l.
Proof.
  intros. destruct (split_length_aux A (S n) l l1 l2 H).
    inversion H0.
    assumption.
Qed.

Function rot
  {A : Type} (n : nat) (l : list A) {measure length l} : list A :=
match split (S n) l with
    | None => l
    | Some (l1, l2) => rev l1 ++ rot n l2
end.
Proof.
  intros A n l _ l1 l2 _ H.
  eapply lengthOrder_split. eassumption.
Defined.

Arguments rot {x} _ _.

Compute rot 1 [1; 2; 3; 4; 5; 6; 7].

Lemma rot_rot :
  forall (A : Type) (n : nat) (l : list A),
    rot n (rot n l) = l.
Proof.
  intros. functional induction (rot n l).
    rewrite rot_equation, e. reflexivity.
    apply split_spec in e. destruct e. subst.
      rewrite rot_equation, split_app_length.
        rewrite rev_involutive, IHl0. reflexivity.
        rewrite rev_length. assumption.
Qed.

End rotn_Function.
(* end hide *)

(** * Rekursja zagnieżdżona *)

(** Jakież to diabelstwo może być tak diabelskie, by przeciwstawić się
    metodzie induktywnej dziedziny oraz komendzie [Function]? Ano ano,
    rekursja zagnieżdżona - wywołanie rekurencyjne jest zagnieżdżone,
    jeżeli jego argumentem jest wynik innego wywołania rekurencyjnego. *)

Module McCarthy.

Fail Fixpoint f (n : nat) : nat :=
  if 100 <? n then n - 10 else f (f (n + 11)).

Fail Function f (n : nat) {measure id n} : nat :=
  if 100 <? n then n - 10 else f (f (n + 11)).

(** Ta funkcja jest podobna zupełnie do niczego, co dotychczas widzieliśmy.
    Działa ona następująco:
    - jeżeli [n] jest większe od [100], to zwróć [n - 10]
    - w przeciwnym wypadku wywołaj rekurencyjnie [f] na [n + 11], a następnie
      wywołaj [f] na wyniku tamtego wywołania. *)

(** Taka rekursja jest oczywiście nielegalna: [n + 11] nie jest strukturalnym
    podtermem [n], gdyż jest od niego większe, zaś [f (n + 11)] w ogóle nie
    wiadomo a priori, jak się ma do [n]. Nie dziwota więc, że Coq odrzuca
    powyższą definicję.

    Być może wobec tego taka "funkcja" w ogóle nie jest funkcją, a definicja
    jest wadliwa? Otóż nie tym razem. Okazuje się bowiem, że istnieje funkcja
    zachowująca się zgodnie z zawartym w definicji równaniem. Żebyśmy mogli
    w to uwierzyć, zastanówmy się, ile wynosi [f 100].

    [f 100 = f (f 111) = f 101 = 101 - 10 = 91] - poszło gładko. A co z [99]?
    Mamy [f 99 = f (f 110) = f 100 = 91] - znowu 91, czyżby spiseg? Dalej:
    [f 98 = f (f 109) = f 99 = 91] - tak, to na pewno spiseg. Teraz możemy
    zwerbalizować nasze domysły: jeżeli [n <= 100], to [f n = 91]. Jak
    widać, nieprzypadkowo funkcja ta bywa też nazywana "funkcją 91
    McCarthy'ego".

    Czy da się tę funkcję zaimplementować w Coqu? Jeszcze jak! *)

Definition f_troll (n : nat) : nat :=
  if n <=? 100 then 91 else n - 10.

(** Ehhh... nie tego się spodziewałeś, prawda? [f_troll] jest wprawdzie
    implementacją opisanej powyżej nieformalnie funkcji [f], ale definicja
    opiera się na tym, że z góry wiemy, jaki jest wynik [f] dla dowolnego
    argumentu. Nie trzeba chyba tłumaczyć, że dla żadnej ciekawej funkcji
    nie będziemy posiadać takiej wiedzy (a sama funkcja McCarthy'ego nie
    jest ciekawa, bo jest sztuczna, ot co!).

    Czy więc da się zaimplementować [f] bezpośrednio, tzn. w sposób dokładnie
    oddający definicję nieformalną? Otóż tak, da się i to w sumie niewielkim
    kosztem: wystarczy jedynie nieco zmodyfikować naszą metodę induktywnej
    dziedziny. Zanim jednak to zrobimy, zobaczmy, dlaczego nie obejdzie się
    bez modyfikacji. *)

Fail Inductive fD : nat -> Type :=
  | fD_gt100 : forall n : nat, 100 < n -> fD n
  | fD_le100 :
      forall n : nat, n <= 100 ->
        fD (n + 11) -> fD (f (n + 11)) -> fD n.

(* ===> The command has indeed failed with message:
        The reference f was not found in the current environment. *)

(** A oto i źródło całego problemu. Jeżeli [n <= 100], to chcemy zrobić dwa
    wywołania rekurencyjne: jedno na [n + 11], a drugie na [f (n + 11)].
    Wobec tego należenie tych dwóch argumentów do dziedziny jest warunkiem
    należenia [n] do dziedziny i stąd postać całego konstruktora.

    Niestety, definicja jest zła - [f (n + 11)] nie jest poprawnym termem,
    gdyż [f] nie jest jeszcze zdefiniowane. Mamy więc błędne koło: żeby
    zdefiniować [f], musimy zdefiniować predykat dziedziny [fD], ale żeby
    zdefiniować [fD], musimy zdefiniować [f].

    Jak wyrwać się z tego błędnego koła? Ratunek przychodzi ze strony być
    może nieoczekiwanej, ale za to już bardzo dobrze przez nas poznanej, a
    jest nim induktywna definicja wykresu. Tak tak - w definicji [fD] możemy
    (a nawet musimy) zastąpić wystąpienia [f] przez wystąpienia wykresu [f].

    Hej ho, po przykład by się szło. *)

Inductive fG : nat -> nat -> Prop :=
    | fG_gt100 :
        forall n : nat, 100 < n -> fG n (n - 10)
    | fG_le100 :
        forall n r1 r2 : nat,
          n <= 100 -> fG (n + 11) r1 -> fG r1 r2 -> fG n r2.

(** Tak wygląda wykres funkcji [f]. Wywołanie rekurencyjne [f (f (n + 11)]
    możemy zareprezentować jako dwa argumenty, mianowicie [fG (n + 11) r1]
    i [fG r1 r2]. Dosłownie odpowiada to wywołaniu rekurencyjnemu w stylu
    [let r1 := f (n + 11) in let r2 := f r1 in r2]. *)

Lemma fG_det :
  forall n r1 r2 : nat,
    fG n r1 -> fG n r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; intros r Hr.
    inversion Hr; subst.
      reflexivity.
      abstract lia.
    inversion Hr; subst.
      abstract lia.
      assert (r1 = r0) by apply (IHfG1 _ H3); subst.
        apply (IHfG2 _ H4).
Defined.

(** Po zdefiniowaniu wykresu dowodzimy, podobnie łatwo jak poprzednio, że
    jest on relacją deterministyczną.*)

Inductive fD : nat -> Type :=
    | fD_gt100 :
        forall n : nat, 100 < n -> fD n
    | fD_le100 :
        forall n r : nat, n <= 100 ->
          fG (n + 11) r -> fD (n + 11) -> fD r -> fD n.

(** A tak wygląda definicja predykatu dziedziny. Zamiast [fD (f (n + 11))]
    mamy [fD r], gdyż [r] na mocy argumentu [fG (n + 11) r] reprezentuje
    wynik wywołania rekurencyjnego [f (n + 11)]. *)

Fixpoint f' {n : nat} (d : fD n) : nat :=
match d with
    | fD_gt100 _ _ => n - 10
    | fD_le100 _ _ _ _ _ d2 => f' d2
end.

(** Definicja funkcji pomocniczej [f'] może być nieco zaskakująca: gdzie
    podziało się zagnieżdżone wywołanie rekurencyjne? Nie możemy jednak
    dać się zmylić przeciwnikowi. Ostatnią klauzulę dopasowania do wzorca
    możemy zapisać jako [| fD_le100 n r H g d1 d2 => f' d2]. Widzimy, że
    [d2] jest typu [fD r], ale [g : fG (n + 11) r], więc możemy myśleć,
    że [r] to tak naprawdę [f (n + 11)], a zatem [d2] tak naprawdę jest
    typu [fD (f (n + 11))]. Jeżeli dodatkowo napiszemy wprost domyślny
    argument [f'], to wywołanie rekurencyjne miałoby postać
    [@f' (@f' (n + 11) d1) d2], a więc wszystko się zgadza. Żeby jednak
    nie rzucać słów na wiatr, udowodnijmy to. *)

Lemma f'_correct :
  forall (n : nat) (d : fD n), fG n (f' d).
Proof.
  induction d; cbn.
    constructor. assumption.
    econstructor 2.
      assumption.
      exact IHd1.
      assert (r = f' d1).
        apply fG_det with (n + 11); assumption.
        subst. assumption.
Defined.

(** Dowód twierdzenia o poprawności jest tylko odrobinkę trudniejszy niż
    ostatnio, gdyż w przypadku wystąpienia w kontekście dwóch hipotez o
    typie [fG (n + 11) _] musimy użyć twierdzenia o determinizmie wykresu. *)

Lemma f'_complete :
  forall (n r : nat) (d : fD n),
    fG n r -> f' d = r.
Proof.
  intros. apply fG_det with n.
    apply f'_correct.
    assumption.
Defined.

(** Dowód twierdzenia o pełności pozostaje bez zmian. *)

Lemma fG_le100_spec :
  forall n r : nat,
    fG n r -> n <= 100 -> r = 91.
Proof.
  induction 1; intro.
    abstract lia.
    inversion H0; subst.
      inversion H1; subst.
        assert (n = 100) by abstract lia. subst. reflexivity.
        abstract lia.
      abstract lia.
Defined.

Lemma f'_le100 :
  forall (n : nat) (d : fD n),
    n <= 100 -> f' d = 91.
Proof.
  intros. apply fG_le100_spec with n.
    apply f'_correct.
    assumption.
Defined.

Lemma f'_ge100 :
  forall (n : nat) (d : fD n),
    100 < n -> f' d = n - 10.
Proof.
  destruct d; cbn; abstract lia.
Defined.

(** Teraz następuje mały twist. Udowodnienie, że każdy argument spełnia
    [fD] będzie piekielnie trudne i będziemy w związku z tym potrzebować
    charakteryzacji funkcji [f']. Zaczynamy więc od udowodnienia, że dla
    [n <= 100] wynikiem jest [91]. Najpierw robimy to na wykresie, bo tak
    jest łatwiej, a potem transferujemy wynik na funkcję. Charakteryzację
    dla [100 < n] dostajemy wprost z definicji. *)

Lemma fD_all :
  forall n : nat, fD n.
Proof.
  apply (well_founded_ind _ (fun n m => 101 - n < 101 - m)).
    apply wf_inverse_image. apply wf_lt.
    intros n IH. destruct (le_lt_dec n 100).
      assert (d : fD (n + 11)) by (apply IH; lia).
        apply fD_le100 with (f' d).
          assumption.
          apply f'_correct.
          assumption.
          apply IH. inversion d; subst.
            rewrite f'_ge100.
              abstract lia.
              assumption.
            rewrite f'_le100; abstract lia.
      constructor. assumption.
Defined.

(** Dowód jest przez indukcję dobrze ufundowaną po [n], a relacja dobrze
    ufundowana, której używamy, to [fun n m : nat => 101 - n < 101 - m].
    Dlaczego akurat taka? Przypomnijmy sobie, jak dokładnie oblicza się
    funkcja [f], np. dla [95]:

    [f 95 = f (f 106) = f 96 = f (f 107) = f 97 = f (f 108) = f 98 =
    f (f 109) = f 99 = f (f 110) = f 100 = f (f 111) = f 101 = 91].

    Jak więc widać, im dalej w las, tym bardziej zbliżamy się do magicznej
    liczby [101]. Wyrażenie [101 - n] mówi nam, jak blisko przekroczenia
    [101] jesteśmy, a więc [101 - n < 101 - m] oznacza, że każde wywołanie
    rekurencyjne musi być bliżej [101] niż poprzednie wywołanie. Oczywiście
    zamiast [101] może być dowolna większa liczba - jeżeli zbliżamy się do
    [101], to zbliżamy się także do [1234567890].

    Dowód dobrego ufundowania jest banalny, ale tylko pod warunkiem, że
    zrobiłeś wcześniej odpowiednie ćwiczenie. Jeszcze jedna uwaga: jak
    wymyślić relację dobrze ufundowaną, jeżeli jest nam potrzebna przy
    dowodzie takim jak ten? Mógłbym ci tutaj naopowiadać frazesów o...
    w sumie nie wiem o czym, ale prawda jest taka, że nie wiem, jak się
    je wymyśla. Tej powyższej wcale nie wymyśliłem sam - znalazłem ją w
    świerszczyku dla bystrzaków.

    Dobra, teraz właściwa część dowodu. Zaczynamy od analizy przypadków.
    Drugi przypadek, gdy [100 < n], jest bardzo łatwy. W pierwszym zaś
    przypadku z hipotezy indukcyjnej dostajemy [fD (n + 11)], tzn.
    [n + 11] należy do dziedziny. Skoro tak, to używamy konstruktora
    [fD_le100], a jako [r] (czyli wynik wywołania rekurencyjnego) dajemy
    mu [f' d].

    Dwa podcele zachodzą na mocy założenia, a jedna wynika z twierdzenia
    o poprawności. Pozostaje nam zatem pokazać, że [f' d] także należy do
    dziedziny. W tym celu po raz kolejny używamy hipotezy indukcyjnej. Na
    zakończenie robimy analizę przypadków po [d], używamy charakteryzacji
    [f'] do uproszczenia celu i kończymy rozumowaniami arytmetycznymi. *)

Definition f (n : nat) : nat := f' (fD_all n).

(* Compute f 110. *)

(** Teraz możemy zdefiniować oryginalne [f]. Niestety, funkcja [f] się nie
    oblicza i nie wiem nawet dlaczego. *)

(* begin hide *)
(* TODO: naprawić obliczanie f91, być może winne jest [lia] *)
(* end hide *)

Lemma f_correct :
  forall n : nat, fG n (f n).
Proof.
  intros. apply f'_correct.
Qed.

Lemma f_complete :
  forall n r : nat,
    fG n r -> f n = r.
Proof.
  intros. apply f'_complete. assumption.
Qed.

Lemma f_91 :
  forall (n : nat),
    n <= 100 -> f n = 91.
Proof.
  intros. apply f'_le100. assumption.
Qed.

(** Twierdzenia o poprawności i pełności oraz charakteryzacja dla [f]
    wynikają za darmo z odpowiednich twierdzeń dla [f']. *)

Lemma f_ind :
  forall
    (P : nat -> nat -> Prop)
    (H_gt100 : forall n : nat, 100 < n -> P n (n - 10))
    (H_le100 :
      forall n : nat, n <= 100 ->
        P (n + 11) (f (n + 11)) -> P (f (n + 11)) (f (f (n + 11))) ->
          P n (f (f (n + 11)))),
    forall n : nat, P n (f n).
Proof.
  intros. apply fG_ind.
    assumption.
    intros. apply f_complete in H0. apply f_complete in H2.
      subst. apply H_le100; assumption.
    apply f_correct.
Defined.

(** Reguły indukcji wykresowej dowodzimy tak samo jak poprzednio, czyli za
    pomocą twierdzeń o pełności i poprawności. *)

Lemma f_eq :
  forall n : nat,
    f n = if 100 <? n then n - 10 else f (f (n + 11)).
Proof.
  intros. apply fG_det with n.
    apply f_correct.
    unfold ltb. destruct (Nat.leb_spec0 101 n).
      constructor. assumption.
      econstructor.
        lia.
        apply f_correct.
        apply f_correct.
Qed.

(** Na koniec również mały twist, gdyż równanie rekurencyjne najprościej jest
    udowodnić za pomocą właściwości wykresu funkcji [f] - jeśli nie wierzysz,
    to sprawdź (ale będzie to bardzo bolesne sprawdzenie).

    Podsumowując: zarówno oryginalna metoda induktywnej dziedziny jak i
    komenda [Function] nie radzą sobie z zagnieżdżonymi wywołaniami
    rekurencyjmi, czyli takimi, w których argumentem jest wynik innego
    wywołania rekurencyjnego. Możemy jednak poradzić sobie z tym problemem
    za pomocą ulepszonej metody induktywnej dziedziny, w której funkcję w
    definicji predykatu dziedziny reprezentujemy za pomocą jej induktywnie
    zdefiniowanego wykresu. *)

(** **** Ćwiczenie *)

(** Przyjrzyjmy się poniższej fikuśnej definicji funkcji: *)

Fail Fixpoint g (n : nat) : nat :=
match n with
    | 0 => 0
    | S n => g (g n)
end.

(** Wytłumacz, dlaczego Coq nie akceptuje tej definicji. Następnie wymyśl
    twierdzenie charakteryzujące tę funkcję, a na koniec zdefiniuj ją za
    pomocą metody zaprezentowanej w tym podrozdziale. *)

(* begin hide *)

(** Coq odrzuca definicję, bo [g n] nie jest strukturalnym podtermem [S n].

    Charakteryzacja jest prosta: [forall n : nat, g n = 0]. *)

Inductive gG : nat -> nat -> Prop :=
    | gG_0 : gG 0 0
    | gG_1 : forall n r1 r2 : nat, gG n r1 -> gG r1 r2 -> gG (S n) r2.

Lemma gG_det :
  forall n r1 r2 : nat, gG n r1 -> gG n r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; inversion 1; subst.
    reflexivity.
    specialize (IHgG1 _ H3). subst. apply IHgG2. assumption.
Defined.

Inductive gD : nat -> Type :=
    | gD_0 : gD 0
    | gD_1 : forall {n r : nat}, gD n -> gG n r -> gD r -> gD (S n).

Fixpoint g' {n : nat} (d : gD n) : nat :=
match d with
    | gD_0 => 0
    | gD_1 d1 _ d2 => g' d2
end.

Lemma gG_correct' :
  forall (n : nat) (d : gD n),
    gG n (g' d).
Proof.
  induction d; cbn.
    constructor.
    assert (g' d1 = r).
      apply gG_det with n; assumption.
      subst. econstructor; eassumption.
Defined.

Lemma gG_complete' :
  forall (n r : nat) (d : gD n),
    gG n r -> r = g' d.
Proof.
  intros. apply gG_det with n.
    assumption.
    apply gG_correct'.
Defined.

Lemma g'_eq :
  forall (n : nat) (d : gD n), g' d = 0.
Proof.
  induction d; cbn.
    reflexivity.
    assumption.
Defined.

Lemma gD_all :
  forall n : nat, gD n.
Proof.
  induction n as [| n'].
    constructor.
    eapply (gD_1 IHn').
      apply (gG_correct' _ IHn').
      rewrite g'_eq. constructor.
Defined.

Definition g (n : nat) : nat := g' (gD_all n).

Time Compute g 50.

Lemma gG_correct :
  forall n : nat, gG n (g n).
Proof.
  intro. apply gG_correct'.
Qed.

Lemma gG_complete :
  forall n r : nat,
    gG n r -> r = g n.
Proof.
  intros. apply gG_complete'. assumption.
Qed.

Lemma g_ind :
  forall
    (P : nat -> nat -> Prop)
    (P_0 : P 0 0)
    (P_1 :
      forall n : nat, P n (g n) -> P (g n) (g (g n)) -> P (S n) (g (g n))),
    forall n : nat, P n (g n).
Proof.
  intros. apply gG_ind.
    assumption.
    intros. apply gG_complete in H. apply gG_complete in H1. subst.
      apply P_1; assumption.
    apply gG_correct.
Qed.

(* end hide *)

End McCarthy.

(** * Metoda induktywno-rekurencyjnej dziedziny *)

(** Zapoznawszy się z metodą induktywnej dziedziny i jej ulepszoną wersją,
    która potrafi poskromić nawet rekursję zagnieżdżoną, dobrze byłoby na
    koniec podumać sobie trochę, co by było gdyby... Coq raczył wspierać
    indukcję-rekursję?

    Ano, trochę ułatwiłoby to nasze nędzne życie, gdyż metoda induktywnej
    dziedziny przepoczwarzyłaby się w metodę induktywno-rekurencyjnej
    dziedziny: dzięki indukcji-rekursji moglibyśmy jednocześnie zdefiniować
    funkcję (nawet taką, w której jest rekursja zagnieżdżona) jednocześnie
    z jej predykatem dziedziny, co oszczędziłoby nam nieco pisania.

    Zobaczmy, jak to wygląda na przykładzie funkcji McCarthy'ego. Ponieważ
    Coq jednak nie wspiera indukcji-rekursji, będziemy musieli użyć kodowania
    aksjomatycznego, co zapewne nieco umniejszy atrakcyjności tej metody. *)

Module McCarthy'.

(*
Inductive fD : nat -> Type :=
    | fD_gt100 : forall n : nat, 100 < n -> fD n
    | fD_le100 :
        forall n : nat, n <= 100 ->
          forall d : fD (n + 11), fD (f' (n + 11) d) -> fD n

with Fixpoint f' (n : nat) (d : fD n) : nat :=
match d with
    | fD_gt100 n H => n - 10
    | fD_le100 n H d1 d2 => f' (f' (n + 11) d1) d2
end.
*)

(** Tak wyglądałoby induktywno-rekurencyjna definicja zmodyfikowanej funkcji
    [f'] wraz z jej dziedziną. Ponieważ w definicji [fD] możemy napisać po
    prostu [fD (f (n + 11) d)], wykres nie jest nam do niczego potrzebny.
    Definicja funkcji wygląda dokładnie tak samo jak ostatnio. *)

Variables
  (fD : nat -> Type)
  (f' : forall n : nat, fD n -> nat)
  (fD_gt100 : forall n : nat, 100 < n -> fD n)
  (fD_le100 :
    forall n : nat, n <= 100 ->
      forall d : fD (n + 11), fD (f' (n + 11) d) -> fD n)
  (f'_eq1 :
    forall (n : nat) (H : 100 < n), f' n (fD_gt100 n H) = n - 10)
  (f'_eq2 :
    forall
      (n : nat) (H : n <= 100)
      (d1 : fD (n + 11)) (d2 : fD (f' (n + 11) d1)),
        f' n (fD_le100 n H d1 d2) = f' (f' (n + 11) d1) d2)
  (fD_ind :
    forall
      (P : forall n : nat, fD n -> Type)
      (P_gt100 :
        forall (n : nat) (H : 100 < n),
          P n (fD_gt100 n H))
      (P_le100 :
        forall
          (n : nat) (H : n <= 100)
          (d1 : fD (n + 11)) (d2 : fD (f' (n + 11) d1)),
            P (n + 11) d1 -> P (f' (n + 11) d1) d2 ->
              P n (fD_le100 n H d1 d2)),
      {g : forall (n : nat) (d : fD n), P n d |
        (forall (n : nat) (H : 100 < n),
          g n (fD_gt100 n H) = P_gt100 n H) /\
        (forall
          (n : nat) (H : n <= 100)
          (d1 : fD (n + 11)) (d2 : fD (f' (n + 11) d1)),
            g n (fD_le100 n H d1 d2) =
            P_le100 n H d1 d2
              (g (n + 11) d1)
              (g (f' (n + 11) d1) d2))
      }).

(** Aksjomatyczne kodowanie tej definicji działa tak, jak nauczyliśmy się
    w poprzednim rozdziale: najpierw deklarujemy [fD], potem [f], potem
    konstruktory [fD], potem równania definiujące [f], a na samym końcu
    regułę indukcji.

    Reguła indukcji powstaje analogicznie jak dla [slist] z poprzedniego
    rozdziału. Definiujemy tylko jedną rodzinę typów [fD], więc reguła
    da nam tylko jedną funkcję, [g], o typie [forall (n : nat) (d : fD n),
    P n d], gdzie [P : forall n : nat, fD n -> Type] reprezentuje
    przeciwdziedzinę [g].

    Mamy dwa przypadki: nieindukcyjny [P_gt100] odpowiadający konstruktorowi
    [fD_gt100] oraz [P_le100] odpowiadający za [fD_le100], w którym mamy do
    dyspozycji dwie hipotezy indukcyjne. Otrzymana z reguły funkcja spełnia
    oczekiwane równania. *)

Lemma fD_inv :
  forall (n : nat) (d : fD n),
    {H : 100 < n | d = fD_gt100 n H} +
    {H : n <= 100 &
      {d1 : fD (n + 11) &
      {d2 : fD (f' (n + 11) d1) | d = fD_le100 n H d1 d2}}}.
Proof.
  apply fD_ind.
    intros. left. exists H. reflexivity.
    intros. right. exists H, d1, d2. reflexivity.
Defined.

(** Będziemy też chcieli używać [inversion] na hipotezach postaci [fD n],
    ale [fD] nie jest induktywne (tylko aksjomatyczne), więc musimy
    pożądaną przez nas inwersję zamknąć w lemat. Dowodzimy go oczywiście
    za pomocą reguły indukcji. *)

Lemma f_spec :
  forall (n : nat) (d : fD n),
    n <= 100 -> f' n d = 91.
Proof.
  apply (fD_ind (fun n d => n <= 100 -> f' n d = 91)).
    intros n H H'. lia.
    intros n H d1 d2 IH1 IH2 _.
      destruct (fD_inv _ d1) as
            [[H' eq] | (H' & d1' & d2' & eq)].
        destruct (fD_inv _ d2) as
              [[H'' eq'] | (H'' & d1'' & d2'' & eq')].
          rewrite f'_eq2, eq', f'_eq1, eq, f'_eq1 in *.
            clear IH1 eq eq' H' H''. lia.
          rewrite f'_eq2. apply IH2. assumption.
        rewrite f'_eq2. apply IH2. rewrite IH1.
          lia.
          assumption.
Qed.

(** Możemy też udowodnić charakteryzację funkcji [f]. Dowód wygląda dużo
    groźniej niż ostatnio, ale to wszystko wina narzutu związanego z
    aksjomatycznym kodowaniem.

    Dowód idzie tak: najpierw używamy indukcji, a potem naszego inwersjowego
    lematu na hipotezach postaci [fD _ _]. W kluczowych momentach obliczamy
    funkcję [f] za pomocą definiujących ją równań oraz posługujemy się
    taktyką [lia] do przemielenia oczywistych, ale skomplikowanych
    formalnie faktów z zakresu arytmetyki liczb naturalnych. *)

Lemma fD_all :
  forall n : nat, fD n.
Proof.
  apply (well_founded_ind _ (fun n m => 101 - n < 101 - m)).
    apply wf_inverse_image. apply wf_lt.
    intros n IH. destruct (le_lt_dec n 100).
      assert (d : fD (n + 11)) by (apply IH; lia).
        apply fD_le100 with d.
          assumption.
          apply IH. destruct (fD_inv _ d) as [[H eq] | [H _]].
            rewrite eq, f'_eq1. lia.
            rewrite f_spec.
              lia.
              assumption.
      apply fD_gt100. assumption.
Qed.

(** Dowód tego, że wszystkie argumenty spełniają predykat dziedziny, jest
    taki sam jak ostatnio. Jedyna różnica jest taka, że zamiast [inversion]
    musimy ręcznie aplikować [fD_inv]. *)

Definition f (n : nat) : nat := f' n (fD_all n).

Compute f 42.
(* ===> = f' 42 (fD_all 42) : nat *)

(** Mając [f'] oraz dowód [fD_all] możemy zdefiniować [f], które niestety
    się nie oblicza, gdyż [f'] jest dane aksjomatycznie. *)

Lemma f'_ext :
  forall (n : nat) (d1 d2 : fD n),
    f' n d1 = f' n d2.
Proof.
  apply (fD_ind (fun _ d1 => forall d2, _)); intros.
    rewrite f'_eq1. destruct (fD_inv _ d2) as [[H' eq] | [H' _]].
      rewrite eq, f'_eq1. reflexivity.
      lia.
    rewrite f'_eq2. destruct (fD_inv _ d0) as [[H' eq] | (H' & d1' & d2' & eq)].
      lia.
      subst. rewrite f'_eq2. specialize (H0 d1').
        destruct H0. apply H1.
Qed.

(** Żeby udowodnić regułę indukcyjną, potrzebny nam będzie lemat mówiacy,
    że konkretny dowód tego, że [n] spełnia predykat dziedziny [fD], nie
    wpływa na wynik obliczany przez [f']. Dowód jest prosty: używamy
    indukcji po [d1], a następnie inwersji po pozostałych hipotezach,
    przepisujemy równania definiujące [f'] i kończymy za pomocą rozumowań
    arytmetycznych albo hipotezy indukcyjnej. *)

Lemma f_ind :
  forall
    (P : nat -> nat -> Prop)
    (P_gt100 : forall n : nat, 100 < n -> P n (n - 10))
    (P_le100 :
      forall n : nat, n <= 100 ->
        P (n + 11) (f (n + 11)) ->
        P (f (n + 11)) (f (f (n + 11))) ->
          P n (f (f (n + 11)))),
    forall n : nat, P n (f n).
Proof.
  intros. apply (fD_ind (fun n d => P n (f' n d))); intros.
    rewrite f'_eq1. apply P_gt100. assumption.
    rewrite f'_eq2. specialize (P_le100 _ H).
      unfold f in P_le100.
      rewrite !(f'_ext _ _ d1), !(f'_ext _ _ d2) in P_le100.
      apply P_le100; assumption.
Qed.

(** Dowód samej reguły też jest dość prosty. Zaczynamy od indukcji po
    dowodzie faktu, że [n : nat] spełnia predykat dziedziny [fD] (którym
    to dowodem jest [fD_all n], a który schowany jest w definicji [f]).
    W przypadku nierekurencyjnym przepisujemy równanie definiujące [f']
    i kończymy założeniem.

    W przypadku rekurencyjnym również zaczynamy od przepisania definicji
    [f']. Następnie korzystamy z założenia [P_le100], choć technicznie
    jest to dość skomplikowane - najpierw specjalizujemy je częściowo
    za pomocą hipotezy [H], a potem odwijamy definicję [f] i dwukrotnie
    korzystamy z lematu [f'_ext], żeby typy się zgadzały. Po tej obróbce
    możemy śmiało skorzystać z [P_le100] - jej przesłanki zachodzą na mocy
    założenia. *)

(** **** Ćwiczenie *)

(** Rozwiąż jeszcze raz ćwiczenie o funkcji [g] z poprzedniego podrozdziału,
    ale tym razem wykorzystaj metodę induktywno-rekurencyjnej dziedziny
    zaprezentowaną w niniejszym podrozdziale. *)

Fail Fixpoint g (n : nat) : nat :=
match n with
    | 0 => 0
    | S n => g (g n)
end.

(* begin hide *)

(*
Inductive gD : nat -> Type :=
    | gD_0 : gD 0
    | gD_S : forall n : nat, gD n -> gD (g n) -> gD (S n)

with Fixpoint g' (n : nat) (d : gD n) : nat :=
match d with
    | gD_0 => 0
    | gD_S _ d1 d2 => g' (g' n d1) d2
end.
*)

Axioms
  (gD : nat -> Type)
  (g' : forall n : nat, gD n -> nat)
  (gD_0 : gD 0)
  (gD_S : forall (n : nat) (d1 : gD n), gD (g' n d1) -> gD (S n))
  (g'_eq1 : g' 0 gD_0 = 0)
  (g'_eq2 :
    forall (n : nat) (d1 : gD n) (d2 : gD (g' n d1)),
      g' (S n) (gD_S n d1 d2) = g' (g' n d1) d2)
  (gD_ind : forall
    (P : forall n : nat, gD n -> Type)
    (P0 : P 0 gD_0)
    (PS :
      forall (n : nat) (d1 : gD n) (d2 : gD (g' n d1)),
        P n d1 -> P (g' n d1) d2 -> P (S n) (gD_S n d1 d2)),
    {h : forall (n : nat) (d : gD n), P n d |
      h 0 gD_0 = P0 /\
      (forall (n : nat) (d1 : gD n) (d2 : gD (g' n d1)),
        h (S n) (gD_S n d1 d2) =
        PS n d1 d2 (h n d1) (h (g' n d1) d2))
    }).

Lemma g'_char :
  forall (n : nat) (d : gD n), g' n d = 0.
Proof.
  apply gD_ind.
    apply g'_eq1.
    intros. rewrite g'_eq2. assumption.
Qed.

Lemma gD_all :
  forall n : nat, gD n.
Proof.
  induction n as [| n'].
    exact gD_0.
    apply (gD_S n' IHn'). rewrite g'_char. exact gD_0.
Qed.

Definition g (n : nat) : nat := g' n (gD_all n).

Lemma wut :
  forall (n : nat) (d1 d2 : gD n),
    g' n d1 = g' n d2.
Proof.
  apply (gD_ind (fun _ d1 => forall d2, _)); intros.
  (*  destruct (gD_inv d2).*)
Admitted.

Lemma g_ind' :
  forall
    (P : nat -> nat -> Prop)
    (P_0 : P 0 0)
    (P_S :
      forall n : nat, P n (g n) -> P (g n) (g (g n)) -> P (S n) (g (g n))),
    forall n : nat, P n (g n).
Proof.
  intros.
  apply (gD_ind (fun n d => P n (g' n d))).
    rewrite g'_eq1. assumption.
    intros. rewrite g'_eq2. specialize (P_S n0).
      assert (g' n0 d1 = g n0).
        apply wut.
        rewrite <- !H1 in P_S. assert (g (g' n0 d1) = g' (g' n0 d1) d2).
          apply wut.
          rewrite !H2 in *. apply P_S; assumption.
Qed.

(* end hide *)

End McCarthy'.

(** * Metoda induktywnej dziedziny 2 *)

(** Na koniec została nam do omówienia jeszcze jedna drobna kwestia.
    Poznając metodę induktywnej dziedziny, dowiedzieliśmy się, że
    "predykat" dziedziny tak naprawdę wcale nie jest predykatem, ale
    rodziną typów. Czas naprawić ten szkopuł.

    W niniejszym podrozdziale najpierw zapoznamy się (na przykładzie
    dzielenia - znowu) z wariantem metody induktywnej dziedziny, w
    którym dziedzina faktycznie jest predykatem, a na koniec podumamy,
    dlaczego powinno nas to w ogóle obchodzić. *)

Module again.

Inductive divD : nat -> nat -> Prop :=
    | divD_lt : forall n m : nat, n < S m -> divD n m
    | divD_ge :
        forall n m : nat,
          n >= S m -> divD (n - S m) m -> divD n m.

(** Definicja dziedziny jest taka sama jak ostatnio, ale z tą drobną
    różnicą, że teraz faktycznie jest to predykat.

    Skoro mamy dziedzinę, spróbujmy zdefiniować funkcję pomocniczą
    tak samo jak ostatnio. *)

Fail Fixpoint div_aux {n m : nat} (d : divD n m) : nat :=
match d with
    | divD_lt _ _ _ => 0
    | divD_ge _ _ _ d' => S (div_aux d')
end.

(* ===> The command has indeed failed with message:
        Incorrect elimination of "d" in the inductive type "divD":
        the return type has sort "Set" while it should be "Prop".
        Elimination of an inductive object of sort Prop
        is not allowed on a predicate in sort Set
        because proofs can be eliminated only to build proofs. *)

(** Cóż, nie da się i nie dziwota - gdyby się dało, to zrobiliśmy tak
    już na samym początku. Powód porażki jest całkiem prozaiczny -
    nie możemy definiować programów przez dopasowanie do wzorca dowodów,
    czyli parafrazując, nie możemy konstruować elementów typów sortów
    [Set] ani [Type] przez eliminację elementów typów sortu [Prop].

    Wynika to z faktu, że sort [Prop] z założenia dopuszcza możliwość
    przyjęcia aksjomatu irrelewancji dowodów (ang. proof irrelevance),
    który głosi, że wszystkie dowody danego zdania są równe. Gdybyśmy
    mogli dopasowywać do wzorca dowody zdań definiując programy,
    irrelewancja wyciekłaby do świata programów i wtedy wszystko byłoby
    równe wszystkiemu, co oczywiście daje sprzeczność.

    Jeżeli powyższy opis nie jest przekonujący, zobaczmy to na szybkim
    przykładzie. *)

Module proof_irrelevance_example.

Inductive bool' : Prop :=
    | true' : bool'
    | false' : bool'.

(** Najpierw definiujemy typ [bool'], który wygląda jak [bool], ale
    żyje w sorcie [Prop]. *)

Axiom
  proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.

(** Następnie przyjmujemy aksjomat irrelewancji dowodów, przez co
    [bool'] staje się tym samym co zdanie [True]. *)

Axioms
  (f : bool' -> bool)
  (eq1 : f true' = true)
  (eq2 : f false' = false).

(** Załóżmy, że Coq pozwolił nam zdefiniować funkcję [f : bool' -> bool],
    która potrafi odróżnić [true'] od [false']. *)

Theorem wut :
  true = false.
Proof.
  rewrite <- eq1.
  rewrite (proof_irrelevance _ _ false').
  rewrite eq2.
  reflexivity.
Qed.

(** Jak widać, [true] to to samo co [f true'], ale [true'] to [false']
    na mocy irrelewancji, a [f false'] to przecież [false]. Konkluzja:
    prawda to fałsz, a tego zdecydowanie nie chcemy. Żeby uniknąć
    sprzeczności, nie wolno definiować programów przez eliminację zdań.

    Od powyższej zasady są jednak wyjątki, mianowicie przy konstrukcji
    programów wolno eliminować dowody zdań, które:
    - nie mają konstruktorów, np. [False]
    - mają jeden konstruktor, którego wszystkie argumenty również są
      dowodami zdań

    Powyższy wyjątek od reguły nazywa się "eliminacją singletonów" i
    jest zupełnie niegroźny, gdyż dla takich zdań możemy bez żadnych
    aksjomatów udowodnić, że wszystkie ich dowody są równe. *)

End proof_irrelevance_example.

(** Dobra, koniec tej przydługiej dygresji. Wracamy do metody induktywnej
    dziedziny, gdzie dziedzina naprawdę jest predykatem. Skoro nie możemy
    zdefiniować funkcji bezpośrednio przez eliminację [d : divD n m], to
    jak inaczej?

    Tutaj ujawnia się pewna chytra sztuczka: nie możemy dopasować [d] za
    pomocą [match]a, ale wciąż możemy robić wywołania rekurencyjne na
    podtermach [d]. Wystarczy więc napisać funkcję, która wyjmuje z [d]
    jego podterm (oczywiście jedynie pod warunkiem, że [n >= S m], bo
    tylko wtedy [d] będzie miało jakiś podterm). Ponieważ kodziedziną
    takiej funkcji będzie [divD (n - S m) m], dopasowanie [d] do wzorca
    będzie już legalne.

    Brzmi... chytrze? Zobaczmy, jak wygląda to w praktyce. *)

Lemma divD_ge_inv :
  forall n m : nat, n >= S m -> divD n m -> divD (n - S m) m.
Proof.
  destruct 2.
    apply le_not_lt in H. contradiction.
    exact H1.
Defined.

(** Jeżeli mamy [d : divD n m] i wiemy, że [n >= S m], to [d] musiało
    zostać zrobione konstruktorem [divD_ge]. Możemy to udowodnić po
    prostu rozbijając [d]. W pierwszym przypadkiem dostajemy sprzeczność
    arytmetyczną (bo [n >= S m] i jednocześnie [n < S m]), zaś w drugim
    wynikiem jest pożądany podterm. *)

Fixpoint div'_aux {n m : nat} (d : divD n m) : nat :=
match le_lt_dec (S m) n with
    | right _ => 0
    | left H => S (div'_aux (divD_ge_inv n m H d))
end.

(** Żeby zdefiniować [div'_aux] (czyli, przypomnijmy, zmodyfikowaną wersję
    dzielenia, którego argumentem głównym jest [d : divD n m], nie zaś
    samo [n]), sprawdzamy najpierw, czy mamy do czynienia z przypadkiem
    [n < S m], czy z [n >= S m]. W pierwszym przypadku po prostu zwracamy
    [0], zaś w drugim robimy wywołanie rekurencyjne, którego argumentem
    jest [divD_ge_inv n m H d].

    Term ten, jak się okazuje, jest uznawany przez Coqa za podterm [d],
    a więc wywołanie rekurencyjne na nim jest legalne. Dlaczego jest to
    podterm [d]? Jeżeli odwiniemy definicję [divD_ge_inv] i wykonamy
    występujące tam dopasowanie [d] do wzorca, to wiemy, że nie może być
    ono postaci [divD_lt _ _ _], a zatem musi być postaci
    [divD_ge _ _ _ d'] i wynikiem wykonania funkcji jest [d'], które
    faktycznie jest podtermem [d]. *)

Lemma divD_all :
  forall n m : nat, divD n m.
Proof.
  apply (well_founded_rect nat lt wf_lt (fun _ => forall m : nat, _)).
  intros n IH m.
  destruct (le_lt_dec (S m) n).
    apply divD_ge.
      unfold ge. assumption.
      apply IH. abstract lia.
    apply divD_lt. assumption.
Defined.

(** Dowód tego, że każde [n m : nat] należą do dziedziny, jest dokładnie
    taki sam jak poprzednio. *)

Definition div' (n m : nat) : nat :=
  div'_aux (divD_all n m).

Compute div' 666 7.
(* ===> = 83 : nat *)

(** Ostateczna definicja funkcji [div'] również wygląda identycznie jak
    poprzednio i podobnie elegancko się oblicza, a skoro tak, to czas
    udowodnić, że wykresem [div'] jest [divG]. Nie musimy redefiniować
    wykresu - jest on zdefiniowany dokładnie tak samo jak ostatnio. *)

Lemma divG_div'_aux :
  forall (n m : nat) (d : divD n m),
    divG n m (div'_aux d).
Proof.
  Fail induction d.
  (* ===> The command has indeed failed with message:
          Abstracting over the terms "n" and "m" leads to a term
          fun n0 m0 : nat => divG n0 m0 (div'_aux d)
          which is ill-typed. *)
Abort.

(** Pierwsza próba dowodu kończy się zupełnie niespodziewaną porażką
    już przy pierwszym kroku, czyli próbie odpalenia indukcji po [d]. *)

Check divD_ind.
(* ===>
  divD_ind :
    forall P : nat -> nat -> Prop,
    (forall n m : nat, n < S m -> P n m) ->
    (forall n m : nat,
      n >= S m -> divD (n - S m) m -> P (n - S m) m -> P n m) ->
    forall n n0 : nat, divD n n0 -> P n n0
*)

(** Powód jest prosty: konkluzja, czyli [divG n m (div'_aux d)] zależy
    od [d], ale domyślna reguła indukcji wygenerowana przez Coqa, czyli
    [divD_ind], nie jest ani trochę zależna i nie dopuszcza możliwości,
    by konkluzja zależała od [d]. Potrzebna jest więc nam zależna reguła
    indukcji.

    Na szczęście nie musimy implementować jej ręcznie - Coq potrafi
    zrobić to dla nas automatycznie (ale skoro tak, to dlaczego nie
    zrobił tego od razu? - nie pytaj, niezbadane są wyroki...). *)

Scheme divD_ind' := Induction for divD Sort Prop.

(** Do generowania reguł indukcji służy komenda [Scheme]. [divD_ind']
    to nazwa reguły, [Induction for divD] mówi nam, dla jakiego typu
    lub rodziny typów chcemy regułę, zaś [Sort Prop] mówi, że chcemy
    regułę, w której przeciwdziedziną motywu jest [Prop] (tak na
    marginesie - motyw eliminacji to typ lub rodzina typów, której
    element chcemy za pomocą eliminacji skonstruować - powinienem
    był wprowadzić tę nazwę wcześniej). *)

(* begin hide *)
(** TODO: wprowadzić gdzieś wcześniej określenie "motyw eliminacji". *)
(* end hide *)

Check divD_ind'.
(* ===>
  divD_ind' :
    forall P : forall n n0 : nat, divD n n0 -> Prop,
    (forall (n m : nat) (l : n < S m), P n m (divD_lt n m l)) ->
    (forall (n m : nat) (g : n >= S m) (d : divD (n - S m) m),
      P (n - S m) m d -> P n m (divD_ge n m g d)) ->
    forall (n n0 : nat) (d : divD n n0), P n n0 d
*)

(** Jak widać, reguła wygenerowana przez komendę [Scheme] jest zależna,
    gdyż jednym z argumentów [P] jest [divD n n0]. Czas więc wrócić do
    dowodu faktu, że [divG] jest wykresem [div']. *)

Lemma divG_div'_aux :
  forall (n m : nat) (d : divD n m),
    divG n m (@div'_aux n m d).
Proof.
  induction d using divD_ind'.
    unfold div'_aux. destruct (le_lt_dec (S m) n).
      lia.
      constructor. assumption.
    unfold div'_aux. destruct (le_lt_dec (S m) n).
      constructor.
        assumption.
        exact IHd.
      lia.
Qed.

(** Indukcję z użyciem innej niż domyślna reguły możemy zrobić za
    pomocą taktyki [induction d using divD_ind']. Tym razem reguła
    jest wystarczająco ogólna, więc indukcja się udaje.

    Następnym krokiem w obu przypadkach jest odwinięcie definicji
    [div'_aux] i sprawdzenie, czy [n < S m], czy może [n >= S m].
    Taki sposób postępowania jest kluczowy, gdyż próba użycia tu
    taktyki [cbn] skończyłaby się katastrofą - zamiast uprościć
    cel, wyprulibyśmy z niego flaki, które zalałyby nam ekran, a
    wtedy nawet przeczytanie celu byłoby trudne. Jeżeli nie
    wierzysz, spróbuj.

    Mamy więc dowód poprawności [div'_aux] względem wykresu. Wszystkie
    pozostałe dowody przechodzą bez zmian, więc nie będziemy ich tutaj
    powtarzać. *)

End again.

(** Do rozstrzygnięcia pozostaje nam ostatnia już kwestia - po cholerę
    w ogóle bawić się w coś takiego? Powyższe trudności z eliminacją
    [d], dowodzeniem lematów wyciągających z [d] podtermy, dowodzeniem
    przez indukcję po [d], generowaniem lepszych reguł indukcyjnych i
    unikaniem użycia taktyki [cbn] powinny jako żywo uzmysłowić nam,
    że uczynienie dziedziny [divD] prawdziwym predykatem było raczej
    upośledzonym pomysłem.

    Odpowiedź jest krótka i mało przekonująca, a jest nią mechanizm
    ekstrakcji. Cóż to takiego? Otóż Coq dobrze sprawdza się przy
    definiowaniu programów i dowodzeniu ich właściwości, ale raczej
    słabo w ich wykonywaniu (komendy [Compute] czy [Eval] są dość
    kiepskie).

    Mechanizm ekstrakcji to coś, co nas z tej nędzy trochę ratuje: daje
    on nam możliwość przetłumaczenia naszego programu w Coqu na program
    w jakimś nieco bardziej mainstreamowym języku funkcyjnym (jak OCaml,
    Haskell czy Scheme), w których programy da się normalnie odpalać i
    działają nawet szybko.

    Mechanizm ten nie będzie nas interesował, ponieważ moim zdaniem jest
    on ślepą uliczką ewolucji - zamiast niego trzeba będzie po prostu
    wymyślić sposób efektywnej kompilacji Coqowych programow, ale to już
    temat na inną bajkę.

    Nie będziemy zatem zbytnio zagłębiać się w szczegóły ekstrakcji -
    zanim zupełnie o niej zapomnimy, zobaczmy tylko jeden przykład. *)

Extraction Language Haskell.

(** Komenda [Extraction Language] ustawia język, do którego chcemy
    ekstrahować. My użyjemy Haskella, gdyż pozostałych dostępnych
    języków nie lubię. *)

Extraction again.div'.
(* ===> div' :: Nat -> Nat -> Nat
        div' = div'_aux *)

(** Komenda [Extraction p] tłumaczy Coqowy program [p] na program
    Haskellowy. Mimo że nie znamy Haskella, spróbujmy przeczytać
    wynikowy program.

    Wynikiem ekstrakcji jest Haskellowa funkcja [div'] o typie
    [Nat -> Nat -> Nat], gdzie [Nat] to Haskellowa wersja Coqowego [nat]
    (podwójny dwukropek [::] oznacza w Haskellu to samo, co pojedynczy
    dwukropek [:] w Coqu). Funkcja [div'] jest zdefiniowana jako... i tu
    zaskoczenie... [div'_aux]. Ale jak to? Rzućmy jeszcze raz okiem na
    oryginalną, Coqową definicję. *)

Print again.div'.
(* ===> again.div' = 
        fun n m : nat => again.div'_aux (again.divD_all n m)
             : nat -> nat -> nat *)

(** Gdzież w wyekstrahowanym programie podział się dowód [divD_all n m]?
    Otóż nie ma go, bo Haskell to zwykły język programowania, w którym
    nie można dowodzić. O to właśnie chodzi w mechanizmie ekstrakcji -
    w procesie ekstrakcji wyrzucić z Coqowego programu wszystkie dowody
    i przetłumaczyć tylko tę część programu, która jest niezbędna, by
    wyekstrahowany program się obliczał.

    Mogłoby się wydawać dziwne, że najpierw w pocie czoła dowodzimy czegoś
    w Coqu, a potem mechanizm ekstrakcji się tego pozbywa. Jest to jednak
    całkiem naturalne - skoro udało nam się udowodnić jakąś właściwość
    naszego programu, to wiemy, że ma on tę właściwość i dowód nie jest
    nam już do niczego potrzebny, a zatem ekstrakcja może się go pozbyć. *)

Print again.div'_aux.
(* ===>
    again.div'_aux = 
    fix div'_aux (n m : nat) (d : again.divD n m) {struct d} : nat :=
    match le_lt_dec (S m) n with
        | left H =>
            S (div'_aux (n - S m) m (again.divD_ge_inv n m H d))
        | right _ => 0
    end
      : forall n m : nat, again.divD n m -> nat *)

Extraction again.div'_aux.
(* ===>
    div'_aux :: Nat -> Nat -> Nat
    div'_aux n m =
      case le_lt_dec (S m) n of {
       Left -> S (div'_aux (sub n (S m)) m);
       Right -> O} *)

(** A tak wygląda wyekstrahowana funkcja [div'_aux]. Jeżeli pominiemy
    różnice składniowe między Coqiem i Haskellem (w Coqu typ jest na
    dole, po dwukropku, a w Haskellu na górze, przed definicją; w Coqu
    mamy [match], a w Haskellu [case] etc.) to wygląda całkiem podobnie.
    Kluczową różnicą jest widniejący w Coqowej wersji dowód należenia do
    dziedziny [again.divD_ge_inv n m H d], który w Haskellowym ekstrakcie
    został usunięty.

    Cały ten cyrk z przerabianiem [divD] na prawdziwy predykat był po
    to, żeby dowód należenia do dziedziny mógł zostać usunięty podczas
    ekstrakcji. Dzięki temu wyekstrahowany program w Haskellu wygląda
    jak gdyby został napisany ręcznie. Jest też szybszy i krótszy, bo
    nie ma tam wzmianki o [divD_all], która musiałaby się pojawić, gdyby
    [divD] było rodziną typów, a nie predykatem. *)

Extraction div'_aux.
(* ===> 
    div'_aux :: Nat -> Nat -> DivD -> Nat
    div'_aux _ _ h =
      case h of {
       DivD_lt _ _ -> O;
       DivD_ge n m h' -> S (div'_aux (sub n (S m)) m h')} *)

(** Tak wygląda ekstrakt oryginalnego [div'_aux], tzn. tego, w którym [divD]
    nie jest predykatem, lecz rodziną typów. W wyekstrahowanym programie, w
    typie funkcji [div'_aux] pojawia się złowieszczy typ [DivD], który jest
    zupełnie zbędny, bo Haskell (i żaden inny funkcyjny język programowania,
    który nie jest przeznaczony do dowodzenia) nie narzuca żadnych ograniczeń
    na wywołania rekurencyjne.

    No, to by było na tyle. Życzę ci, żebyś nigdy nie musiał stosować
    wariantu metody induktywnej dziedziny opisanej w tym podrozdziale
    ani nie musiał niczego ekstrahować. *)

(** * Plugin [Equations] *)

(** **** Ćwiczenie *)

(** Zainstaluj plugin Equations:
    https://github.com/mattam82/Coq-Equations

    Przeczytaj tutorial:
    https://raw.githubusercontent.com/mattam82/Coq-Equations/master/doc/equations_intro.v

    Następnie znajdź jakiś swój dowód przez indukcję, który był skomplikowany
    i napisz prostszy dowód za pomocą komendy [Equations] i taktyki [funelim].
*)

(** * Podsumowanie (TODO) *)

(** Póki co nie jest źle, wszakże udało nam się odkryć indukcję wykresową,
    czyli metodę dowodzenia właściwości funkcji za pomocą specjalnie do
    niej dostosowanej reguły indukcji, wywodzącej się od reguły indukcji
    jej wykresu. *)