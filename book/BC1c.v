(** * BC1c: Podstawy programowania funkcyjnego [TODO] *)

(* begin hide *)
(*
TODO 1: Kwestia non-uniform parameters i jak je zasymulować przy użyciu indeksów.
TODO 2: Typy induktywne z parametrami + równość = rodziny indeksowane.
TODO 3: Nie trzeba specjalizować hipotezy, żeby przepisać.
TODO 4: Opisać dokładniej definiowanie przez dowód.
TODO 5: Opisać alternatywne składnie na typy induktywne (czyli te, w
TODO 5: których nie trzeba aż tak dużo pisać i są inne słowa kluczowe,
TODO 5: jak np. [Variant]). Jest to mądry sposób rozróżniania poziomów
TODO 5: zaawansowania typów induktywnych (np. rodzin induktywnych nie
TODO 5: można definiować bez podawania indeksów w przeciwdziedzinie).
*)
(* end hide *)

(** W poprzednim rozdziale dowiedzieliśmy się już co nieco o typach, a
    także spotkaliśmy kilka z nich oraz kilka sposobów tworzenia nowych
    typów ze starych (takich jak np. koniunkcja; pamiętaj, że zdania są
    typami). W tym rozdziale dowiemy się, jak definiować nowe typy przy
    pomocy indukcji oraz jak użyć rekursji do definiowania funkcji, które
    operują na tych typach. *)

(** W Coqu są trzy główne rodzaje typów: produkt zależny, typy induktywne
    i typy koinduktywne. Z pierwszym z nich już się zetknęliśmy, drugi
    poznamy w tym rozdziale, trzeci na razie pominiemy.

    Typ induktywny definiuje się przy pomocy zbioru konstruktorów, które
    służą, jak sama nazwa wskazuje, do budowania termów tego typu.
    Konstruktory te są funkcjami (być może zależnymi), których
    przeciwdziedziną jest definiowany typ, ale niczego nie
    obliczają — nadają jedynie termom ich "kształt". W szczególności, nie
    mają nic wspólnego z konstruktorami w takich językach jak C++ lub Java
    — nie mogą przetwarzać swoich argumentów, alokować pamięci, dokonywać
    operacji wejścia/wyjścia etc.

    Tym, co jest ważne w przypadku konstruktorów, jest ich ilość, nazwy
    oraz ilość i typy przyjmowanych argumentów. To te cztery rzeczy decydują
    o tym, jakie "kształty" będą miały termy danego typu, a więc i czym
    będzie sam typ. W ogolności każdy term jest skończonym, ukorzenionym
    drzewem, którego kształt zależy od charakterystyki konstruktorów tak:
    - każdy konstruktor to inny rodzaj węzła (nazwa konstruktora to nazwa
      węzła)
    - konstruktory nierekurencyjne to liście, a rekurencyjne — węzły
      wewnętrzne
    - argumenty konstruktorów to dane przechowywane w danym węźle *)

(** Typ induktywny można wyobrażać sobie jako przestrzeń zawierającą
    te i tylko te drzewa, które można zrobić przy pomocy jego
    konstruktorów. Nie przejmuj się, jeżeli opis ten wydaje ci się
    dziwny — sposób definiowania typów induktywnych i ich wartości
    w Coqu jest diametralnie różny od sposobu definiowania klas i
    obiektów w językach imperatywnych i wymaga przyzwyczajenia się
    do niego. Zobaczmy, jak powyższy opis ma się do konkretnych
    przykładów. *)

(** * Wstęp *)

(** ** Typy i typowanie statyczne (TODO) *)

(** Tutaj historyjka o tym, że im bardziej statyczne jest typowanie, tym
    szybciej po popełnieniu błędu jesteśmy w stanie go wykryć. *)

(** *** Typy vs testy *)

(** * Typy, programy, zdania, dowody i specyfikacje (TODO) *)

(** Tu zestawić ze sobą P : Prop, A : Type, p : P, x : A.

    Wytłumaczyć relację między typami, zdaniami, specyfikacjami
    programów, przestrzeniami, etc. *)

(** ** Przydatne komendy *)

(** Czas, aby opisać kilka przydatnych komend. *)

Check unit.
(* ===> unit : Set *)

Print unit.
(* ===> Inductive unit : Set := tt : unit *)

(** Przypomnijmy, że komenda [Check] wyświetla typ danego jej termu,
    a [Print] wypisuje jego definicję. *)

Search nat.

(** [Search] wyświetla wszystkie obiekty, które zawierają podaną nazwę.
    W naszym przypadku pokazały się wszystkie funkcje, w których
    sygnaturze występuje typ [nat]. *)

SearchPattern (_ + _ = _).

(** [SearchPattern] jako argument bierze wzorzec i wyświetla wszystkie
    obiekty, które zawierają podterm pasujący do danego wzorca. W naszym
    przypadku pokazały się twierdzenia, w których występuje podterm
    mający po lewej dodawanie, a po prawej cokolwiek.

    Dokładny opis wszystkich komend znajdziesz
    #<a class='link' href='https://coq.inria.fr/refman/coq-cmdindex.html'>tutaj</a>#. *)

(** * Typy wbudowane (TODO) *)

(** Tutaj będą opisane typy, która można spotkać w normalnych językach
    programowania, takie jak [int] czy [float]. *)

(** * Funkcje (TODO) *)

(** * Enumeracje (TODO) *)

(* begin hide *)
(*
TODO 1: przykładowe typy: dni tygodnia, miesiące, pory roku, strony świata
TODO 2: opisać opcje za pomocą analogii do "która godzina", jak w
TODO 2: https://www.cs.cmu.edu/~15150/previous-semesters/2012-spring/resources/lectures/09.pdf
TODO 3: boole pozwalają patrzeć, opcje pozwalają widzieć
*)
(* end hide *)

(** Najprostszym rodzajem typów induktywnych są enumeracje, czyli typy,
    których wszystkie konstruktory są stałymi. *)

Inductive bool : Set :=
| true : bool
| false : bool.

(** Definicja typu induktywnego ma następującą postać: najpierw występuje
    słowo kluczowe [Inductive], następnie nazwa typu, a po dwukropku sort
    ([Set], [Prop] lub [Type]). Następnie wymieniamy konstruktory typu —
    dla czytelności każdy w osobnej linii. Mają one swoje unikalne nazwy i
    są funkcjami, których przeciwdziedziną jest definiowany typ. W naszym
    przypadku mamy 2 konstruktory, zwane [true] oraz [false], które są
    funkcjami zeroargumentowymi.

    Definicję tę możemy odczytać następująco: "[true] jest typu [bool],
    [false] jest typu [bool] i nie ma żadnych więcej wartości typu
    [bool]".

    Uwaga: należy odróżnić symbole [:=] oraz [=]. Pierwszy z nich służy
    do definiowania, a drugi do zapisywania równości.

    Zapis [name := term] oznacza "niech od teraz [name] będzie inną nazwą
    dla [term]". Jest to komenda, a nie zdanie logiczne. Od teraz jeżeli
    natkniemy się na nazwę [name], będziemy mogli odwinąć jej definicję i
    wstawić w jej miejsce [term]. Przykład: [Definition five := 5].
    Antyprzykład: [2 := 5] (błąd składni).

    Zapis [a = b] oznacza "[a] jest równe [b]". Jest to zdanie logiczne,
    a nie komenda. Zdanie to rzecz jasna nie musi być prawdziwe. Przykład:
    [2 = 5]. Antyprzykład: [five = 5] (jeżeli [five] nie jest zdefiniowane,
    to dostajemy komunikat w stylu "nie znaleziono nazwy [five]"). *)

Definition negb (b : bool) : bool :=
match b with
| true => false
| false => true
end.

(** Definicja funkcji wygląda tak: najpierw mamy słowo kluczowe [Definition]
    (jeżeli funkcja nie jest rekurencyjna), następnie argumenty funkcji
    w postaci [(name : type)]; po dwukropku przeciwdziedzina, a po symbolu
    [:=] ciało funkcji.

    Podstawowym narzędziem służącym do definiowania funkcji jest
    dopasowanie do wzorca (ang. pattern matching). Pozwala ono sprawdzić,
    którego konstruktora użyto do zrobienia dopasowywanej wartości.
    Podobnym tworem występującym w językach imperatywnych jest instrukcja
    switch, ale dopasowanie do wzorca jest od niej dużo potężniejsze.

    Nasza funkcja działa następująco: sprawdzamy, którym konstruktorem
    zrobiono argument [b] — jeżeli było to [true], zwracamy [false], a
    gdy było to [false], zwracamy [true]. *)

(** **** Ćwiczenie ([andb] i [orb]) *)

(** Zdefiniuj funkcje [andb] (koniunkcja boolowska) i [orb] (alternatywa
    boolowska). *)

(* begin hide *)
Definition andb (b1 b2 : bool) : bool :=
match b1 with
| true => b2
| false => false
end.

Definition orb (b1 b2 : bool) : bool :=
match b1 with
| true => true
| false => b2
end.
(* end hide *)

(** Zanim odpalimy naszą funkcję, powinniśmy zadać sobie pytanie: w jaki
    sposób programy są wykonywane? W celu lepszego zrozumienia tego
    zagadnienia porównamy ewaluację programów napisanych w językach
    imperatywnych oraz funkcyjnych.

    Rozważmy bardzo uproszczony model: interpreter wykonuje program,
    który nie dokonuje operacji wejścia/wyjścia, napisany w jakimś
    języku imperatywnym. W tej sytuacji działanie interpretera
    sprowadza się do tego, że czyta on kod programu instrukcja po
    instrukcji, a następnie w zależności od przeczytanej instrukcji
    odpowiednio zmienia swój stan.

    W języku czysto funkcyjnym taki model ewaluacji jest niemożliwy,
    gdyż nie dysponujemy globalnym stanem. Zamiast tego, w Coqu
    wykonanie programu polega na jego redukcji. O co chodzi?
    Przypomnijmy najpierw, że program to term, którego typem jest
    specyfikacja, czyli typ sortu [Set]. Termy mogą być redukowane,
    czyli zamieniane na równoważne, ale prostsze, przy użyciu
    reguł redukcji. Prześledźmy wykonanie programu [negb true]
    krok po kroku. *)

Eval cbv delta in negb true.
(* ===> = (fun b : bool => match b with
                           | true => false
                           | false => true
                           end) true
        : bool *)

(** Redukcja delta odwija definicje. Żeby użyć jakiejś redukcji, używamy
    komendy [Eval cbv redukcje in term]. *)

Eval cbv delta beta in negb true.
(* ===> = match true with
          | true => false
          | false => true
          end
        : bool *)

(** Redukcja beta podstawia argument do funkcji. *)

Eval cbv delta beta iota in negb true.
(* === = false : bool *)

(** Redukcja jota dopasowuje term do wzorca i zamienia go na term
    znajdujący się po prawej stronie [=>] dla dopasowanego przypadku. *)

Eval cbv in negb true.
(* ===> = false : bool *)

(** Żeby zredukować term za jednym zamachem, możemy pominąć nazwy
    redukcji występujące po [cbv] — w taki wypadku zostaną zaaplikowane
    wszystkie możliwe redukcje, czyli program zostanie wykonany. Do jego
    wykonania możemy też użyć komend [Eval cbn] oraz [Eval compute] (a
    także [Eval simpl], ale taktyka [simpl] jest przestarzała, więc nie
    polecam). *)

(** **** Ćwiczenie (redukcja) *)

(** Zredukuj "ręcznie" programy [andb false false] oraz [orb false true]. *)

(** Jak widać, wykonanie programu w Coqu jest dość toporne. Wynika to
    z faktu, że Coq nie został stworzony do wykonywania programów, a
    jedynie do ich definiowania i dowodzenia ich poprawności. Aby użyć
    programu napisanego w Coqu w świecie rzeczywistym, stosuje się
    zazwyczaj mechanizm ekstrakcji, który pozwala z programu napisanego
    w Coqu automatycznie uzyskać program w Scheme, OCamlu lub Haskellu,
    które są od Coqa dużo szybsze i dużo powszechniej używane. My jednak
    nie będziemy się tym przejmować. 

    Zdefiniowawszy naszą funkcję, możemy zadać sobie pytanie:
    czy definicja jest poprawna? Gdybyśmy pisali w jednym z
    języków imperatywnych, moglibyśmy napisać dla niej testy
    jednostkowe, polegające np. na tym, że generujemy losowo
    wejście funkcji i sprawdzamy, czy wynik posiada żądaną przez
    nas właściwość. Coq umożliwia nam coś dużo silniejszego:
    możemy wyrazić przy pomocy twierdzenia, że funkcja posiada
    interesującą nas własność, a następnie spróbować je udowodnić.
    Jeżeli nam się powiedzie, mamy całkowitą pewność, że funkcja
    rzeczywiście posiada żądaną własność. *)

Lemma negb_involutive :
  forall b : bool, negb (negb b) = b.
Proof.
  intros. destruct b.
    cbn. reflexivity.
    cbn. reflexivity.
Qed.

(** Nasze twierdzenie głosi, że funkcja [negb] jest inwolucją,
    tzn. że dwukrotne jej zaaplikowanie do danego argumentu
    nie zmienia go, lub też, innymi słowy, że [negb] jest
    swoją własną odwrotnością.

    Dowód przebiega w następujący sposób: taktyką [intro]
    wprowadzamy zmienną [b] do kontekstu, a następnie
    używamy taktyki [destruct], aby sprawdzić, którym
    konstruktorem została zrobiona. Ponieważ typ [bool] ma
    dwa konstruktory, taktyka ta generuje nam dwa podcele:
    musimy udowodnić twierdzenie osobno dla przypadku, gdy
    [b = true] oraz dla [b = false]. Potem przy pomocy
    taktyki [cbn] redukujemy (czyli wykonujemy) programy
    [negb (negb true)] i [negb (negb false)]. Zauważ, że
    byłoby to niemożliwe, gdyby argument był postaci [b]
    (nie można wtedy zaaplikować żadnej redukcji), ale jest
    jak najbardziej możliwe, gdy jest on postaci [true] albo
    [false] (wtedy redukcja przebiega jak w przykładzie). Na
    koniec używamy taktyki [reflexivity], która potrafi udowodnić
    cel postaci [a = a].

    [destruct] jest taktykowym odpowiednikiem dopasowania do wzorca
    i bardzo często jest używany, gdy mamy do czynienia z czymś,
    co zostało za jego pomocą zdefiniowane.

    Być może poczułeś dyskomfort spowodowany tym, że cel postaci
    [a = a] można udowodnić dwoma różnymi taktykami ([reflexivity]
    oraz [trivial]) albo że termy można redukować na cztery różne
    sposoby ([Eval cbn], [Eval cbv], [Eval compute], [Eval simpl]).
    Niestety, będziesz musiał się do tego przyzwyczaić — język
    taktyka Coqa jest strasznie zabałaganiony i niesie ze sobą
    spory bagaż swej mrocznej przeszłości. Na szczęście od niedawna
    trwają prace nad jego ucywilizowaniem, czego pierwsze efekty
    widać już od wersji 8.5. W chwilach desperacji uratować może
    cię jedynie dokumentacja:
    - #<a class='link' href='https://coq.inria.fr/refman/coq-tacindex.html'>Indeks taktyk</a>#
    - #<a class='link' href='https://coq.inria.fr/refman/proof-engine/ltac.html'>Ltac</a># *)

Lemma negb_involutive' :
  forall b : bool, negb (negb b) = b.
Proof.
  destruct b; cbn; reflexivity.
Qed.

(** Zauważmy, że nie musimy używać taktyki [intro], żeby wprowadzić
    [b] do kontekstu: taktyka [destruct] sama jest w stanie wykryć,
    że nie ma go w kontekście i wprowadzić je tam przed rozbiciem
    go na konstruktory. Zauważmy też, że oba podcele rozwiązaliśmy
    w ten sam sposób, więc możemy użyć kombinatora [;] (średnika),
    żeby rozwiązać je oba za jednym zamachem. *)

(** **** Ćwiczenie (logika boolowska) *)

(** Udowodnij poniższe twierdzenia. *)

Lemma andb_assoc :
  forall b1 b2 b3 : bool,
    andb b1 (andb b2 b3) = andb (andb b1 b2) b3.
(* begin hide *)
Proof.
  destruct b1, b2, b3; cbn; trivial.
Qed.
(* end hide *)

Lemma andb_comm :
  forall b1 b2 : bool,
    andb b1 b2 = andb b2 b1.
(* begin hide *)
Proof.
  destruct b1, b2; cbn; trivial.
Qed.
(* end hide *)

Lemma orb_assoc :
  forall b1 b2 b3 : bool,
    orb b1 (orb b2 b3) = orb (orb b1 b2) b3.
(* begin hide *)
Proof.
  destruct b1, b2, b3; cbn; trivial.
Qed.
(* end hide *)

Lemma orb_comm :
  forall b1 b2 : bool,
    orb b1 b2 = orb b2 b1.
(* begin hide *)
Proof.
  destruct b1, b2; cbn; reflexivity.
Qed.
(* end hide *)

Lemma andb_true_elim :
  forall b1 b2 : bool,
    andb b1 b2 = true -> b1 = true /\ b2 = true.
(* begin hide *)
Proof.
  destruct b1, b2; cbn; split; auto.
Qed.
(* end hide *)

(** **** Ćwiczenie (róża kierunków) *)

Module Directions.

(** Zdefiniuj typ opisujący kierunki podstawowe (północ, południe, wschód,
    zachód - dodatkowe punkty za nadanie im sensownych nazw). *)

(* begin hide *)
Inductive D : Type :=
| N : D
| S : D
| W : D
| E : D.
(* end hide *)

(** Zdefiniuj funkcje [turnL] i [turnR], które reprezentują obrót o 90
    stopni przeciwnie/zgodnie z ruchem wskazówek zegara. Sformułuj i
    udowodnij twierdzenia mówiące, że:
    - obrót cztery razy w lewo/prawo niczego nie zmienia
    - obrót trzy razy w prawo to tak naprawdę obrót w lewo (jest to tzw.
      pierwsze twierdzenie korwinizmu)
    - obrót trzy razy w lewo to obrót w prawo (jest to tzw. drugie
      twierdzenie korwinizmu)
    - obrót w prawo, a potem w lewo niczego nie zmienia
    - obrót w lewo, a potem w prawo niczego nie zmienia
    - każdy kierunek to północ, południe, wschód lub zachód (tzn. nie ma
      innych kierunków) *)

(* begin hide *)
Definition turnL (d : D) : D :=
match d with
| N => W
| W => S
| S => E
| E => N
end.

Definition turnR (d : D) : D :=
match d with
| N => E
| E => S
| S => W
| W => N
end.

Lemma turnL4 :
  forall d : D, turnL (turnL (turnL (turnL d))) = d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma turnR4 :
  forall d : D, turnR (turnR (turnR (turnR d))) = d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma turnL3 :
  forall d : D, turnL (turnL (turnL d)) = turnR d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma turnR3 :
  forall d : D, turnR (turnR (turnR d)) = turnL d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma turnL_turnR :
  forall d : D, turnL (turnR d) = d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma turnR_turnL :
  forall d : D, turnR (turnL d) = d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma D_uniqueness :
  forall d : D, d = N \/ d = S \/ d = W \/ d = E.
Proof.
  destruct d; repeat (left + right); trivial; fail.
Qed.
(* end hide *)

(** Zdefiniuj funkcję [opposite], które danemu kierunkowi przyporządkowuje
    kierunek do niego przeciwny (czyli północy przyporządkowuje południe
    etc.). Wymyśl i udowodnij jakąś ciekawę specyfikację dla tej funkcji
    (wskazówka: powiąż ją z [turnL] i [turnR]). *)

(* begin hide *)
Definition opposite (d : D) : D :=
match d with
| N => S
| S => N
| W => E
| E => W
end.

Lemma opposite_involutive :
  forall d : D, opposite (opposite d) = d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma opposite_turnL :
  forall d : D, opposite (turnL d) = turnR d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma opposite_turnR :
  forall d : D, opposite (turnR d) = turnL d.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma opposite_turnL_comm :
  forall d : D, opposite (turnL d) = turnL (opposite d).
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma opposite_turnR_comm :
  forall d : D, opposite (turnR d) = turnR (opposite d).
Proof.
  destruct d; cbn; reflexivity.
Qed.
(* end hide *)

(** Zdefiniuj funkcję [is_opposite], która bierze dwa kierunki i zwraca
    [true], gdy są one przeciwne oraz [false] w przeciwnym wypadku. Wymyśl
    i udowodnij jakąś specyfikację dla tej funkcji. Wskazówka: jakie są jej
    związku z [turnL], [turnR] i [opposite]? *)

(* begin hide *)
Definition is_opposite (d1 d2 : D) : bool :=
match d1, d2 with
| N, S => true
| S, N => true
| W, E => true
| E, W => true
| _, _ => false
end.

Lemma is_opposite_turnL :
  forall d1 d2 : D,
    is_opposite (turnL d1) (turnL d2) = is_opposite d1 d2.
Proof.
  destruct d1, d2; cbn; reflexivity.
Qed.

Lemma is_opposite_turnR :
  forall d1 d2 : D,
    is_opposite (turnR d1) (turnR d2) = is_opposite d1 d2.
Proof.
  destruct d1, d2; cbn; reflexivity.
Qed.

Lemma is_opposite_opposite_l :
  forall d : D, is_opposite (opposite d) d = true.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma is_opposite_opposite_r :
  forall d : D, is_opposite d (opposite d) = true.
Proof.
  destruct d; cbn; reflexivity.
Qed.

Lemma is_opposite_comm :
  forall d1 d2 : D,
    is_opposite d1 d2 = is_opposite d2 d1.
Proof.
  destruct d1, d2; cbn; reflexivity.
Qed.
(* end hide *)

(** Pokaż, że funkcje [turnL], [turnR] oraz [opposite] są injekcjami i
    surjekcjami (co to dokładnie znacz, dowiemy się później). Uwaga: to
    zadanie wymaga użyci taktyki [inversion], która jest opisana w
    podrozdziale o polimorfizmie. *)

Lemma turnL_inj :
  forall x y : D, turnL x = turnL y -> x = y.
(* begin hide *)
Proof.
  destruct x, y; cbn; intros; inversion H; reflexivity.
Qed.
(* end hide *)

Lemma turnR_inj :
  forall x y : D, turnR x = turnR y -> x = y.
(* begin hide *)
Proof.
  destruct x, y; cbn; intros; inversion H; reflexivity.
Qed.
(* end hide *)

Lemma opposite_inj :
  forall x y : D, opposite x = opposite y -> x = y.
(* begin hide *)
Proof.
  destruct x, y; cbn; intros; inversion H; reflexivity.
Qed.
(* end hide *)

Lemma turnL_sur :
  forall y : D, exists x : D, turnL x = y.
(* begin hide *)
Proof.
  intro. exists (turnR y). apply turnL_turnR.
Qed.
(* end hide *)

Lemma turnR_sur :
  forall y : D, exists x : D, turnR x = y.
(* begin hide *)
Proof.
  intro. exists (turnL y). apply turnR_turnL.
Qed.
(* end hide *)

Lemma opposite_sur :
  forall y : D, exists x : D, opposite x = y.
(* begin hide *)
Proof.
  intro. exists (opposite y). apply opposite_involutive.
Qed.
(* end hide *)

End Directions.

(** **** Ćwiczenie (różne enumeracje) *)

(** Zdefiniuj typy induktywne reprezentujące:
    - dni tygodnia
    - miesiące
    - kolory podstawowe systemu RGB *)

(* begin hide *)
Inductive Day : Type :=
| Mon : Day
| Tue : Day
| Wed : Day
| Thu : Day
| Fri : Day
| Sat : Day
| Sun : Day.

Inductive Month : Type :=
| Jan : Month
| Feb : Month
| Mar : Month
| Apr : Month
| May : Month
| Jun : Month
| Jul : Month
| Aug : Month
| Sep : Month
| Oct : Month
| Nov : Month
| Dec : Month.

Inductive Color : Type :=
| R : Color
| G : Color
| B : Color.
(* end hide *)

(** Wymyśl do nich jakieś ciekawe funkcje i twierdzenia. *)

(* begin hide *)

(** TODO *)

Definition nextDay (d : Day) : Day :=
match d with
| Mon => Tue
| Tue => Wed
| Wed => Thu
| Thu => Fri
| Fri => Sat
| Sat => Sun
| Sun => Mon
end.

Definition prevDay (d : Day) : Day :=
match d with
| Mon => Sun
| Tue => Mon
| Wed => Tue
| Thu => Wed
| Fri => Thu
| Sat => Fri
| Sun => Sat
end.
(* end hide *)

(** ** Ważne enumeracje *)

Module ImportantTypes.

(** *** Typ pusty *)

Inductive Empty_set : Set := .

(** [Empty_set] jest, jak sama nazwa wskazuje, typem pustym. Żaden term
    nie jest tego typu. Innymi słowy: jeżeli jakiś term jest typu [Empty_set],
    to mamy sprzeczność. *)

Definition create {A : Type} (x : Empty_set) : A :=
  match x with end.

(** Jeżeli mamy term typu [Empty_set], to możemy w sposób niemal magiczny
    wyczarować term dowolnego typu [A], używając dopasowania do wzorca z
    pustym wzorcem. *)

(** **** Ćwiczenie ([create_unique]) *)

(** Udowodnij, że powyższa funkcja jest unikalna. *)

Lemma create_unique :
  forall (A : Type) (f : Empty_set -> A),
    (forall x : Empty_set, create x = f x).
(* begin hide *)
Proof.
  intros. destruct x.
Qed.
(* end hide *)

(** **** Ćwiczenie ([no_fun_from_nonempty_to_empty]) *)

(** Pokaż, że nie istnieją funkcje z typu niepustego w pusty. *)

Lemma no_fun_from_nonempty_to_empty :
  forall (A : Type) (a : A) (f : A -> Empty_set), False.
(* begin hide *)
Proof.
  intros. specialize (f a). destruct f.
Qed.
(* end hide *)

(** *** Singleton *)

Inductive unit : Set :=
| tt : unit.

(** [unit] jest typem, który ma tylko jeden term, zwany [tt] (nazwa ta
    jest wzięta z sufitu). *)

Definition delete {A : Type} (a : A) : unit := tt.

(** Funkcja [delete] jest w pewien sposób "dualna" do napotkanej przez
    nas wcześniej funkcji [create]. Mając term typu [Empty_set] mogliśmy
    stworzyć term dowolnego innego typu, zaś mając term dowolnego typu
    [A], możemy "zapomnieć o nim" albo "skasować go", wysyłając go
    funkcją [delete] w jedyny term typu [unit], czyli [tt].

    Uwaga: określenie "skasować" nie ma nic wspólnego z fizycznym
    niszczeniem albo dealokacją pamięci. Jest to tylko metafora. *)

(** **** Ćwiczenie ([delete_unique]) *)

(** Pokaż, że funkcja [delete] jest unikalna. *)

Lemma delete_unique :
  forall (A : Type) (f : A -> unit),
    (forall x : A, delete x = f x).
(* begin hide *)
Proof.
  intros. destruct (delete x). destruct (f x). trivial.
Qed.
(* end hide *)

End ImportantTypes.

(** ** Reguły eliminacji dla enumeracji *)

Module enum.

Inductive I : Type :=
| c0 : I
| c1 : I
| c2 : I.

(** Najprymitywniejszymi z typów induktywnych są enumeracje. Definiując je,
    wymieniamy po prostu wszystkie ich elementy. *)

Definition I_case_nondep_type : Type :=
  forall P : Type, P -> P -> P -> I -> P.

(** Reguła definiowania przez przypadki jest banalnie prosta: jeżeli w
    jakimś inny typie [P] uda nam się znaleźć po jednym elemencie dla każdego
    z elementów naszego typu [I], to możemy zrobić funkcję [I -> P]. *)

Definition I_case_nondep : I_case_nondep_type :=
  fun (P : Type) (c0' c1' c2' : P) (i : I) =>
  match i with
  | c0 => c0'
  | c1 => c1'
  | c2 => c2'
  end.

(** Regułę zdefiniować możemy za pomocą dopasowania do wzorca. *)

Definition I_case_dep_type : Type :=
  forall (P : I -> Type) (c0' : P c0) (c1' : P c1) (c2' : P c2),
    forall i : I, P i.

(** Zależną regułę definiowania przez przypadki możemy uzyskać z poprzedniej
    uzależniając przeciwdziedzinę [P] od dziedziny. *)

Definition I_case_dep : I_case_dep_type :=
  fun (P : I -> Type) (c0' : P c0) (c1' : P c1) (c2' : P c2) (i : I) =>
  match i with
  | c0 => c0'
  | c1 => c1'
  | c2 => c2'
  end.

(** Definicja, jak widać, jest taka sama jak poprzednio, więc obliczeniowo
    obie reguły zachowują się tak samo. Różnica leży jedynie w typach -
    druga reguła jest ogólniejsza. *)

End enum.

(** * Sumy (TODO) *)

Module MySum.

Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {A B} _.
Arguments inr {A B} _.

(** Suma [A] i [B] to typ, którego termy są albo termami typu [A],
    zawiniętymi w konstruktor [inl], albo termami typu [B], zawiniętymi
    w konstruktor [inr]. Suma, w przeciwieństwie do produktu, zdecydowanie
    nie ma projekcji. *)

(** **** Ćwiczenie (sumy bez projekcji) *)

(** Pokaż, że suma nie ma projekcji. *)

Lemma sum_no_fst :
  forall (proj : forall A B : Type, sum A B -> A), False.
(* begin hide *)
Proof.
  intros. apply proj with nat. apply inr. exact 0.
Qed.
(* end hide *)

Lemma sum_no_snd :
  forall (proj : forall A B : Type, sum A B -> B), False.
(* begin hide *)
Proof.
  intros. apply proj with nat. apply inl. exact 0.
Qed.
(* end hide *)

End MySum.

(** * Enumeracje z argumentami (TODO) *)

(** * Produkty (TODO) *)

Module MyProd.

Inductive prod (A B : Type) : Type :=
| pair : A -> B -> prod A B.

Arguments pair {A B} _ _.

(** Produkt typów [A] i [B] to typ, którego termami są pary. Pierwszy
    element pary to term typu [A], a drugi to term typu [B]. Tym, co
    charakteryzuje produkt, są projekcje:
    - [fst : forall A B : Type, prod A B -> A] wyciąga z pary jej
      pierwszy element
    - [snd : forall A B : Type, prod A B -> B] wyciąga z pary jej
      drugi element *)

(** **** Ćwiczenie (projekcje) *)

(** Zdefiniuj projekcje i udowodnij poprawność swoich definicji. *)

(* begin hide *)
Definition fst {A B : Type} (p : prod A B) : A :=
match p with
| pair a b => a
end.

Definition snd {A B : Type} (p : prod A B) : B :=
match p with
| pair a b => b
end.
(* end hide *)

Lemma proj_spec :
  forall (A B : Type) (p : prod A B),
    p = pair (fst p) (snd p).
(* begin hide *)
Proof.
  destruct p. cbn. trivial.
Qed.
(* end hide *)

End MyProd.

(** * Rekordy (TODO) *)

(** W wielu językach programowania występują typy rekordów (ang. record
    types). Charakteryzują się one tym, że mają z góry określoną ilość
    pól o potencjalnie różnych typach. W językach imperatywnych rekordy
    wyewoluowały zaś w obiekty, które różnią się od rekordów tym, że mogą
    zawierać również funkcje, których dziedziną jest obiekt, w którym
    funkcja się znajduje.

    W Coqu mamy do dyspozycji rekordy, ale nie obiekty. Trzeba tu po raz
    kolejny pochwalić siłę systemu typów Coqa — o ile w większości języków
    rekordy są osobnym konstruktem językowym, o tyle w Coqu mogą być one z
    łatwością reprezentowane przez typy induktywne z jednym konstruktorem
    (wraz z odpowiednimi projekcjami, które dekonstruują rekord). *)

Module rational2.

Record rational : Set :=
{
  sign : bool;
  numerator : nat;
  denominator : nat;
  denominator_not_zero : denominator <> 0
}.

(** Z typem induktywnym o jednym konstruktorze już się zetknęliśmy,
    próbując zdefiniować liczby wymierne. Powyższa definicja używająca
    rekordu ma drobną przewagę nad poprzednią, w której słowo kluczowe
    [Inductive] pada explicité:
    - wygląda ładniej
    - ma projekcje *)

Check sign.
(* ===> sign : rational -> bool *)

Check denominator_not_zero.
(* ===> denominator_not_zero
    : forall r : rational, denominator r <> 0 *)

(** Dzięki projekcjom mamy dostęp do poszczególnych pól rekordu bez
    konieczności jego dekonstruowania — nie musimy używać konstruktu
    [match] ani taktyki [destruct], jeżeli nie chcemy. Często bywa to
    bardzo wygodne.

    Projekcję [sign] możemy interpretować jako funkcję, która bierze
    liczbę wymierną [r] i zwraca jej znak, zaś projekcja
    [denominator_not_zero] mówi nam, że mianownik żadnej liczb wymiernej
    nie jest zerem.

    Pozwa tymi wizualno-praktycznymi drobnostkami, obie definicje są
    równoważne (w szczególności, powyższa definicja, podobnie jak
    poprzednia, nie jest dobrą reprezentacją liczb wymiernych). *)

End rational2.

(** **** Ćwiczenie (kalendarz) *)

(** Zdefiniuj typ induktywny reprezentujący datę i napisz ręcznie
    wszystkie projekcje. Następnie zdefiniuj rekord reprezentujący
    datę i zachwyć się tym, ile czasu i głupiego pisania zaoszczędziłbyś,
    gdybyś od razu użył rekordu... *)

(* begin hide *)
(* TODO : zrób to ćwiczenie *)
(* end hide *)

(** * Prymitywne rekordy (TODO) *)

(** Tutaj wprowadzić prymitywne projekcje i porównać ze zwykłymi rekordami. *)

CoInductive product (A : Type) (B : Type) : Type :=
{
  fst : A;
  snd : B;
}.

Definition swap {A B : Type} (p : product A B) : product B A :=
{|
  fst := snd A B p;
  snd := fst A B p;
|}.

Definition para_liczb : product nat nat :=
{|
  fst := 42;
  snd := 1;
|}.

(*
Compute fst nat nat para_liczb.
Compute snd nat nat para_liczb.
*)

Lemma eq_product :
  forall {A B : Type} (p q : product A B),
    fst A B p = fst A B q -> snd A B p = snd A B q -> p = q.
Proof.
  destruct p, q. cbn. intros -> ->. reflexivity.
Qed.

(** * Programowanie a dowodzenie - eliminacja zdań (TODO) *)

(** Tutaj opisać ograniczenia na eliminację dowodów zdań. *)

(** * Typy hybrydowe *)

(** Ostatnim z typów istotnych z punktu widzenia silnych specyfikacji
    jest typ o wdzięcznej nazwie [sumor]. *)

Module sumor.

Inductive sumor (A : Type) (B : Prop) : Type :=
| inleft : A -> sumor A B
| inright : B -> sumor A B.

(** Jak sama nazwa wskazuje, [sumor] jest hybrydą sumy rozłącznej [sum]
    oraz dysjunkcji [or]. Możemy go interpretować jako typ, którego
    elementami są elementy [A] albo wymówki w stylu "nie mam elementu [A],
    ponieważ zachodzi zdanie [B]". [B] nie zależy od [A], a więc jest to
    zwykła suma (a nie suma zależna, czyli uogólnienie produktu). [sumor]
    żyje w [Type], a więc jest to specyfikacja i liczy się konkretna
    postać jego termów, a nie jedynie fakt ich istnienia. *)

(** **** Ćwiczenie ([pred']) *)

(** Zdefiniuj funkcję [pred'], która przypisuje liczbie naturalnej jej
    poprzednik. Poprzednikiem [0] nie powinno być [0]. Mogą przydać ci
    się typ [sumor] oraz sposób definiowania za pomocą taktyk, omówiony
    w podrozdziale dotyczącym sum zależnych. *)

(* begin hide *)
Definition pred' (n : nat) : sumor nat (n = 0) :=
match n with
| 0 => inright _ _ eq_refl
| S n' => inleft _ _ n'
end.
(* end hide *)

End sumor.

(** * Typy pozytywne i negatywne (TODO) *)

(** Tutaj tłumaczenie co to znaczy, że typ jest pozytywny/negatywny. *)

(** * Moduły (TODO) *)

(** Nie lubię Coqowego systemu modułów, więc w tym rozdziale jeszcze
    długo nic nie zagości. *)

(* begin hide *)

(** Trochę materiałów o modułach, coby sobie to wszystko lepiej w głowie posortować.

    Moduły w Coqu:
    - https://coq.inria.fr/refman/language/core/modules.html
    - https://github.com/coq/coq/wiki/ModuleSystemTutorial
    - http://adam.chlipala.net/cpdt/html/Large.html
    - https://www.researchgate.net/publication/2840744_Implementing_Modules_in_the_Coq_System
    - https://stackoverflow.com/questions/48837996/import-module-vs-include-module-in-coq-module-system/49717951

    Moduły w OCamlu:
    - https://ocaml.org/learn/tutorials/modules.html
    - https://dev.realworldocaml.org/files-modules-and-programs.html
    - https://www.cs.cornell.edu/courses/cs3110/2019fa/textbook/modules/intro.html
    - https://www.ocaml.org/releases/4.11/htmlman/moduleexamples.html

    First-class modules:
    - https://dev.realworldocaml.org/first-class-modules.html
    - https://www.cs.cornell.edu/courses/cs3110/2020sp/manual-4.8/manual028.html
    - https://www.cl.cam.ac.uk/~jdy22/papers/first-class-modules.pdf
    - https://people.mpi-sws.org/~rossberg/1ml/1ml-extended.pdf

    Modular implicits:
    - https://tycon.github.io/modular-implicits.html
    - http://www.lpw25.net/papers/ml2014.pdf

    Tajpklasy/moduły w Haskellu:
    - https://www.youtube.com/watch?v=XtogTwzcGcM (DOBRY KONTENT!)
    - https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/first_class_modules.pdf

    OCamlowe moduły vs Haskellowe tajpklasy:
    - https://blog.shaynefletcher.org/2017/05/more-type-classes-in-ocaml.html
    - http://okmij.org/ftp/Computation/typeclass.html
    - https://accu.org/journals/overload/25/142/fletcher_2445/
    - https://people.mpi-sws.org/~dreyer/papers/mtc/main-long.pdf
    - https://www.reddit.com/r/ocaml/comments/364vqg/examples_of_ocaml_modules_which_cant_be_done_in/

*)

(* end hide *)

(** * Styl, czyli formatowanie, wcięcia i komentarze (TODO) *)

(* begin hide *)
(*
TODO 1: Dodać rozdział o stylu, wcięciach, komentowaniu etc.
TODO 1: Patrz tu: https://www.cs.princeton.edu/courses/archive/fall19/cos326/style.php#1
TODO 2: Co do stylu, to tu jest Haskell style guide:
TODO 2: https://kowainik.github.io/posts/2019-02-06-style-guide)
TODO 3: Najtrudniejsza rzeczą w programowaniu jest wymyślanie nazw
*)
(* end hide *)

(** Tu będzie rozdział o stylu, czyli rzeczach takich jak czytelne
    formatowanie kodu czy pisanie zrozumiałych komentarzy. *)

(** ** Formatowanie kodu i wcięcia *)

(** ** Komentarze *)

(** ** Ars nazywandi, czyli trudna sztuka wymyślania nazw *)