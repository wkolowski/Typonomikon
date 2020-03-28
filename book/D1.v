(** * D1: Indukcja i rekursja *)

(** W poprzednim rozdziale dowiedzieliśmy się już co nieco o typach, a
    także spotkaliśmy kilka z nich oraz kilka sposobów tworzenia nowych
    typów ze starych (takich jak np. koniunkcja; pamiętaj, że zdania są
    typami). W tym rozdziale dowiemy się, jak definiować nowe typy przy
    pomocy indukcji oraz jak użyć rekursji do definiowania funkcji, które
    operują na tych typach. *)

(** * Typy induktywne *)

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

(** ** Enumeracje *)

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

    Definicję tę możemy udczytać następująco: "[true] jest typu [bool],
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

Theorem negb_involutive :
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
    - https://coq.inria.fr/refman/coq-tacindex.html
    - https://coq.inria.fr/refman/proof-engine/ltac.html *)

Theorem negb_involutive' :
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

Theorem andb_assoc :
  forall b1 b2 b3 : bool,
    andb b1 (andb b2 b3) = andb (andb b1 b2) b3.
(* begin hide *)
Proof.
  destruct b1, b2, b3; cbn; trivial.
Qed.
(* end hide *)

Theorem andb_comm :
  forall b1 b2 : bool,
    andb b1 b2 = andb b2 b1.
(* begin hide *)
Proof.
  destruct b1, b2; cbn; trivial.
Qed.
(* end hide *)

Theorem orb_assoc :
  forall b1 b2 b3 : bool,
    orb b1 (orb b2 b3) = orb (orb b1 b2) b3.
(* begin hide *)
Proof.
  destruct b1, b2, b3; cbn; trivial.
Qed.
(* end hide *)

Theorem orb_comm :
  forall b1 b2 : bool,
    orb b1 b2 = orb b2 b1.
(* begin hide *)
Proof.
  destruct b1, b2; cbn; reflexivity.
Qed.
(* end hide *)

Theorem andb_true_elim :
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

(** ** Konstruktory rekurencyjne *)

(** Powiedzieliśmy, że termy typów induktywnych są drzewami. W przypadku
    enumeracji jest to słabo widoczne, gdyż drzewa te są zdegenerowane —
    są to po prostu punkciki oznaczone nazwami konstruktorów. Efekt
    rozgałęzienia możemy uzyskać, gdy jeden z konstruktorów będzie
    rekurencyjny, tzn. gdy jako argument będzie przyjmował term typu,
    który właśnie definiujemy. Naszym przykładem będą liczby naturalne
    (choć i tutaj rozgałęzienie będzie nieco zdegenerowane  �- każdy term
    będzie mógł mieć co najwyżej jedno). *)

Module NatDef.

(** Mechanizm modułów jest podobny do mechanizmu sekcji i na razie nie
    będzie nas interesował — użyjemy go, żeby nie zaśmiecać głównej
    przestrzeni nazw (mechanizm sekcji w tym przypadku by nie pomógł). *)

Inductive nat : Set :=
    | O : nat
    | S : nat -> nat.

Notation "0" := O.

(** Uwaga: nazwa pierwszego konstruktora to duża litera O, a nie cyfra 0
    — cyfry nie mogą być nazwami. Żeby obejść tę niedogodność, musimy
    posłużyć się mechanizmem notacji — dzięki temu będziemy mogli pisać
    0 zamiast O.

    Definicję tę możemy odczytać w następujący sposób: "[0] jest liczbą
    naturalną; jeżeli [n] jest liczbą naturalną, to [S n] również jest
    liczbą naturalną". Konstruktor [S] odpowiada tutaj dodawaniu jedynki:
    [S 0] to 1, [S (S 0)] to 2, [S (S (S 0))] to 3 i tak dalej. *)

Check (S (S (S 0))).
(* ===> S (S (S 0)) : nat *)

End NatDef.

Check S (S (S 0)).
(* ===> 3 : nat *)

(** Ręczne liczenie ilości [S] w każdej liczbie szybko staje się trudne
    nawet dla małych liczb. Na szczęście standardowa biblioteka Coqa
    udostępnia notacje, które pozwalają nam zapisywać liczby naturalne
    przy pomocy dobrze znanych nam cyfr arabskich. Żeby uzyskać do nich
    dostęp, musimy opuścić zdefiniowany przez nas moduł [NatDef], żeby
    nasza definicja [nat] nie przysłaniała tej bibliotecznej. Zaczniemy
    za to nowy moduł, żebyśmy mogli swobodnie zredefiniować działania
    na liczbach naturalnych z biblioteki standardowej. *)

Module NatOps.

Fixpoint plus (n m : nat) : nat :=
match n with
    | 0 => m
    | S n' => S (plus n' m)
end.

(* begin hide *)
(*Notation "n + m" := (plus n m). Dzięki notacjom będziemy też mogli pisać
    [n + m] zamiast [plus n m].*)
(* end hide *)

(** W zapisie unarnym liczby naturalne możemy wyobrażać sobie jako kupki
    [S]-ów, więc dodawanie dwóch liczb sprowadza się do przerzucenia [S]-ów
    z jednej kupki na drugą.

    Definiowanie funkcji dla typów z konstruktorami rekurencyjnymi
    wygląda podobnie jak dla enumeracji, ale występują drobne różnice:
    jeżeli będziemy używać rekurencji, musimy zaznaczyć to za pomocą
    słowa kluczowego [Fixpoint] (zamiast wcześniejszego [Definition]).
    Zauważmy też, że jeżeli funkcja ma wiele argumentów tego samego typu,
    możemy napisać [(arg1 ... argN : type)] zamiast dłuższego [(arg1 : type)
    ... (argN : type)].

    Jeżeli konstruktor typu induktywnego bierze jakieś argumenty, to wzorce,
    które go dopasowują, stają się nieco bardziej skomplikowane: poza nazwą
    konstruktora muszą też dopasowywać argumenty — w naszym przypadku używamy
    zmiennej o nazwie [n'], która istnieje tylko lokalnie (tylko we wzorcu
    dopasowania oraz po prawej stronie strzałki [=>]).

    Naszą funkcję zdefiniowaliśmy przy pomocy najbardziej elementarnego
    rodzaju rekursji, jaki jest dostępny w Coqu: rekursji strukturalnej.
    W przypadku takiej rekursji wywołania rekurencyjne mogą odbywać się
    jedynie na termach strukturalnie mniejszych, niż obecny argument
    główny rekurencji. W naszym przypadku argumentem głównym jest [n]
    (bo on jest dopasowywany), zaś rekurencyjnych wywołań dokonujemy na
    [n'], gdzie [n = S n']. [n'] jest strukturalnie mniejszy od [S n'],
    gdyż składa się z jednego [S] mniej. Jeżeli wyobrazimy sobie nasze
    liczby jako kupki [S]-ów, to wywołania rekurencyjne możemy robić
    jedynie po zdjęciu z kupki co najmniej jednego [S]. *)

(** **** Ćwiczenie (rekursja niestrukturalna) *)

(** Wymyśl funkcję z liczb naturalnych w liczby naturalne,
    która jest rekurencyjna, ale nie jest strukturalnie rekurencyjna.
    Precyzyjniej pisząc: później okaże się, że wszystkie formy
    rekurencji to tak naprawdę rekursja strukturalna pod przykrywką.
    Wymyśl taką definicję, która na pierwszy rzut oka nie jest
    strukturalnie rekurencyjna. *)

(* begin hide *)
(** Odpowiedź: dzielenie. *)
(* end hide *)

(** Podobnie jak w przypadku funkcji [negb], tak i tym razem w celu
    sprawdzenia poprawności naszej definicji spróbujemy udowodnić, że
    posiada ona właściwości, których się spodziewamy. *)

Theorem plus_O_n :
  forall n : nat, plus 0 n = n.
Proof.
  intro. cbn. trivial.
Qed.

(** Tak prosty dowód nie powinien nas dziwić — wszakże twierdzenie to
    wynika wprost z definicji (spróbuj zredukować "ręcznie" wyrażenie
    [0 + n]). *)

Theorem plus_n_O_try1 :
  forall n : nat, plus n 0 = n.
Proof.
  intro. destruct n.
    trivial.
    cbn. f_equal.
Abort.

(** Tym razem nie jest już tak prosto — [n + 0 = n] nie wynika z definicji
    przez prostą redukcję, gdyż argumentem głównym funkcji [plus] jest
    jej pierwszy argument, czyli [n]. Żeby móc zredukować to wyrażenie,
    musimy rozbić [n]. Pokazanie, że [0 + 0 = 0] jest trywialne, ale
    drugi przypadek jest już beznadziejny. Ponieważ funkcje zachowują
    równość (czyli [a = b] implikuje [f a = f b]), to aby pokazać, że
    [f a = f b], wystarczyć pokazać, że [a = b] — w ten właśnie sposób
    działa taktyka [f_equal]. Nie pomogła nam ona jednak — po jej
    użyciu mamy do pokazania to samo, co na początku, czyli [n + 0 = n]. *)

Theorem plus_n_O :
  forall n : nat, plus n 0 = n.
Proof.
  intro. induction n.
    trivial.
    cbn. f_equal. assumption.
Qed.

(** Do udowodnienia tego twierdzenia musimy posłużyć się indukcją.
    Indukcja jest sposobem dowodzenia właściwości typów induktywnych
    i funkcji rekurencyjnych, który działa mniej więcej tak: żeby
    udowodnić, że każdy term typu [A] posiada własność [P], pokazujemy
    najpierw, że konstruktory nierekurencyjne posiadają tę własność
    dla dowolnych argumentów, a następnie, że konstruktory rekurencyjne
    zachowują tę własność.

    W przypadku liczb naturalnych indukcja wygląda tak: żeby pokazać,
    że każda liczba naturalna ma własność [P], najpierw należy
    pokazać, że zachodzi [P 0], a następnie, że jeżeli zachodzi [P n],
    to zachodzi także [P (S n)]. Z tych dwóch reguł możemy zbudować
    dowód na to, że [P n] zachodzi dla dowolnego [n].

    Ten sposób rozumowania możemy zrealizować w Coqu przy pomocy
    taktyki [induction]. Działa ona podobnie do [destruct], czyli
    rozbija podany term na konstruktory, ale w przypadku konstruktorów
    rekurencyjnych robi coś jeszcze — daje nam założenie indukcyjne,
    które mówi, że dowodzone przez nas twierdzenie zachodzi dla
    rekurencyjnych argumentów konstruktora. Właśnie tego było nam
    trzeba: założenie indukcyjne pozwala nam dokończyć dowód. *)

Theorem plus_comm :
  forall n m : nat, plus n m = plus m n.
Proof.
  induction n as [| n']; cbn; intros.
    rewrite plus_n_O. trivial.
    induction m as [| m'].
      cbn. rewrite plus_n_O. trivial.
      cbn. rewrite IHn'. rewrite <- IHm'. cbn. rewrite IHn'.
        trivial.
Qed.

(** Pojedyncza indukcja nie zawsze wystarcza, co obrazuje powyższy przypadek.
    Zauważmy, że przed użyciem [induction] nie musimy wprowadzać zmiennych
    do kontekstu — taktyka ta robi to sama, podobnie jak [destruct].
    Również podobnie jak [destruct], możemy przekazać jej wzorzec, którym
    nadajemy nazwy argumentom konstruktorów, na które rozbijany jest term.
    
    W ogólności wzorzec ma postać [[a11 .. a1n | ... | am1 .. amk]]. Pionowa
    kreska oddziela argumenty poszczególnych konstruktorów: [a11 .. a1n]
    to argumenty pierwszego konstruktora, zaś [am1 .. amk] to argumenty
    m-tego konstruktora. [nat] ma dwa konstruktory, z czego pierwszy nie
    bierze argumentów, a drugi bierze jeden, więc nasz wzorzec ma postać
    [[| n']]. Dzięki temu nie musimy polegać na domyślnych nazwach nadawanych
    argumentom przez Coqa, które często wprowadzają zamęt.

    Jeżeli damy taktyce [rewrite] nazwę hipotezy lub twierdzenia, którego
    konkluzją jest [a = b], to zamienia ona w obecnym podcelu wszystkie
    wystąpienia [a] na [b] oraz generuje tyle podcelów, ile przesłanek ma
    użyta hipoteza lub twierdzenie. W naszym przypadku użyliśmy udowodnionego
    uprzednio twierdzenia [plus_n_O], które nie ma przesłanek, czego efektem
    było po prostu przepisanie [plus m 0] na [m].

    Przepisywać możemy też w drugą stronę pisząc [rewrite <-]. Wtedy jeżeli
    konkluzją danego [rewrite] twierdzenia lub hipotezy jest [a = b], to
    w celu wszystkie [b] zostaną zastąpione przez [a]. *)

(** **** Ćwiczenie (mnożenie) *)

(** Zdefiniuj mnożenie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint mult (n m : nat) : nat :=
match n with
    | 0 => 0
    | S n' => plus m (mult n' m)
end.
(* end hide *)

Theorem mult_0_l :
  forall n : nat, mult 0 n = 0.
(* begin hide *)
Proof.
  induction n; trivial.
Qed.
(* end hide *)

Theorem mult_0_r :
  forall n : nat, mult n 0 = 0.
(* begin hide *)
Proof.
  induction n as [| n'].
    cbn. trivial.
    cbn. assumption.
Restart.
  induction n; trivial.
Qed.
(* end hide *)

Theorem mult_1_l :
  forall n : nat, mult 1 n = n.
(* begin hide *)
Proof.
  destruct n as [| n'].
    cbn. trivial.
    cbn. rewrite plus_n_O. trivial.
Restart.
  destruct n; cbn; try rewrite plus_n_O; trivial.
Qed.
(* end hide*)

Theorem mult_1_r :
  forall n : nat, mult n 1 = n.
(* begin hide *)
Proof.
  induction n.
    cbn. trivial.
    cbn. rewrite IHn. trivial.
Restart.
  induction n; cbn; try rewrite IHn; trivial.
Qed.
(* end hide *)

(** Jeżeli ćwiczenie było za proste i czytałeś podrozdział o kombinatorach
    taktyk, to spróbuj udowodnić:
    - dwa pierwsze twierdzenia używając nie więcej niż 2 taktyk
    - trzecie bez użycia indukcji, używając nie więcej niż 4 taktyk
    - czwarte używając nie więcej niż 4 taktyk *)

(** Wszystkie dowody powinny być nie dłuższe niż pół linijki. *)

(** **** Ćwiczenie (inne dodawanie) *)

(** Dodawanie można alternatywnie zdefiniować także w sposób przedstawiony
    poniżej. Udowodnij, że ta definicja jest równoważna poprzedniej. *)

Fixpoint plus' (n m : nat) : nat :=
match m with
    | 0 => n
    | S m' => plus' (S n) m'
end.

Theorem plus'_n_0 :
  forall n : nat, plus' n 0 = n.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Theorem plus'_S :
  forall n m : nat, plus' (S n) m = S (plus' n m).
(* begin hide *)
Proof.
  intros. generalize dependent n.
  induction m as [| m']; cbn; intros.
    reflexivity.
    rewrite IHm'. reflexivity.
Qed.
(* end hide *)

Theorem plus'_0_n :
  forall n : nat, plus' 0 n = n.
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    cbn. rewrite plus'_S. rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem plus'_comm :
  forall n m : nat, plus' n m = plus' m n.
(* begin hide *)
Proof.
  intros. generalize dependent n. induction m as [| m']; cbn; intros.
    rewrite plus'_0_n. trivial.
    rewrite IHm'. cbn. trivial.
Qed.
(* end hide *)

Theorem plus'_is_plus :
  forall n m : nat, plus' n m = plus n m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intro.
    apply plus'_0_n.
    rewrite <- IHn'. rewrite plus'_S. trivial.
Qed.
(* end hide *)

End NatOps.

(** ** Typy polimorficzne i właściwości konstruktorów *)

(** Przy pomocy komendy [Inductive] możemy definiować nie tylko typy
    induktywne, ale także rodziny typów induktywnych. Jeżeli taka
    rodzina parametryzowana jest typem, to mamy do czynienia z
    polimorfizmem. *)

Inductive option (A : Type) : Type :=
    | Some : A -> option A
    | None : option A.

(** [option] jest rodziną typów, zaś samo [option A] dla ustalonego [A]
    jest typem, który reprezentuje możliwość istnienia wartości typu [A]
    (konstruktor [Some]) albo i nie (konstruktor [None]). *)

Check Some.
(* ===> Some forall A : Type, A -> option A *)

Check Some nat 5.
(* ===> Some nat 5 *)

Check None.
(* ===> None forall A : Type, option A *)

Arguments Some [A] _.
Arguments None [A].

(** Jak widać typ [A], będący parametrem [option], jest też pierwszym
    argumentem każdego z konstruktorów.
    Pisanie go bywa uciążliwe, ale na szczęście Coq może sam wywnioskować
    jego wartość, jeżeli mu każemy. Komenda [Arguments] pozwala nam
    określić, które argumenty mają być domyślne — chcemy, aby argument [A]
    był domyślny, gdyż w przypadku konstruktura [Some] może być wywnioskowany
    z drugiego argumentu, a w przypadku [None] — zazwyczaj z kontekstu.

    Konstruktory typów induktywnych mają kilka właściwości, o którch
    warto wiedzieć. Po pierwsze, wartości zrobione za pomocą różnych
    konstruktorów są różne. Jest to konieczne, gdyż za pomocą dopasowania
    do wzorca możemy rozróżnić różne konstruktory — gdyby były one
    równe, uzyskalibyśmy sprzeczność. *)

Definition isSome {A : Type} (a : option A) : Prop :=
match a with
    | Some _ => True
    | None => False
end.

(** Pomocnicza funkcja [isSome] ma za zadanie sprawdzić, którym
    konstruktorem zrobiono wartość typu [option A]. Zapis [{A : Type}]
    oznacza, że [A] jest argumentem domyślnym funkcji — Coq może go
    wywnioskować, gdyż zna typ argumentu [a] (jest nim [option A]).
    Zauważ też, że funkcja ta zwraca zdania logiczne, a nie wartości
    boolowskie. *)

Theorem some_not_none :
  forall (A : Type) (a : A), Some a <> None.
Proof.
  unfold not; intros. change False with (isSome (@None A)).
  rewrite <- H. cbn. trivial.
Qed.

(** Możemy użyć tej pomocniczej funkcji, aby udowodnić, że konstruktory
    [Some] i [None] tworzą różne wartości. Taktyka [change t1 with t2]
    pozwala nam zamienić term [t1] na [t2] pod warunkiem, że są one
    konwertowalne (czyli jeden z nich redukuje się do drugiego). W naszym
    wypadku chcemy zastąpić [False] przez [isSome (@None A)], który
    redukuje się do [False] (spróbuj zredukować to wyrażenie ręcznie).

    Użycie symbolu [@] pozwala nam dla danego wyrażenia zrezygnować z
    próby automatycznego wywnioskowania argumentów domyślnych — w tym
    przypadku Coq nie potrafiłby wywnioskować argumentu dla konstruktora
    [None], więc musimy podać ten argument ręcznie. 

    Następnie możemy skorzystać z równania [Some a = None], żeby
    uzyskać cel postaci [isSome (Some a)]. Cel ten redukuje się
    do [True], którego udowodnienie jest trywialne. *)

Theorem some_not_none' :
  forall (A : Type) (a : A), Some a <> None.
Proof. inversion 1. Qed.

(** Cała procedura jest dość skomplikowana — w szczególności wymaga
    napisania funkcji pomocniczej. Na szczęście Coq jest w stanie
    sam wywnioskować, że konstruktory są różne. Możemy zrobić to
    przy pomocy znanej nam z poprzedniego rozdziału taktyki [inversion].
    Zapis [inversion 1] oznacza: wprowadź zmienne związane przez
    kwantyfikację uniwersaną do kontekstu i użyj taktyki [inversion]
    na pierwszej przesłance implikacji. W naszym przypadku implikacja
    jest ukryta w definicji negacji: [Some a <> None] to tak naprawdę
    [Some a = None -> False]. *)

Theorem some_inj :
  forall (A : Type) (x y : A),
    Some x = Some y -> x = y.
Proof.
  intros. injection H. trivial.
Qed.

(** Kolejną właściwością konstruktorów jest fakt, że są one injekcjami,
    tzn. jeżeli dwa termy zrobione tymi samymi konstruktorami są równe,
    to argumenty tych konstruktorów też są równe.

    Aby skorzystać z tej właściwości w dowodzie, możemy użyć taktyki
    [injection], podając jej jako argument nazwę hipotezy. Jeżeli
    hipoteza jest postaci [C x1 ... xn = C y1 ... yn], to nasz cel [G]
    zostanie zastąpiony przez implikację [x1 = y1 -> ... -> xn = yn -> G].
    Po wprowadzeniu hipotez do kontekstu możemy użyć ich do udowodnienia
    [G], zazwyczaj przy pomocy taktyki [rewrite].

    W naszym przypadku [H] miało postać [Some x = Some y], a cel [x = y],
    więc [injection H] przekształciło cel do postaci [x = y -> x = y],
    który jest trywialny. *)

Theorem some_inj' :
  forall (A : Type) (x y : A), Some x = Some y -> x = y.
Proof.
  inversion 1. trivial.
Qed.

(** Taktyka [inversion] może nam pomóc również wtedy, kiedy chcemy skorzystać
    z injektywności konstruktorów. W zasadzie jest ona nawet bardziej
    przydatna — działa ona tak jak [injection], ale zamiast zostawiać cel w
    postaci [x1 = y1 -> ... -> G], wprowadza ona wygenerowane hipotezy do
    kontekstu, a następnie przepisuje w celu wszystkie, których przepisanie
    jest możliwe. W ten sposób oszczędza nam ona nieco pisania.

    W naszym przypadku [inverson 1] dodała do kontekstu hipotezę [x = y],
    a następnie przepisała ją w celu (który miał postać [x = y]), dając
    cel postaci [y = y]. *)

Theorem some_inj'' :
  forall (A : Type) (x y : A), Some x = Some y -> x = y.
Proof.
  injection 1. intro. subst. trivial.
Qed.

(** Taktyką ułatwiającą pracę z [injection] oraz [inversion] jest [subst].
    Taktyka ta wyszukuje w kontekście hipotezy postaci [a = b],
    przepisuje je we wszystkich hipotezach w kontekście i celu, w których
    jest to możliwe, a następnie usuwa. Szczególnie często spotykana
    jest kombinacja [inversion H; subst], gdyż [inversion] często
    generuje sporą ilość hipotez postaci [a = b], które [subst] następnie
    "sprząta".

    W naszym przypadku hipoteza [H0 : x = y] została przepisana nie tylko
    w celu, dając [y = y], ale także w hipotezie [H], dając
    [H : Some y = Some y]. *)

(** **** Ćwiczenie (zero i jeden) *)

(** Udowodnij poniższe twierdzenie bez używania taktyki [inversion].
    Żeby było trudniej, nie pisz osobnej funkcji pomocniczej — zdefiniuj
    swoją funkcję bezpośrednio w miejscu, w którym chcesz jej użyć.  *)

Theorem zero_not_one : 0 <> 1.
(* begin hide *)
Proof.
  intro. change False with
  ((fun n : nat =>
  match n with
      | 0 => False
      | _ => True
  end) 0).
  rewrite H. trivial.
Qed.
(* end hide *)

(** Dwie opisane właściwości, choć pozornie niewinne, a nawet przydatne,
    mają bardzo istotne i daleko idące konsekwencje. Powoduję one na
    przykład, że nie istnieją typy ilorazowe. Dokładne znaczenie tego
    faktu omówimy później, zaś teraz musimy zadowolić się jedynie
    prostym przykładem w formie ćwiczenia. *)

Module rational.

Inductive rational : Set :=
    | mk_rational :
      forall (sign : bool) (numerator denominator : nat),
        denominator <> 0 -> rational.

Axiom rational_eq :
  forall (s s' : bool) (p p' q q' : nat)
    (H : q <> 0) (H' : q' <> 0), p * q' = p' * q ->
      mk_rational s p q H = mk_rational s' p' q' H'.

(** Typ [rational] ma reprezentować liczby wymierne. Znak jest typu
    [bool] — możemy interpretować, że [true] oznacza obecność znaku
    minus, a [false] brak znaku. Dwie liczby naturalne będą oznaczać
    kolejno licznik i mianownik, a na końcu żądamy jeszcze dowodu na
    to, że mianownik nie jest zerem.

    Oczywiście typ ten sam w sobie niewiele ma wspólnego z liczbami
    wymiernymi — jest to po prostu trójka elementów o typach [bool,
    nat, nat], z których ostatni nie jest zerem. Żeby rzeczywiście
    reprezentował liczby wymierne musimy zapewnić, że termy, które
    reprezentują te same wartości, są równe, np. 1/2 musi być równa
    2/4.

    W tym celu postulujemy aksjomat, który zapewni nam pożądane
    właściwości relacji równości. Komenda [Axiom] pozwala nam
    wymusić istnienie termu pożądanego typu i nadać mu nazwę,
    jednak jest szalenie niebezpieczna — jeżeli zapostulujemy
    aksjomat, który jest sprzeczny, jesteśmy zgubieni.

    W takiej sytuacji całe nasze dowodzenie idzie na marne, gdyż
    ze sprzecznego aksjomatu możemy wywnioskować [False], z
    [False] zaś możemy wywnioskować cokolwiek, o czym przekonaliśmy
    się w rozdziale pierwszym. Tak też jest w tym przypadku —
    aksjomat [rational_eq] jest sprzeczny, gdyż łamie zasadę
    injektywności konstruktorów. *)

(** **** Ćwiczenie (niedobry aksjomat) *)

(** Udowodnij, że aksjomat [rational_eq] jest sprzeczny. Wskazówka: znajdź
    dwie liczby wymierne, które są równe na mocy tego aksjomatu, ale które
    można rozróżnić za pomocą dopasowania do wzorca. *)

(* begin hide *)
Definition q_1_2 : rational :=
  mk_rational true 1 2 ltac:(inversion 1).

Definition q_2_4 : rational :=
  mk_rational true 2 4 ltac:(inversion 1).

Lemma q_1_2_eq_q_2_4 : q_1_2 = q_2_4.
Proof.
  apply rational_eq. reflexivity.
Qed.
(* end hide *)

Theorem rational_eq_inconsistent : False.
(* begin hide *)
Proof.
  change False with
  ((fun q : rational =>
  match q with
      | mk_rational true 1 2 _ => False
      | _ => True
  end) q_1_2).
  rewrite q_1_2_eq_q_2_4. cbn. trivial.
Qed.
(* end hide *)

End rational.

(** ** Listy, czyli parametry + rekursja *)

(** Połączenie funkcji zależnych, konstruktorów rekurencyjnych i
    polimorfizmu pozwala nam na opisywanie (prawie) dowolnych typów.
    Jednym z najbardziej podstawowych i najbardziej przydatnych
    narzędzi w programowaniu funkcyjnym (i w ogóle w życiu) są listy. *)

Module MyList.

Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

(** Lista przechowuje wartości pewnego ustalonego typu [A] (a więc nie
    można np. trzymać w jednej liście jednocześnie wartości typu [bool] i
    [nat]) i może mieć jedną z dwóch postaci: może być pusta (konstruktor
    [nil]) albo składać się z głowy i ogona (konstruktor [cons]). Głowa
    listy to wartość typu [A], zaś jej ogon to inna lista przechowująca
    wartości typu [A]. *)

Check nil.
(* ===> nil : forall A : Type, list A *)

Check cons.
(* ===> cons : forall A : Type, A -> list A -> list A *)

Arguments nil [A].
Arguments cons [A] _ _.

(** Jak już wspomnieliśmy, jeżeli typ induktywny ma argument (w naszym
    przypadku [A : Type]), to argument ten jest też pierwszym argumentem
    każdego z konstruktorów. W przypadku konstruktora [cons] podawanie
    argumentu [A] jest zbędne, gdyż kolejnym jego argumentem jest wartość
    tego typu. Wobec tego Coq może sam go wywnioskować, jeżeli mu każemy.

    Robimy to za pomocą komendy [Arguments konstruktor argumenty].
    Argumenty w nawiasach kwadratowych Coq będzie traktował jako domyślne,
    a te oznaczone podkreślnikiem trzeba będzie zawsze podawać ręcznie.
    Nazwa argumentu domyślnego musi być taka sama jak w definicji typu
    (w naszym przypadku w definicji [list] argument nazywał się [A],
    więc tak też musimy go nazwać używając komendy [Arguments]). Musimy
    wypisać wszystkie argumenty danego konstruktora — ich ilość możemy
    sprawdzić np. komendą [Check].

    Warto w tym momencie zauważyć, że Coq zna typy wszystkich termów,
    które zostały skonstruowane — gdyby tak nie było, nie mógłby
    sam uzupełniać argumentów domyślnych, a komenda [Check] nie mogłaby
    działać. *)

Notation "[]" := nil.
Infix "::" := (cons) (at level 60, right associativity ).

Check [].
(* ===> [[]] : list ?254 *)

Check 0 :: 1 :: 2 :: nil.
(* ===> [[0; 1; 2]] : list nat *)

(** Nazwy [nil] i [cons] są zdecydowanie za długie w porównaniu do swej
    częstości występowania. Dzięki powyższym eleganckim notacjom
    zaoszczędzimy sobie trochę pisania. Jeżeli jednak notacje utrudniają
    nam np. odczytanie celu, który mamy udowodnić, możemy je wyłączyć
    odznaczając w CoqIDE View > Display Notations.

    Wynik [[] : list ?254] (lub podobny) wyświetlony przez Coqa dla [[]]
    mówi nam, że [[]] jest listą pewnego ustalonego typu, ale Coq jeszcze
    nie wie, jakiego (bo ma za mało informacji, bo wywnioskować argument
    domyślny konstruktora [nil]). *)

Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=
    (cons x (cons y .. (cons z nil) .. )).

Check [5].
(* ===> [[5]] : list nat *)

Check [0; 1; 2; 3].
(* ===> [[0; 1; 2; 3]] : list nat *)

(** Zauważ, że system notacji Coqa jest bardzo silny — ostatnia notacja
    (ta zawierająca [..]) jest rekurencyjna. W innych językach tego typu
    notacje są zazwyczaj wbudowane w język i ograniczają się do podstawowych
    typów, takich jak listy właśnie. *)

Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
match l1 with
    | [] => l2
    | h :: t => h :: app t l2
end.

Notation "l1 ++ l2" := (app l1 l2).

(** Funkcje na listach możemy definiować analogicznie do funkcji na
    liczbach naturalnych. Zaczniemy od słowa kluczowego [Fixpoint],
    gdyż będziemy potrzebować rekurencji. Pierwszym argumentem naszej
    funkcji będzie typ [A] — musimy go wymienić, bo inaczej nie będziemy
    mogli mieć argumentów typu [list A] (pamiętaj, że samo [list]
    jest rodziną typów, a nie typem). Zapis [{A : Type}] oznacza,
    że Coq ma traktować [A] jako argument domyślny — jest to szybszy
    sposób, niż użycie komendy [Arguments].

    Nasz funkcja ma za zadanie dokleić na końcu (ang. append) pierwszej
    listy drugą listę. Definicja jest dość intuicyjna: doklejenie jakiejś
    listy na koniec listy pustej daje pierwszą listę, a doklejenie listy
    na koniec listy mającej głowę i ogon jest doklejeniem jej na koniec
    ogona. *)

Eval compute in [1; 2; 3] ++ [4; 5; 6].
(* ===> [[1; 2; 3; 4; 5; 6]] : list nat *)

(** Wynik działania naszej funkcji wygląda poprawnie, ale niech cię
    nie zwiodą ładne oczka — jedynym sposobem ustalenia poprawności
    naszego kodu jest udowodnienie, że posiada on pożądane przez
    nas właściwości. *)

Theorem app_nil_l :
  forall (A : Type) (l : list A), [] ++ l = l.
Proof.
  intros. cbn. reflexivity.
Qed.

Theorem app_nil_r :
  forall (A : Type) (l : list A), l ++ [] = l.
Proof.
  induction l as [| h t].
    cbn. reflexivity.
    cbn. rewrite IHt. reflexivity.
Qed.

(** Sposoby dowodzenia są analogiczne jak w przypadku liczb naturalnych.
    Pierwsze twierdzenie zachodzi na mocy samej definicji funkcji [app]
    i dowód sprowadza się do wykonania programu za pomocą taktyki [cbn].
    Drugie jest analogiczne do twierdzenia [plus_n_0], z tą różnicą, że
    w drugim celu zamiast [f_equal] posłużyliśmy się taktyką [rewrite].

    Zauważ też, że zmianie uległa postać wzorca przekazanego taktyce
    [induction] — teraz ma on postać [[| h t]], gdyż [list] ma 2
    konstruktory, z których pierwszy, [nil], nie bierze argumentów
    (argumenty domyślne nie są wymieniane we wzorcach), zaś drugi, [cons],
    ma dwa argumenty — głowę, tutaj nazwaną [h] (jako skrót od ang. head)
    oraz ogon, tutaj nazwany [t] (jako skrót od ang. tail). *)

(** **** Ćwiczenie (właściwości funkcji [app])*)

(** Udowodnij poniższe właściwości funkcji [app]. Wskazówka: może ci się
    przydać taktyka [specialize]. *)

Theorem app_assoc :
  forall (A : Type) (l1 l2 l3 : list A),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite <- IHt1. reflexivity.
Qed.
(* end hide *)

Theorem app_not_comm :
  ~ forall (A : Type) (l1 l2 : list A), l1 ++ l2 = l2 ++ l1.
(* begin hide *)
Proof.
  intro. specialize (H nat [0] [1]). cbn in H. inversion H.
Qed.
(* end hide *)

(** **** Ćwiczenie ([length]) *)

(** Zdefiniuj funkcję [length], która oblicza długość listy, a następnie
    udowodnij poprawność swojej implementacji. *)

(* begin hide *)
Fixpoint length {A : Type} (l : list A) : nat :=
match l with
    | [] => 0
    | h :: t => S (length t)
end.
(* end hide *)

Theorem length_nil :
  forall A : Type, length (@nil A) = 0.
(* begin hide *)
Proof.
  intro. cbn. reflexivity.
Qed.
(* end hide *)

Theorem length_cons :
  forall (A : Type) (h : A) (t : list A), length (h :: t) <> 0.
(* begin hide *)
Proof.
  cbn. intros. inversion 1.
Qed.
(* end hide *)

Theorem length_app :
  forall (A : Type) (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    f_equal. rewrite IHt1. reflexivity.
Qed.
(* end hide *)

End MyList.

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

SearchAbout nat.

(** [SearchAbout] wyświetla wszystkie obiekty, które mają jakiś związek
    z daną nazwą. Zazwyczaj wskaże on nam dużo więcej obiektów, niż zwykłe
    [Search], np. poza funkcjami, w których sygnaturze występuje [nat],
    pokazuje też twierdzenia dotyczące ich właściwości. *)

SearchPattern (_ + _ = _).

(** [SearchPattern] jako argument bierze wzorzec i wyświetla wszystkie
    obiekty, które zawierają podterm pasujący do danego wzorca. W naszym
    przypadku pokazały się twierdzenia, w których występuje podterm
    mający po lewej dodawanie, a po prawej cokolwiek.

    Dokładny opis wszystkich komend znajdziesz tutaj:
    https://coq.inria.fr/refman/coq-cmdindex.html *)

(** ** Ważne typy induktywne *)

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

Theorem create_unique :
  forall (A : Type) (f : Empty_set -> A),
    (forall x : Empty_set, create x = f x).
(* begin hide *)
Proof.
  intros. destruct x.
Qed.
(* end hide *)

(** **** Ćwiczenie ([no_fun_from_nonempty_to_empty]) *)

(** Pokaż, że nie istnieją funkcje z typu niepustego w pusty. *)

Theorem no_fun_from_nonempty_to_empty :
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

Theorem delete_unique :
  forall (A : Type) (f : A -> unit),
    (forall x : A, delete x = f x).
(* begin hide *)
Proof.
  intros. destruct (delete x). destruct (f x). trivial.
Qed.
(* end hide *)

(** *** Produkt *)

Inductive prod (A B : Type) : Type :=
    | pair : A -> B -> prod A B.

Arguments pair [A] [B] _ _.

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

Theorem proj_spec :
  forall (A B : Type) (p : prod A B),
    p = pair (fst p) (snd p).
(* begin hide *)
Proof.
  destruct p. cbn. trivial.
Qed.
(* end hide *)

(** *** Suma *)

Inductive sum (A B : Type) : Type :=
    | inl : A -> sum A B
    | inr : B -> sum A B.

Arguments inl [A] [B] _.
Arguments inr [A] [B] _.

(** Suma [A] i [B] to typ, którego termy są albo termami typu [A],
    zawiniętymi w konstruktor [inl], albo termami typu [B], zawiniętymi
    w konstruktor [inr]. Suma, w przeciwieństwie do produktu, zdecydowanie
    nie ma projekcji. *)

(** **** Ćwiczenie (sumy bez projekcji) *)

(** Pokaż, że suma nie ma projekcji. *)

Theorem sum_no_fst :
  forall (proj : forall A B : Type, sum A B -> A), False.
(* begin hide *)
Proof.
  intros. apply proj with nat. apply inr. exact 0.
Qed.
(* end hide *)

Theorem sum_no_snd :
  forall (proj : forall A B : Type, sum A B -> B), False.
(* begin hide *)
Proof.
  intros. apply proj with nat. apply inl. exact 0.
Qed.
(* end hide *)

End ImportantTypes.

(** ** Kiedy typ induktywny jest pusty? *)

(** Typy puste to typy, które nie mają żadnych elementów. Z jednym z nich
    już się spotkaliśmy — był to [Empty_set], który jest pusty, gdyż nie
    ma żadnych konstruktorów. Czy wszystkie typy puste to typy, które
    nie mają konstruktorów? *)

Inductive Empty : Type :=
    | c : Empty_set -> Empty.

Theorem Empty_is_empty :
  forall empty : Empty, False.
Proof.
  intro. destruct empty. destruct e.
Qed.

(** Okazuje się, że nie. Pustość i niepustość jest kwestią czegoś więcej,
    niż tylko ilości konstruktorów. Powyższy przykład pokazuje dobitnie,
    że ważne są też typy argumentów konstruktorów. Jeżeli typ któregoś z
    argumentów konstruktora jest pusty, to nie można użyć go do zrobienia
    żadnego termu. Jeżeli każdy konstruktor typu [T] ma argument, którego
    typ jest pusty, to sam typ [T] również jest pusty.

    Wobec powyższych rozważań możemy sformułować następujące kryterium:
    typ [T] jest niepusty, jeżeli ma co najmniej jeden konstruktor, który
    nie bierze argumentów, których typy są puste. Jakkolwiek jest to bardzo
    dobre kryterium, to jednak nie rozwiewa ono niestety wszystkich możliwych
    wątpliwości. *)

Inductive InfiniteList (A : Type) : Type :=
    | InfiniteCons : A -> InfiniteList A -> InfiniteList A.

(** Czy typ [InfiniteList A] jest niepusty? Skorzystajmy z naszego kryterium:
    ma on jeden konstruktor biorący dwa argumenty, jeden typu [A] oraz drugi
    typu [InfiniteList A]. W zależności od tego, czym jest [A], może on być
    pusty lub nie — przyjmijmy, że [A] jest niepusty. W przypadku drugiego
    argumentu napotykamy jednak na problem: to, czy [InfiniteList A] jest
    niepusty zależy od tego, czy typ argumentu jego konstruktora, również
    [InfiniteList A], jest niepusty. Sytuacja jest więc beznadziejna — mamy
    błędne koło.

    Powyższy przykład pokazuje, że nasze kryterium może nie poradzić sobie
    z rekurencją. Jak zatem rozstrzygnąć, czy typ ten jest niepusty? Musimy
    odwołać się bezpośrednio do definicji i zastanowić się, czy możliwe jest
    skonstruowanie jakichś jego termów. W tym celu przypomnijmy, czym są typy
    induktywne:
    - Typ induktywny to rodzaj planu, który pokazuje, w jaki sposób można
      konstruować jego termy, które są drzewami.
    - Konstruktory to węzły drzewa. Ich nazwy oraz ilość i typy argumentów
      nadają drzewu kształt i znaczenie.
    - Konstruktory nierekurencyjne to liście drzewa.
    - Konstruktory rekurencyjne to węzły wewnętrzne drzewa. *)

(** Kluczowym faktem jest rozmiar termów: o ile rozgałęzienia mogą być
    potencjalnie nieskończone, o tyle wszystkie gałęzie muszą mieć
    skończoną długość. Pociąga to za sobą bardzo istotny fakt: typy
    mające jedynie konstruktory rekurencyjne są puste, gdyż bez użycia
    konstruktorów nierekurencyjnych możemy konstruować jedynie drzewa
    nieskończone (i to tylko przy nierealnym założeniu, że możliwe jest
    zakończenie konstrukcji liczącej sobie nieskończoność kroków). *)

Theorem InfiniteList_is_empty :
  forall A : Type, InfiniteList A -> False.
Proof.
  intros A l. induction l as [h t]. exact IHt.
Qed.

(** Pokazanie, że [InfiniteList A] jest pusty, jest bardzo proste —
    wystarczy posłużyć się indukcją. Indukcja po [l : InfiniteList A]
    daje nam hipotezę indukcyjną [IHt : False], której możemy użyć,
    aby natychmiast zakończyć dowód.

    Zaraz, co właściwie się stało? Dlaczego dostaliśmy zupełnie za darmo
    hipotezę [IHt], która jest szukanym przez nas dowodem? W ten właśnie
    sposób przeprowadza się dowody indukcyjne: zakładamy, że hipoteza [P]
    zachodzi dla termu [t : InfiniteList A], a następnie musimy pokazać,
    że [P] zachodzi także dla termu [InfiniteCons h t]. Zazwyczaj [P] jest
    predykatem i wykonanie kroku indukcyjnego jest nietrywialne, w naszym
    przypadku jest jednak inaczej — postać [P] jest taka sama dla [t] oraz
    dla [InfiniteCons h t] i jest nią [False].

    Czy ten konfundujący fakt nie oznacza jednak, że [list A], czyli typ
    zwykłych list, również jest pusty? Spróbujmy pokazać, że tak jest. *)

Theorem list_empty :
  forall (A : Type), list A -> False.
Proof.
  intros A l. induction l as [| h t].
    Focus 2. exact IHt.
Abort.

(** Pokazanie, że typ [list A] jest pusty, jest rzecz jasna niemożliwe,
    gdyż typ ten zdecydowanie pusty nie jest — w jego definicji stoi
    jak byk napisane, że dla dowolnego typu [A] istnieje lista termów
    typu [A]. Jest nią oczywiście [@nil A].

    Przyjrzyjmy się naszej próbie dowodu. Próbujemy posłużyć się indukcją
    w ten sam sposób co poprzednio. Taktyka [induction] generuje nam dwa
    podcele, gdyż [list] ma dwa konstruktory — pierwszy podcel dla [nil],
    a drugi dla [cons]. Komenda [Focus] pozwala nam przełączyć się do
    wybranego celu, w tym przypadku celu nr 2, czyli gdy [l] jest postaci
    [cons h t].

    Sprawa wygląda identycznie jak poprzednio — za darmo dostajemy hipotezę
    [IHt : False], której używamy do natychmiastowego rozwiązania naszego
    celu. Tym, co stanowi przeszkodę nie do pokonania, jest cel nr 1, czyli
    gdy [l] zrobiono za pomocą konstruktora [nil]. Ten konstruktor nie jest
    rekurencyjny, więc nie dostajemy żadnej hipotezy indukcyjnej. Lista [l]
    zostaje w każdym miejscu, w którym występuje, zastąpiona przez [[]], a
    ponieważ nie występuje nigdzie — znika. Musimy teraz udowodnić fałsz
    wiedząc jedynie, że [A] jest typem, co jest niemożliwe. *)

(** * Induktywne zdania i predykaty *)

(** Wiemy, że słowo kluczowe [Inductive] pozwala nam definiować nowe typy
    (a nawet rodziny typów, jak w przypadku [option]). Wiemy też, że zdania
    są typami. Wobec tego nie powinno nas dziwić, że induktywnie możemy
    definiować także zdania, spójniki logiczne, predykaty oraz relacje. *)

(** ** Induktywne zdania *)

Inductive false_prop : Prop := .

Inductive true_prop : Prop :=
    | obvious_proof : true_prop
    | tricky_proof : true_prop
    | weird_proof : true_prop
    | magical_proof : true_prop.

(** Induktywne definicje zdań nie są zbyt ciekawe, gdyż pozwalają definiować
    jedynie zdania fałszywe (zero konstruktorów) lub prawdziwe (jeden lub
    więcej konstruktorów). Pierwsze z naszych zdań jest fałszywe (a więc
    rónoważne z [False]), drugie zaś jest prawdziwe (czyli równoważne z [True])
    i to na cztery sposoby! *)

(** **** Ćwiczenie (induktywne zdania) *)

Theorem false_prop_iff_False : false_prop <-> False.
(* begin hide *)
Proof.
  split; inversion 1.
Qed.
(* end hide *)

Theorem true_prop_iff_True : true_prop <-> True.
(* begin hide *)
Proof.
  split; inversion 1; constructor.
Qed.
(* end hide *)

(** ** Induktywne predykaty *)

(** Przypomnijmy, że predykaty to funkcje, których przeciwdziedziną jest
    sort [Prop], czyli funkcje zwracające zdania logiczne. Predykat
    [P : A -> Prop] można rozumieć jako właściwość, którą mogą posiadać
    termy typu [A], zaś dla konkretnego [x : A] zapis [P x] interpretować
    można "term [x] posiada właściwóść [P]".

    O ile istnieją tylko dwa rodzaje induktwynych zdań (prawdziwe i fałszywe),
    o tyle induktywnie zdefiniowane predykaty są dużo bardziej ciekawe i
    użyteczne, gdyż dla jednych termów mogą być prawdziwe, a dla innych nie. *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

(** Predykat [even] ma oznaczać właściwość "bycia liczbą parzystą". Jego
    definicję można zinterpretować tak:
    - "[0] jest liczbą przystą"
    - "jeżeli [n] jest liczbą parzystą, to [n + 2] również jest
       liczbą parzystą" *)

(** Jak widać, induktywna definicja parzystości różni się od powszechnie
    używanej definicji, która głosi, że "liczba jest parzysta, gdy
    dzieli się bez reszty przez 2". Różnica jest natury filozoficznej:
    definicja induktywna mówi, jak konstruować liczby parzyste, podczas
    gdy druga, "klasyczna" definicja mówi, jak sprawdzić, czy liczba
    jest parzysta.

    Przez wzgląd na swą konstruktywność, w Coqu induktywne definicje
    predykatów czy relacji są często dużo bardziej użyteczne od tych
    nieinduktywnych, choć nie wszystko można zdefiniować induktywnie. *)

Theorem zero_is_even : even 0.
Proof.
  apply even0.
Qed.

(** Jak możemy udowodnić, że [0] jest liczbą parzystą? Posłuży nam
    do tego konstruktor [even0], który wprost głosi, że [even 0].
    Nie daj się zwieść: [even0], pisane bez spacji, jest nazwą
    konstruktora, podczas gdy [even 0], ze spacją, jest zdaniem
    (czyli termem typu [Prop]), które można interpretować jako
    "[0] jest liczbą parzystą". *)

Theorem two_is_even : even 2.
Proof.
  apply evenSS. apply even0.
Qed.

(** Jak możemy udowodnić, że [2] jest parzyste? Konstruktor [even0]
    nam nie pomoże, gdyż jego postać ([even 0]) nie pasuje do postaci
    naszego twierdzenia ([even 2]). Pozostaje nam jednak konstruktor
    [evenSS].

    Jeżeli przypomnimy sobie, że [2] to tak naprawdę [S (S 0)],
    natychmiast dostrzeżemy, że jego konkluzja pasuje do postaci naszego
    twierdzenia. Możemy go więc zaaplikować (pamiętaj, że konstruktory są
    jak zwykłe funkcje, tylko że niczego nie obliczają — nadają one typom
    ich kształty). Teraz wystarczy pokazać, że [even 0] zachodzi, co już
    potrafimy. *)

Theorem four_is_even : even 4.
Proof.
  constructor. constructor. constructor.
Qed.

(** Jak pokazać, że [4] jest parzyste? Tą samą metodą, która pokazaliśmy,
    że [2] jest parzyste. [4] to [S (S (S (S 0)))], więc możemy użyć
    konstruktora [evenSS]. Zamiast jednak pisać [apply evenSS], możemy
    użyć taktyki [constructor]. Taktyka ta działa na celach, w których
    chcemy skonstruować wartość jakiegoś typu induktywnego (a więc także
    gdy dowodzimy twierdzeń o induktywnych predykatach). Szuka ona
    konstruktora, który może zaaplikować na celu, i jeżeli znajdzie, to
    aplikuje go, a gdy nie — zawodzi.

    W naszym przypadku pierwsze dwa użycia [constructor] aplikują
    konstruktor [evenSS], a trzecie — konstruktor [even0]. *)

Theorem the_answer_is_even : even 42.
Proof.
  repeat constructor.
Qed.

(** A co, gdy chcemy pokazać, że [42] jest parzyste? Czy musimy 22 razy
    napisać [constructor]? Na szczęście nie — wystarczy posłużyć się
    kombinatorem [repeat] (jeżeli nie pamiętasz, jak działa, zajrzyj do
    rozdziału 1). *)

Theorem one_not_even_failed : ~ even 1.
Proof.
  unfold not. intro. destruct H.
Abort.

Theorem one_not_even : ~ even 1.
Proof.
  unfold not. intro. inversion H.
Qed.

(** A jak pokazać, że [1] nie jest parzyste? Mając w kontekście dowód
    na to, że [1] jest parzyste ([H : even 1]), możemy zastantowić się,
    w jaki sposób dowód ten został zrobiony. Nie mógł zostać zrobiony
    konstruktorem [even0], gdyż ten dowodzi, że [0] jest parzyste, a
    przecież przekonaliśmy się już, że [0] to nie [1]. Nie mógł też
    zostać zrobiony konstruktorem [evenSS], gdyż ten ma w konkluzji
    [even (S (S n))], podczas gdy [1] jest postaci [S 0] — nie pasuje
    on do konkluzji [evenSS], gdyż "ma za mało [S]ów".

    Nasze rozumowanie prowadzi do wniosku, że za pomocą [even0] i [evenSS],
    które są jedynymi konstruktorami [even], nie można skonstruować [even 1],
    więc [1] nie może być parzyste. Na podstawie wcześniejszych doświadczeń
    mogłoby się nam wydawać, że [destruct] załatwi sprawę, jednak tak nie
    jest — taktyka ta jest w tym przypadku upośledzona i nie potrafi nam
    pomóc. Zamiast tego możemy się posłużyć taktyką [inversion]. Działa ona
    dokładnie w sposób opisany w poprzednim akapicie. *)

Theorem three_not_even : ~ even 3.
Proof.
  intro. inversion H. inversion H1.
Qed.

(** Jak pokazać, że [3] nie jest parzyste? Pomoże nam w tym, jak poprzednio,
    inwersja. Tym razem jednak nie załatwia ona sprawy od razu. Jeżeli
    zastanowimy się, jak można pokazać [even 3], to dojdziemy do wniosku,
    że można to zrobić konstruktorem [evenSS], gdyż [3] to tak naprawdę
    [S (S 1)]. To właśnie robi pierwsza inwersja: mówi nam, że [H : even 3]
    można uzyskać z zaaplikowania [evenSS] do [1], jeżeli tylko mamy dowód
    [H1 : even 1] na to, że [1] jest parzyste. Jak pokazać, że [1] nie
    jest parzyste, już wiemy. *)

(** **** Ćwiczenie (odd) *)

(** Zdefiniuj induktywny predykat [odd], który ma oznaczać "bycie liczbą
    nieparzystą" i udowodnij, że zachowuje się on jak należy. *)

(* begin hide *)
Inductive odd : nat -> Prop :=
    | odd1 : odd 1
    | oddSS : forall n : nat, odd n -> odd (S (S n)).
(* end hide *)

Theorem one_odd : odd 1.
(* begin hide *)
Proof.
  constructor.
Qed.
(* end hide *)

Theorem seven_odd : odd 7.
(* begin hide *)
Proof.
  repeat constructor.
Qed.
(* end hide *)

Theorem zero_not_odd : ~ odd 0.
(* begin hide *)
Proof.
  inversion 1.
Qed.
(* end hide *)

Theorem two_not_odd : ~ odd 2.
(* begin hide *)
Proof.
  inversion 1. inversion H1.
Qed.
(* end hide *)

(** ** Indukcja po dowodzie *)

Require Import Arith.

(** Biblioteka [Arith] zawiera różne definicje i twierdzenia dotyczące
    arytmetyki. Będzie nam ona potrzebna w tym podrozdziale.

    Jak udowodnić, że suma liczb parzystych jest parzysta? Być może
    właśnie pomyślałeś o indukcji. Spróbujmy zatem: *)

Theorem even_sum_failed1 :
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction n as [| n']; cbn; intros.
    trivial.
    induction m as [| m']; rewrite plus_comm; cbn; intros.
      assumption.
      constructor. rewrite plus_comm. apply IHn'.
Abort.

(** Próbując jednak indukcji po [n], a potem po [m], docieramy do martwego
    punktu. Musimy udowodnić [even n'], podczas gdy zachodzi [even (S n')]
    (czyli [even n'] jest fałszywe). Wynika to z faktu, że przy indukcji
    [n] zwiększa się o 1 ([P n -> P (S n)]), podczas gdy w definicji
    [even] mamy konstruktor głoszący, że ([even n -> even (S (S n))]).

    Być może w drugiej kolejności pomyślałeś o taktyce [destruct]: jeżeli
    sprawdzimy, w jaki sposób udowodniono [even n], to przy okazji dowiemy
    się też, że [n] może być jedynie postaci [0] lub [S (S n')]. Dzięki
    temu powinniśmy uniknąć problemu z poprzedniej próby. *)

Theorem even_sum_failed2 :
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm. destruct Hn, Hm; cbn.
    constructor.
    constructor. assumption.
    rewrite plus_comm. cbn. constructor. assumption.
    rewrite plus_comm. cbn. do 2 constructor.
Abort.

(** Niestety, taktyka [destruct] okazała się za słaba. Predykat [even] jest
    induktywny, a zatem bez indukcji się nie obędzie. Rozwiązaniem naszych
    problemów nie będzie jednak indukcja po [n] lub [m], lecz po dowodzie na
    to, że [n] jest parzyste. *)

Theorem even_sum :
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [| n' Hn'].
    cbn. assumption.
    cbn. constructor. assumption.
Qed.

(** Indukcja po dowodzie działa dokładnie tak samo, jak indukcja, z którą
    zetknęliśmy się dotychczas. Różni się od niej jedynie tym, że aż do
    teraz robiliśmy indukcję jedynie po termach, których typy były sortu
    [Set] lub [Type]. Indukcja po dowodzie to indukcja po termie, którego
    typ jest sortu [Prop].

    W naszym przypadku użycie [induction Hn] ma następujący skutek:
    - W pierwszym przypadku [Hn] to po prostu konstruktor [even0], a 
      zatem [n] jest zerem.
    - W drugim przypadku [Hn] to [evenSS n' Hn'], gdzie [n] jest postaci
      [S (S n')], zaś [Hn'] jest dowodem na to, że [n'] jest parzyste. *)

(** *** Taktyki [replace] i [assert]. *)

(** Przy następnych ćwiczeniach mogą przydać ci się taktyki [replace]
    oraz [assert]. *)

Theorem stupid_example_replace :
  forall n : nat, n + 0 = n.
Proof.
  intro. replace (n + 0) with (0 + n).
    trivial.
    apply plus_comm.
Qed.

(** Taktyka [replace t with t'] pozwala nam zastąpić w celu każde
    wystąpienie termu [t] termem [t']. Jeżeli [t] nie ma w celu, to
    taktyka zawodzi, a w przeciwnym wypadku dodaje nam jeden podcel,
    w którym musimy udowodnić, że [t = t']. Można też zastosować ją
    w hipotezie, pisząc [replace t with t' in H]. *)

Theorem stupid_example_assert :
  forall n : nat, n + 0 + 0 = n.
Proof.
  intro. assert (H : n + 0 = n).
    apply plus_0_r.
    do 2 rewrite H. trivial.
Qed.

(** Taktyka [assert (x : A)] dodaje do kontekstu term [x] typu [A] oraz
    generuje jeden dodatkowy podcel, w którym musimy skonstruować [x].
    Zawodzi ona, jeżeli nazwa [x] jest już zajęta. *)

(** **** Ćwiczenie (właściwości [even]) *)

(** Udowodnij poniższe twierdzenia. Zanim zaczniesz, zastanów się, po czym
    należy przeprowadzić indukcję: po wartości, czy po dowodzie? *)

Theorem double_is_even :
  forall n : nat, even (2 * n).
(* begin hide *)
Proof.
  induction n as [| n']; cbn in *.
    constructor.
    rewrite <- plus_n_O in *. rewrite plus_comm. cbn.
      constructor. assumption.
Qed.
(* end hide *)

Theorem even_is_double :
  forall n : nat, even n -> exists k : nat, n = 2 * k.
(* begin hide *)
Proof.
  induction 1.
    exists 0. trivial.
    destruct IHeven. exists (S x). cbn in *. rewrite <- plus_n_O in *.
      rewrite plus_comm. cbn. do 2 f_equal. assumption.
Qed.
(* end hide *)

(** ** Definicje stałych i spójników logicznych *)

(** W rozdziale pierwszym dowiedzieliśmy się, że produkt zależny (typ,
    którego termami są funkcje zależne), a więc i implikacja, jest
    typem podstawowym/wbudowanym oraz że negacja jest zdefiniowana jako
    implikowanie fałszu. Teraz, gdy wiemy już co nieco o typach induktywnych,
    nadszedł czas by zapoznać się z definicjami spójników logicznych (i nie
    tylko). *)

Module MyConnectives.

(** *** Prawda i fałsz *)

Inductive False : Prop := .

(** Fałsz nie ma żadnych konstruktorów, a zatem nie może zostać w żaden
    sposób skonstruowany, czyli udowodniony. Jego definicja jest bliźniaczo
    podobna do czegoś, co już kiedyś widzieliśmy — tym czymś był [Empty_set],
    czyli typ pusty. Nie jest to wcale przypadek. Natknęliśmy się (znowu) na
    przykład korespondencji Curry'ego-Howarda.

    Przypomnijmy, że głosi ona (w sporym uproszczeniu), iż sorty [Prop]
    i [Set]/[Type] są do siebie bardzo podobne. Jednym z tych podobieństw
    było to, że dowody implikacji są funkcjami. Kolejnym jest fakt, że
    [False] jest odpowiednikiem [Empty_set], od którego różni się tym, że
    żyje w [Prop], a nie w [Set].

    Ta definicja rzuca też trochę światła na sposób wnioskowania "ex falso
    quodlibet" (z fałszu wynika wszystko), który poznaliśmy w rozdziale
    pierwszym.

    Użycie taktyki [destruct] lub [inversion] na termie dowolnego typu
    induktywnego to sprawdzenie, którym konstruktorem term ten został
    zrobiony — generują one dokładnie tyle podcelów, ile jest możliwych
    konstruktorów. Użycie ich na termie typu [False] generuje zero
    podcelów, co ma efekt natychmiastowego zakończenia dowodu. Dzięki
    temu mając dowód [False] możemy udowodnić cokolwiek. *)

Inductive True : Prop :=
    | I : True.

(** [True] jest odpowiednikiem [unit], od którego różni się tym, że żyje
    w [Prop], a nie w [Set]. Ma dokładnie jeden dowód, który w Coqu
    nazwano, z zupełnie nieznanych powodów (zapewne dla hecy), [I]. *)

(** *** Koniunkcja i dysjunkcja *)

Inductive and (P Q : Prop) : Prop :=
    | conj : P -> Q -> and P Q.

(** Dowód koniunkcji zdań [P] i [Q] to para dowodów: pierwszy element
    pary jest dowodem [P], zaś drugi dowodem [Q]. Koniunkcja jest
    odpowiednkiem produktu, od którego różni się tym, że żyje w [Prop],
    a nie w [Type]. *)

Inductive or (P Q : Prop) : Prop :=
    | or_introl : P -> or P Q
    | or_intror : Q -> or P Q.

(** Dowód dysjunkcji zdań [P] i [Q] to dowód [P] albo dowód [Q] wraz ze
    wskazaniem, którego zdania jest to dowód. Dysjunkcja jest odpowiednikiem
    sumy, od której różni się tym, że żyje w [Prop], a nie w [Type]. *)

End MyConnectives.

(** ** Równość *)

Module MyEq.

(** Czym jest równość? To pytanie stawiało sobie wielu filozofów,
    szczególnie politycznych, zaś wyjątkowo rzadko nad tą sprawą
    zastanawiali się sami bojownicy o równość, tak jakby wszystko
    dokładnie wiedzieli. Odpowiedź na nie jest jednym z największych
    osiągnięć matematyki w dziejach: równość to jeden z typów induktywnych,
    które możemy zdefiniować w Coqu. *)

Inductive eq {A : Type} (x : A) : A -> Prop :=
    | eq_refl : eq x x.

(** Spróbujmy przeczytać tę definicję: dla danego typu [A] oraz termu
    [x] tego typu, [eq x] jest predykatem, który ma jeden konstruktor
    głoszący, że [eq x x] zachodzi. Choć definicja taka brzmi obco i
    dziwacznie, ma ona swoje uzasadnienie (które niestety poznamy
    dopiero w przyszłości). *)

Theorem eq_refl_trivial : eq 42 42.
Proof.
  apply eq_refl.
Qed.

(** Poznane przez nas dotychczas taktyki potrafiące udowadniać proste
    równości, jak [trivial] czy [reflexivity] działają w ten sposób,
    że po prostu aplikują na celu [eq_refl]. Nazwa [eq_refl] to skrót
    od ang. "reflexivity of equality", czyli "zwrotność równości" —
    jest to najważniejsza cecha równości, która oznacza, że każdy term
    jest równy samemu sobie. *)

Theorem eq_refl_nontrivial : eq (1 + 41) 42.
Proof.
  constructor.
Qed.

(** Mogłoby wydawać się, że zwrotność nie wystarcza do udowadniania
    "nietrywialnych" równości pokroju [1 + 41 = 42], jednak tak nie jest.
    Dlaczego [eq_refl] odnosi na tym celu sukces skoro [1 + 41] oraz [42]
    zdecydowanie różnią się postacią? Odpowiedź jest prosta: typ [eq] w
    rzeczywistości owija jedynie równość pierwotną, wbudowaną w samo jądro
    Coqa, którą jest konwertowalność. *)

Theorem eq_refl_alpha :
  forall A : Type, eq (fun x : A => x) (fun y : A => y).
Proof.
  intro. change (fun x : A => x) with (fun y : A => y).
  apply eq_refl.
Qed.

Theorem eq_refl_beta :
  forall m : nat, eq ((fun n : nat => n + n) m) (m + m).
Proof.
  intro. cbn. apply eq_refl.
Qed.

Definition ultimate_answer : nat := 42.

Theorem eq_refl_delta : eq ultimate_answer 42.
Proof.
  unfold ultimate_answer. apply eq_refl.
Qed.

Theorem eq_refl_iota :
  eq 42 (match 0 with | 0 => 42 | _ => 13 end).
Proof.
  cbn. apply eq_refl.
Qed.

Theorem eq_refl_zeta :
  let n := 42 in eq n 42.
Proof.
  reflexivity.
Qed.

(** Przypomnijmy, co już wiemy o redukcjach:
    - konwersja alfa pozwala nam zmienić nazwę zmiennej związanej w
      funkcji anonimowej nową, jeżeli ta nie jest jeszcze używana.
      W naszym przykładzie zamieniamy [x] w [fun x : A => x] na [y],
      otrzymując [fun y : A => y] — konwersja jest legalna. Jednak
      w funkcji [fun x y : nat => x + x] nie możemy użyć konwersji
      alfa, żeby zmienić nazwę [x] na [y], bo [y] jest już używana
      (tak nazywa się drugi argument).
    - Redukcja beta zastępuje argumentem każde wystąpienie zmiennej
      związanej w funkcji anonimowej. W naszym przypadku redukcja
      ta zamienia [(fun n : nat => n + n) m] na [m + m] — w miejsce
      [n] wstawiamy [m].
    - Redukcja delta odwija definicje. W naszym przypadku zdefiniowaliśmy,
      że [ultimate_answer] oznacza [42], więc redukcja delta w miejsce
      [ultimate_answer] wstawia [42].
    - Redukcja jota wykonuje dopasowanie do wzorca. W naszym przypadku [0]
      jest termem, który postać jest znana (został on skonstruowany
      konstruktorem [0]) i który pasuje do wzorca [| 0 => 42], a zatem
      redukcja jota zamienia całe wyrażenie od [match] aż do [end]
      na [42].
    - Redukcja zeta odwija lokalną definicję poczynioną za pomocą [let]a *)

(** Termy [x] i [y] są konwertowalne, gdy za pomocą serii konwersji alfa
    oraz redukcji beta, delta, jota i zeta oba redukują się do tego samego
    termu (który dzięki silnej normalizacji istnieje i jest w postaci
    kanonicznej).

    Uważny czytelnik zada sobie w tym momencie pytanie: skoro równość to
    konwertowalność, to jakim cudem równe są termy [0 + n] oraz [n + 0],
    gdzie [n] jest zmienną, które przecież nie są konwertowalne?

    Trzeba tutaj dokonać pewnego doprecyzowania. Termy [0 + n] i [n + 0] są
    konwertowalne dla każdego konkretnego [n], np. [0 + 42] i [42 + 0] są
    konwertowalne. Konwertowalne nie są natomiast, gdy [n] jest zmienną -
    jest tak dlatego, że nie możemy wykonać redukcji iota, bo nie wiemy, czy
    [n] jest zerem czy następnikiem.

    Odpowiedzią na pytanie są reguły eliminacji, głównie dla typów
    induktywnych. Reguły te mają konkluzje postaci [forall x : I, P x],
    więc w szczególności możemy użyć ich dla [P x := x = y] dla jakiegoś
    [y : A]. Dzięki nim przeprowadzaliśmy już wielokrotnie mniej więcej
    takie rozumowania: [n] jest wprawdzie nie wiadomo czym, ale przez
    indukcję może to być albo [0], albo [S n'], gdzie dla [n'] zachodzi
    odpowiednia hipoteza indukcyjna. *)

End MyEq.

(** ** Indukcja wzajemna *)

(** Jest jeszcze jeden rodzaj indukcji, o którym dotychczas nie mówiliśmy:
    indukcja wzajemna (ang. mutual induction). Bez zbędnego teoretyzowania
    zbadajmy sprawę na przykładzie klasyków polskiej literatury: *)

(** _Smok to wysuszony zmok_ *)

(** _Zmok to zmoczony smok_ *)

(** Stanisław Lem *)

(** Idea stojąca za indukcją wzajemną jest prosta: chcemy przez indukcję
    zdefiniować jednocześnie dwa obiekty, które mogą się nawzajem do siebie
    odwoływać.

    W owym definiowaniu nie mamy rzecz jasna pełnej swobody — obowiązują te
    same kryteria co w przypadku zwykłych, "pojedynczych" definicji typów
    induktywnych. Wobec tego zauważyć należy, że definicja słowa "smok"
    podana przez Lema jest według Coqowych standardów nieakceptowalna, gdyż
    jeżeli w definicji _smoka_ rozwiniemy definicję _zmoka_, to otrzymamy

    _Smok ty wysuszony zmoczony smok_ *)

(** Widać gołym okiem, iż próba zredukowania (czyli obliczenia) obiektu
    _smok_ nigdy się nie skończy. Jak już wiemy, niekończące się obliczenia
    w logice odpowiadają sprzeczności, a zatem ani _smoki_, ani _zmoki_ w
    Coqowym świecie nie istnieją.

    Nie znaczy to bynajmniej, że wszystkie definicje przez indukcję
    wzajemną są w Coqu niepoprawne, choć należy przyznać, że są dość
    rzadko używane. Czas jednak abyśmy ujrzeli pierwszy prawdziwy przkład
    indukcji wzajemnej. *)

Module MutInd.

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenS : forall n : nat, odd n -> even (S n)

with odd : nat -> Prop :=
    | oddS : forall n : nat, even n -> odd (S n).

(** Aby zrozumieć tę definicję, zestawmy ją z naszą definicją parzystości
    z sekcji _Induktywne predykaty_.

    Zdefiniowaliśmy tam predykat bycia liczbą parzystą tak:
    - [0] jest parzyste
    - jeżeli [n] jest parzyste, to [n + 2] też jest parzyste *)

(** Tym razem jednak nie definiujemy jedynie predykatu "jest liczbą parzystą".
    Definiujemy jednocześnie dwa predykaty: "jest liczbą parzystą" oraz
    "jest liczbą nieparzystą", które odwołują się do siebi nawzajm. Definicja
    brzmi tak:
    - [0] jest parzyste
    - jeżeli [n] jest nieparzyste, to [n + 1] jest parzyste
    - jeżeli [n] jest parzyste, to [n + 1] jest nieparzyste *)

(** Czy definicja taka rzeczywiście ma sens? Sprawdźmy to:
    - [0] jest parzyste na mocy definicji
    - jeżeli [0] jest parzyste (a jest), to [1] jest nieparzyste
    - jeżeli [1] jest nieparzyste (a jest), to [2] jest parzyste
    - i tak dalej, ad infinitum
*)

(** Jak widać, za pomocą naszej wzajemnie induktywnej definicji [even] można
    wygenerować wszystkie liczby parzyste (i tylko je), tak więc nowe [even]
    jest równoważne staremu [even] z sekcji _Induktywne predykaty_. Podobnie
    [odd] może wygenerować wszystkie liczby nieparzyste i tylko je. *)

(** **** Ćwiczenie (upewniające) *)

(** Upewnij się, że powyższy akapit nie kłamie. *)

Lemma even_0 : even 0.
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

Lemma odd_1 : odd 1.
(* begin hide *)
Proof. repeat constructor. Qed.
(* end hide *)

Lemma even_2 : even 2.
(* begin hide *)
Proof. repeat constructor. Qed.
(* end hide *)

Lemma even_42 : even 42.
(* begin hide *)
Proof. repeat constructor. Qed.
(* end hide *)

Lemma not_odd_0 : ~ odd 0.
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma not_even_1 : ~ even 1.
(* begin hide *)
Proof. inversion 1. inversion H1. Qed.
(* end hide *)

(** **** Ćwiczenie (właściwości [even] i [odd]) *)

(** Udowodnij podstawowe właściwości [even] i [odd]. *)

Lemma even_SS :
  forall n : nat, even n -> even (S (S n)).
(* begin hide *)
Proof.
  induction n; intro; do 2 constructor.
    constructor.
    assumption.
Qed.
(* end hide *)

Lemma odd_SS : 
  forall n : nat, odd n -> odd (S (S n)).
(* begin hide *)
Proof.
  induction n; intro; do 2 constructor; auto.
Qed.
(* end hide *)

Lemma even_plus :
  forall n m : nat, even n -> even m -> even (n + m).
(* begin hide *)
Abort.
(* end hide *)

(** Jeśli poległeś przy ostatnim zadaniu — nie przejmuj się. Specjalnie
    dobrałem złośliwy przykład.

    W tym momencie należy sobie zadać pytanie: jak dowodzić właściwości
    typów wzajemnie induktywnych? Aby udzielić odpowiedzi, spróbujmy
    udowodnić [even_plus] za pomocą indukcji po [n], a potem prześledźmy,
    co poszło nie tak. *)

Lemma even_plus_failed_1 : 
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction n; intros.
    assumption.
    cbn. constructor. inversion H; subst.
Abort.

(** Nasza indukcja po [n] zawiodła, gdyż nasza hipoteza indukcyjna ma w
    konkluzji [even (n + m)], podczas gdy nasz cel jest postaci
    [odd (n + m)]. Zauważmy, że teoretycznie cel powinno dać się udowodnić,
    jako że mamy hipotezy [even m] oraz [odd n], a suma liczby parzystej i
    nieparzystej jest nieparzysta.

    Nie zrażajmy się jednak i spróbujmy indukcji po dowodzie [even n]. *)

Lemma even_plus_failed_2 : 
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction 1; cbn; intro.
    assumption.
    constructor.
Abort.

(** Nasza indukcja po dowodzie hipotezy [even n] zawiodła, i to z kretesem,
    gdyż w kontekście nie mamy nawet żadnej hipotezy indukcyjnej! Co właściwie
    się stało? *)

Check even_ind.
(* ===> even_ind :
     forall P : nat -> Prop,
     P 0 -> (forall n : nat, odd n -> P (S n)) ->
       forall n : nat, even n -> P n *)

(** Jak widać, w naszej hipotezie "indukcyjnej" wygenerowanej przez Coqa w
    ogóle nie ma żadnej indukcji. Jest tam jedynie odwołanie do predykatu
    [odd]...

    Zauważmy jednak, że naszym celem znów było [odd (n + m)], a hipotezy
    [odd n] oraz [even m] sprawiają, że w teorii powinno dać się ten cel
    udowodnić, gdyż suma liczby parzystej i nieparzystej jest nieparzysta.

    Mogłoby się zdawać, że cierpimy na niedopasowanie (próba 1) lub brak
    (próba 2) hipotez indukcyjnych. Wydaje się też, że skoro w obydwu
    próbach zatrzymaliśmy się na celu [odd (n + m)], to pomocne mogłoby
    okazać się poniższe twierdzenie. *)

Lemma odd_even_plus_failed :
  forall n m : nat, odd n -> even m -> odd (n + m).
Proof.
  induction n; intros.
    inversion H.
    cbn. constructor. inversion H; subst.
Abort.

(** Niestety — nie dla psa kiełbasa, gdyż natykamy się na problemy bliźniaczo
    podobne do tych, które napotkaliśmy w poprzednim twierdzeniu: nasza
    hipoteza indukcyjna ma w konkluzji [odd (n + m)], podczas gdy nasz cel
    jest postaci [even (n + m)].

    Próba przepchnięcia lematu za pomocą indukcji po dowodzie hipotezy
    [odd n] także nie zadziała, z tych samych powodów dla których indukcja
    po [even n] nie pozwoliła nam udowodnić [even_plus]. Zauważmy jednak, że
    cel jest udowadnialny, gdyż jako hipotezy mamy [even n] oraz [even m],
    a suma dwóch liczb parzystych jest parzysta.

    Wydaje się, że wpadliśmy w błędne koło i jesteśmy w matni, bez wyjścia,
    bez nadziei, bez krzty szans na powodzenie: w dowodzie [even_plus]
    potrzebujemy lematu [odd_even_plus], ale nie możemy go udowodnić, gdyż
    w dowodzie [odd_even_plus] wymagane jest użycie lematu [even_plus].
    Ehhh, gdybyśmy tak mogli udowodnić oba te twierdzenia na raz...

    Eureka!

    Zauważ, że w naszych dotychczasowych dowodach przez indukcję posługiwaliśmy
    się zwykłą, "pojedynczą" indukcją. Była ona wystarczająca, gdyż mieliśmy do
    czynienia jedynie ze zwykłymi typami induktywnymi. Tym razem jednak jest
    inaczej: w ostatnich trzech dowodach chcieliśmy użyć "pojedynczej" indukcji
    do udowodnienia czegoś na temat predykatów wzajemnie induktywnych.

    Jest to ogromny zgrzyt. Do dowodzenia właściwości typów wzajemnie
    induktywnych powinniśmy użyć... o zgrozo, jak mogliśmy to przeoczyć,
    przecież to takie oczywiste... indukcji wzajemnej!

    Najprostszy sposób przeprowadzenia tego dowodu wygląda tak: *)

Theorem even_plus :
  forall n m : nat, even n -> even m -> even (n + m)
with odd_even_plus :
  forall n m : nat, odd n -> even m -> odd (n + m).
Proof.
  assumption.
  assumption.
Fail Qed.
Restart.
  destruct n as [| n']; cbn; intros.
    assumption.
    constructor. apply odd_even_plus.
      inversion H. assumption.
      assumption.
  destruct n as [| n']; cbn; intros.
    inversion H.
    constructor. apply even_plus.
      inversion H. assumption.
      assumption.
Qed.

(** Co tu się właściwie stało? Pierwsze dwie linijki są takie same jak
    poprzednio: stwierdzamy, że będziemy dowodzić twierdzenia o podanej
    nazwie i postaci. Następnie mamy słowo kluczowe [with], które pełni
    tu rolę podobną jak w definicjach przez indukcję wzajemną: podając po
    nim nazwę i postać twierdzenia mówimy Coqowi, że chcemy dowodzić tego
    twierdzenia ([odd_even_plus]) jednocześnie z poprzednim ([even_plus]).

    Dotychczas po rozpoczęciu dowodu ukazywał nam się jeden cel. Tym razem,
    jako że dowodzimy dwóch twierdzeń jednocześnie, mamy przed sobą dwa cele.
    W kontekście mamy też od razu dwie hipotezy indukcyjne. Musimy na nie
    bardzo uważać: dotychczas hipotezy indukcyjne pojawiały się dopiero w
    kroku indukcyjnym i sposób ich użycia był oczywisty. Tym razem jest
    inaczej — jako, że mamy je od samego początku, możemy natychmiast użyć
    ich do "udowodnienia" naszych twierdzeń.

    Niestety, takie "udowodnienie" odpowiada wywołaniu rekurencyjnemu na
    argumencie, który nie jest strukturalnie mniejszy (coś jak [f x := f x]).
    Fakt ten obrazuje wiadomość o błędzie, jaką Coq daje nam po tej próbie: *)

(* ===> Error: Cannot guess decreasing argument of fix. *)

(** Zaczynamy dowód od nowa, tym razem już bez oszukiwania. Musimy udowodnić
    każdy z naszych celów osobno, ale możemy korzystać z obydwu hipotez
    indukcyjnych. W obydwu celach zaczynamy od analizy przypadków, czyli
    rozbicia [n], i rozwiązania przypadku bazowego. Rozbicie [n] dało nam
    [n'], które jest strukturalnie mniejsze od [n], a zatem możemy bez obaw
    użyć naszej hipotezy indukcyjnej. Reszta jest trywialna. *)

Theorem even_double :
  forall n : nat, even (2 * n).
Proof.
  induction n as [| n']; cbn in *; constructor.
  rewrite <- plus_n_O in *. rewrite plus_comm. cbn. constructor.
    assumption.
Qed.

End MutInd.

(** * Różne *)

(** ** Rodziny typów induktywnych *)

(** Słowo kluczowe [Inductive] pozwala nam definiować nie tylko typy
    induktywne, ale także rodziny typów induktywnych — i to nawet na
    dwa sposoby. W tym podrozdziale przyjrzymy się obu z nich oraz
    różnicom między nimi, a także ich wadom i zaletom. Przyjrzyjmy się
    raz jeszcze typowi [option]: *)

Print option.
(* ===> Inductive option (A : Type) : Type :=
            | Some : A -> option A
            | None : option A *)

Check Some.
(* ===> Some : forall A : Type, A -> option A *)

Check @None.
(* ===> @None : forall A : Type, option A *)

(** Definiując rodzinę typów [option], umieściliśmy argument będący typem
    w nawiasach okrągłych tuż po nazwie definiowanego typu, a przed [: Type].
    Definiując konstruktory, nie napisaliśmy nigdzie [forall A : Type, ...],
    a mimo tego komenda [Check] jasno pokazuje, że typy obydwu konstruktorów
    zaczynają się od takiej właśnie kwantyfikacji.

    (Przypomnijmy, że w przypadku [None] argument [A] jest domyślny, więc
    wyświetlenie pełnego typu tego konstruktora wymagało użycia symbolu [@],
    który oznacza "wyświetl wszystkie argumenty domyślne").

    W ogólności, definiowanie rodziny typów [T] jako [T (x1 : A1) ... (xN : AN)]
    ma następujący efekt:
    - kwantyfikacja [forall (x1 : A1) ... (xN : AN)] jest dodawana na
      początek każdego konstruktora
    - w konkluzji konstruktora [T] musi wystąpić zaaplikowany do tych
      argumentów, czyli jako [T x1 ... xN] — wstawienie innych argumentów
      jest błędem *)

Fail Inductive option' (A : Type) : Type :=
    | Some' : A -> option' A
    | None' : forall B : Type, option' B.

(** Próba zdefiniowania typu [option'] kończy się następującym komunikatem
    o błędzie: *)

(* Error: Last occurrence of "option'" must have "A" as 1st argument in 
   "forall B : Type, option' B". *)

(** Drugi sposób zdefiniowania rodziny typów [option] przedstawiono
    poniżej. Tym razem zamiast umieszczać argument [A : Type] po
    nazwie definiowanego typu, deklarujemy, że typem [option'] jest
    [Type -> Type]. *)

Inductive option' : Type -> Type :=
    | Some' : forall A : Type, A -> option' A
    | None' : forall B : Type, option' B.

(** Taki zabieg daje nam większą swobodę: w każdym konstruktorze
    z osobna musimy explicité umieścić kwantyfikację po argumencie
    sortu [Type], dzięki czemu różne konstruktory mogą w konkluzji
    mieć [option'] zaaplikowany do różnych argumentów. *)

Check Some'.
(* ===> Some' : forall A : Type, A -> option' A *)

Check None'.
(* ===> None' : forall B : Type, option' B *)

(** Zauważmy jednak, że definicje [option] i [option'] są równoważne
    — typ konstruktora [None'] różni się od typu [None] jedynie nazwą
    argumentu ([A] dla [None], [B] dla [None']).

    Jak zatem rozstrzygnąć, który sposób definiowania jest "lepszy"?
    W naszym przypadku lepszy jest sposób pierwszy, odpowiadający
    typowi [option], gdyż jest bardziej zwięzły. Nie jest to jednak
    jedyne kryterium. *)

Check option_ind.
(* ===> option_ind :
            forall (A : Type) (P : option A -> Prop),
            (forall a : A, P (Some a)) -> P None ->
            forall o : option A, P o *)

Check option'_ind.
(* ===> option'_ind :
            forall P : forall T : Type, option' T -> Prop,
            (forall (A : Type) (a : A), P A (Some' A a)) ->
            (forall B : Type, P B (None' B)) ->
            forall (T : Type) (o : option' T), P T o *)

(** Dwa powyższe termy to reguły indukcyjne, wygenerowane automatycznie
    przez Coqa dla typów [option] oraz [option']. Reguła dla [option]
    jest wizualnie krótsza, co, jak dowiemy się w przyszłości, oznacza
    zapewne, że jest prostsza, zaś prostsza reguła indukcyjna oznacza
    łatwiejsze dowodzenie przez indukcję. Jest to w zasadzie najmocniejszy
    argument przemawiający za pierwszym sposobem zdefiniowania [option].

    Powyższe rozważania nie oznaczają jednak, że sposób pierwszy jest
    zawsze lepszy — sposób drugi jest bardziej ogólny i istnieją rodziny
    typów, których zdefiniowanie sposobem pierwszym jest niemożliwe.
    Klasycznym przykładem jest rodzina typów [vec]. *)

Inductive vec (A : Type) : nat -> Type :=
    | vnil : vec A 0
    | vcons : forall n : nat, A -> vec A n -> vec A (S n).

(** Konstruktor [vnil] reprezentuje listę pustą, której długość wynosi
    rzecz jasna [0], zaś [vcons] reprezentuje listę składająca się z
    głowy i ogona o długości [n], której długość wynosi oczywiście [S n].

    [vec] reprezetuje listy o długości znanej statycznie (tzn. Coq zna
    długość takiej listy już w trakcie sprawdzania typów), dzięki czemu
    możemy obliczać ich długość w czasie stałym (po prostu odczytując ją
    z typu danej listy).

    Zauważ, że w obu konstruktorach argumenty typu [nat] są różne, a zatem
    zdefiniowanie tego typu jako [vec (A : Type) (n : nat) ...] byłoby
    niemożliwe.

    Przykład ten pokazuje nam również, że przy definiowaniu rodzin typów
    możemy dowolnie mieszać sposoby pierwszy i drugi — w naszym przypadku
    argument [A : Type] jest wspólny dla wszystkich konstruktorów, więc
    umieszczamy go przed ostatnim [:], zaś argument typu [nat] różni się
    w zależności od konstruktora, a zatem umieszczamy go po ostatnim [:]. *)

(** **** Ćwiczenie *)

(** Zdefiniuj następujące typy (zadbaj o to, żeby wygenerowana reguła
    indukcyjna była jak najkrótsza):
    - typ drzew binarnych przechowujących elementy typu [A]
    - typ drzew binarnych przechowujących elementy typu [A],
      których wysokość jest znana statycznie
    - typ heterogenicznych drzew binarnych (mogą one
      przechowywać elementy różnych typów)
    - typ heterogenicznych drzew binarnych, których wysokość
      jest znana statycznie *)

(* begin hide *)
Inductive BTree (A : Type) : Type :=
    | BT_Empty : BTree A
    | BT_Node : A -> BTree A -> BTree A -> BTree A.

Inductive EBTree (A : Type) : nat -> Type :=
    | EBT_Empty : EBTree A 0
    | EBT_Node : forall n m : nat,
        A -> EBTree A n -> EBTree A m -> EBTree A (max n m).

Inductive HBTree : Type :=
    | HBT_Empty : HBTree
    | HBT_Node : forall A : Type, A -> HBTree -> HBTree -> HBTree.

Check HBT_Node _ 42 (HBT_Node _ true HBT_Empty HBT_Empty) HBT_Empty.

Inductive EHBTree : nat -> Type :=
    | EHBT_Empty : EHBTree 0
    | EHBT_Node : forall (A : Type) (n m : nat),
        A -> EHBTree n -> EHBTree m -> EHBTree (max n m).
(* end hide *)

(** ** Indukcja wzajemna a indeksowane rodziny typów *)

Module MutualIndution_vs_InductiveFamilies.

(** Indukcja wzajemna nie jest zbyt użyteczna. Pierwszym, praktycznym,
    powodem jest to, że, jak pewnie zdążyłeś się już na własnej skórze
    przekonać, jej używanie jest dość upierdliwe. Drugi, teoretyczny,
    powód jest taki, że definicje przez indukcję wzajemną możemy łatwo
    zasymulować za pomocą indeksowanych rodzin typów. *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenS : forall n : nat, odd n -> even (S n)

with odd : nat -> Prop :=
    | oddS : forall n : nat, even n -> odd (S n).

(** Rzućmy jeszcze raz okiem na znaną nam już definicję predykatów [even]
    i [odd] przez indukcję wzajemną. Nie dzieje się tu nic niezwykłego, a
    najważniejszym spostrzeżeniem, jakie możemy poczynić, jest to, że
    [even] i [odd] to dwa byty - nie trzy, nie pięć, ale dwa. *)

Inductive even_odd : bool -> nat -> Prop :=
    | even0' : even_odd true 0
    | evenS' :
        forall n : nat, even_odd false n -> even_odd true (S n)
    | oddS' :
        forall n : nat, even_odd true n -> even_odd false (S n).

Definition even' := even_odd true.
Definition odd' := even_odd false.

(** Co z tego wynika? Ano, zamiast definiować przez indukcję wzajemną dwóch
    predykatów [even] i [odd] możemy za jednym zamachem zdefiniować relację
    [even_odd], która jednocześnie odpowiada obu tym predykatom. Kluczem
    w tej sztuczce jest dodatkowy indeks, którym jest dwuelementowy typ
    [bool]. Dzięki niemu możemy zakodować definicję [even] za pomocą
    [even_odd true], zaś [odd] jako [even_odd false]. *)

Lemma even_even' :
  forall n : nat, even n -> even' n

with odd_odd' :
  forall n : nat, odd n -> odd' n.
(* begin hide *)
Proof.
  destruct n as [| n']; intro.
    constructor.
    constructor. apply odd_odd'. inversion H; assumption.
  destruct n as [| n']; intro.
    inversion H.
    constructor. apply even_even'. inversion H; assumption.
Qed.
(* end hide *)

Lemma even'_even :
  forall n : nat, even' n -> even n

with odd'_odd :
  forall n : nat, odd' n -> odd n.
(* begin hide *)
Proof.
  destruct n as [| n']; intro.
    constructor.
    constructor. apply odd'_odd. inversion H; assumption.
  destruct n as [| n']; intro.
    inversion H.
    constructor. apply even'_even. inversion H; assumption.
Qed.
(* end hide *)

(** Obie definicje są, jak widać (ćwiczenie!), równoważne, choć pod względem
    estetycznym oczywiście dużo lepiej wypada indukcja wzajemna. *)

End MutualIndution_vs_InductiveFamilies.

(** Na koniec wypada jeszcze powiedzieć, że indeksowane typy induktywne są
    potężniejsze od typów wzajemnie induktywnych. Wynika to z tego prostego
    faktu, że przez wzajemną indukcję możemy zdefiniować na raz jedynie
    skończenie wiele typów, zaś indeksowane typy induktywne indeksowane
    mogą być typami nieskończonymi. *)

(** ** Sumy zależne i podtypy *)

(** W Coqu, w przeciwieństwie do wielu języków imperatywnych, nie ma
    mechanizmu podtypowania, a każde dwa typy są ze sobą rozłączne.
    Nie jest to problemem, gdyż podtypowanie możemy zasymulować za
    pomocą sum zależnych, a te zdefiniować możemy induktywnie. *)

Module sigma.

Inductive sigT (A : Type) (P : A -> Type) : Type :=
    | existT : forall x : A, P x -> sigT A P.

(** Typ [sigT] reprezentuje sumę zależną, której elementami są pary zależne.
    Pierwszym elementem pary jest [x], który jest typu [A], zaś drugim
    elementem pary jest term typu [P x]. Suma zależna jest wobec tego pewnym
    uogólnieniem produktu.

    Niech cię nie zmyli nazewnictwo:
    - Suma jest reprezentowana przez typ [sum A B]. Jej elementami są
      elementy [A] zawinięte w konstruktor [inl] oraz elementy [B]
      zawinięte w konstruktor [inr]. Reprezentuje ideę "lub/albo".
      Typ [B] nie może zależeć od typu [A].
    - Produkt jest reprezentowany przez typ [prod A B]. Jego elementami
      są pary elementów [A] i [B]. Reprezentuje on ideę "i/oraz". Typ
      [B] nie może zależeć od typu [A].
    - Uogólnieniem produktu jest suma zależna. Jest ona reprezentowana
      przez typ [sigT A P]. Jej elementami są pary zależne elementów
      [A] i [P x], gdzie [x : A] jest pierwszym elementem pary.
      Reprezentuje ona ideę "i/oraz", gdzie typ [P x] może zależeć od
      elementu [x] typu [A].
    - Typ funkcji jest reprezentowany przez [A -> B]. Jego elementami
      są termy postaci [fun x : A => ...]. Reprezentują ideę "daj mi
      coś typu [A], a ja oddam ci coś typu [B]". Typ [B] nie może
      zależeć od typu [A].
    - Uogólnieniem typu funkcji jest produkt zależny [forall x : A, B x].
      Jego elementami są termu postaci [fun x : A => ...]. Reprezentuje
      on ideę "daj mi [x] typu [A], a ja oddam ci coś typu [B x]". Typ
      [B x] może zależeć od typu elementu [x] typu [A]. *)

(** [sigT] jest najogólniejszą postacią pary zależnej — [A] jest typem,
    a [P] rodziną typów. Mimo swej ogólności jest używany dość rzadko,
    gdyż najbardziej przydatną postacią sumy zależnej jest typ [sig]: *)

Inductive sig (A : Type) (P : A -> Prop) : Type :=
    | exist : forall x : A, P x -> sig A P.

Arguments exist [A] [P] _ _.

(** Typ [sig A P] można interpretować jako typ składający się z tych
    elementów [A], które spełniają predykat [P]. Formalnie jest to
    para zależna, której pierwszym elementem jest term typu [A], zaś
    drugim dowód na to, że spełnia on predykat [P]. *)

Definition even_nat : Type := sig nat even.

Definition even_four : even_nat := exist 4 four_is_even.

(** Typ [even_nat] reprezentuje parzyste liczby naturalne, zaś term
    [even_four] to liczba [4] wraz z załączonym dowodem faktu, że [4]
    jest parzyste.

    Interpretacja typu [sig] sprawia, że jest on wykorzystywany bardzo
    często do podawania specyfikacji programów — pozwala on dodać do
    wyniku zwracanego przez funkcję informację o jego właściwościach.
    W przypadku argumentów raczej nie jest używany, gdyż prościej jest
    po prostu wymagać dowodów żądanych właściwości w osobnych argumentach
    niż pakować je w [sig] po to, żeby i tak zostały później odpakowane. *)

Definition even_42 : sig nat even.
Proof.
  apply (exist 42). repeat constructor.
Defined.

(** Definiowanie wartości typu [sig] jest problematyczne, gdyż zawierają
    one dowody. Napisanie definicji "ręcznie", explicité podając proofterm,
    nie wchodzi w grę. Innym potencjalnym rozwiązaniem jest napisanie dowodu
    na boku, a następnie użycie go we właściwej definicji, ale jest ono
    dłuższe niż to konieczne.

    Przypomnijmy sobie, czym są taktyki. Dowody to termy, których typy są
    sortu [Prop], a taktyki służą do konstruowania tych dowodów. Ponieważ
    dowody nie różnią się (prawie) niczym od programów, taktyk można użyć
    także do pisania programów. Taktyki to metaprogramy (napisane w jęzku
    Ltac), które piszą programy (w jęzku termów Coqa, zwanym Gallina).

    Wobec tego trybu dowodzenia oraz taktyk możemy używać nie tylko do
    dowodzenia, ale także do definiowania i to właśnie uczyniliśmy w
    powyższym przykładzie. Skonstruowanie termu typu [sig nat even],
    czyli parzystej liczby naturalnej, odbyło się w następujący sposób.

    Naszym celem jest początkowo [sig nat even], czyli typ, którego
    element chcemy skonstrować. Używamy konstruktora [exist], który
    w naszym przypadku jest typu [forall x : nat, even n -> sig nat even].
    Wobec tego [exist 42] jest typu [even 42 -> sig nat even], a jego
    zaaplikowanie skutkować będzie zamianą naszego celu na [even 42].
    Następnie dowodzimy tego faktu, co kończy proces definiowania. *)

(** **** Ćwiczenie *)

(** Zdefiniuj predykat [sorted], który jest spełniony, gdy jego argument
    jest listą posortowaną. Następnie zdefiniuj typ list liczb naturalnych
    posortowanych według relacji [<=] i skonstruuj term tego typu
    odpowiadający liście [[42; 666; 1337]]. *)

End sigma.

(** ** Kwantyfikacja egzystencjalna *)

(** Znamy już pary zależne i wiemy, że mogą służyć do reprezentowania
    podtypów, których w Coqu brak. Czas zatem uświadomić sobie kolejny
    fragment korespondencji Curry'ego-Howarda, a mianowicie definicję
    kwantyfikacji egzystencjalnej: *)

Module ex.

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    | ex_intro : forall x : A, P x -> ex A P.

(** [ex] to kolejne wcielenie sumy zależnej. Porównaj dokładnie tę
    definicję z definicją [sigT] oraz [sig]. [ex] jest niemal identyczne
    jak [sig]: jest to para zależna, której pierwszym elementem jest
    term [x : A], a drugim dowód na to, że [P x] zachodzi. [ex] jednak,
    w przeciwieństwie do [sig], żyje w [Prop], czyli jest zdaniem — nie
    liczą się konkretne postaci jego termów ani ich ilość, a jedynie
    fakt ich istnienia. To sprawia, że [ex] jest doskonałym kandydatem
    do reprezentowania kwantyfikacji egzystencjalnej. *)

(** **** Ćwiczenie *)

(** Udowodnij, że dla każdej liczby naturalnej n istnieje liczba od niej
    większa. Następnie zastanów się, jak działa taktyka [exists]. *)

Theorem exists_greater :
  forall n : nat, ex nat (fun k : nat => n < k).
(* begin hide *)
Proof.
  intro. apply (ex_intro _ _ (S n)). unfold lt. apply le_n.
Qed.
(* end hide *)

End ex.

(** * Wyższe czary *)

(** Najwyższy czas nauczyć się czegoś tak zaawansowanego, że nawet w Coqu
    (pełnym przecież dziwnych rzeczy) tego nie ma i nie zapowiada się na
    to, że będzie. Mam tu na myśli mechanizmy takie jak indukcja-indukcja,
    indukcja-rekursja oraz indukcja-indukcja-rekursja (jak widać, w świecie
    poważnych uczonych, podobnie jak świecie Goebbelsa, im więcej razy
    powtórzy się dane słowo, tym więcej płynie z niego mocy). *)

(** ** Przypomnienie *)

(** Zanim jednak wyjaśnimy, co to za stwory, przypomnijmy sobie różne, coraz
    bardziej innowacyjne sposoby definiowania przez indukcję oraz dowiedzmy
    się, jak sformułować i udowodnić wynikające z nich reguły rekursji oraz
    indukcji. *)

Unset Elimination Schemes.

(** Powyższa komenda mówi Coqowi, żeby nie generował automatycznie reguł
    indukcji. Przyda nam się ona, by uniknąć konfliktów nazw z regułami,
    które będziemy pisać ręcznie. *)

(** *** Enumeracje *)

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

(** *** Konstruktory rekurencjne *)

Module rec.

Inductive I : Type :=
    | x : I -> I
    | D : I -> I.

(** Typy induktywne stają się naprawdę induktywne, gdy konstruktory mogą
    brać argumenty typu, który właśnie definiujemy. Dzięki temu możemy
    tworzyć type, które mają nieskończenie wiele elementów, z których
    każdy ma kształt takiego czy innego drzewa. *)

Definition I_rec_type : Type :=
  forall P : Type,  (P -> P) -> (P -> P) -> I -> P.

(** Typ reguły rekursji (czyli rekursora) tworzymy tak jak dla enumeracji:
    jeżeli w typie [P] znajdziemy rzeczy o takim samym kształcie jak
    konstruktory typu [I], to możemy zrobić funkcję [I -> P]. W naszym
    przypadku oba konstruktory mają kształt [I -> I], więc do zdefiniowania
    naszej funkcji musimy znaleźć odpowiadające im rzeczy typu [P -> P]. *)

Fixpoint I_rec (P : Type) (x' : P -> P) (D' : P -> P) (i : I) : P :=
match i with
    | x i' => x' (I_rec P x' D' i')
    | D i' => D' (I_rec P x' D' i')
end.

(** Definicja rekursora jest prosta. Jeżeli wyobrazimy sobie [i : I] jako
    drzewo, to węzły z etykietką [x] zastępujemy wywołaniem funkcji [x'],
    a węzły z etykietką [D] zastępujemy wywołaniami funkcji [D]. *)

Definition I_ind_type : Type :=
  forall (P : I -> Type)
    (x' : forall i : I, P i -> P (x i))
    (D' : forall i : I, P i -> P (D i)),
      forall i : I, P i.

(** Reguła indukcji (czyli induktor - cóż za piękna nazwa!) powstaje z
    reguły rekursji przez uzależnienie przeciwdziedziny [P] od dziedziny
    [I]. *)

Fixpoint I_ind (P : I -> Type)
  (x' : forall i : I, P i -> P (x i)) (D' : forall i : I, P i -> P (D i))
  (i : I) : P i :=
match i with
    | x i' => x' i' (I_ind P x' D' i')
    | D i' => D' i' (I_ind P x' D' i')
end.

(** Podobnie jak poprzednio, implementacja reguły indukcji jest identyczna
    jak rekursora, jedynie typy są bardziej ogólnej.

    Uwaga: nazywam reguły nieco inaczej niż te autogenerowane przez Coqa.
    Dla Coqa reguła indukcji dla [I] to nasze [I_ind] z [P : I -> Type]
    zastąpionym przez [P : I -> Prop], zaś Coqowe [I_rec] odpowiadałoby
    naszemu [I_ind] dla [P : I -> Set].

    Jeżeli smuci cię burdel nazewniczy, to nie przejmuj się - kiedyś będzie
    lepiej. Klasyfikacja reguł jest prosta:
    - reguły mogą być zależne lub nie, w zależności od tego czy [P] zależy
      od [I]
    - reguły mogą być rekurencyjne lub nie
    - reguły mogą być dla sortu [Type], [Prop] albo nawet [Set] *)

End rec.

(** *** Parametry *)

Module param.

Inductive I (A B : Type) : Type :=
    | c0 : A -> I A B
    | c1 : B -> I A B
    | c2 : A -> B -> I A B.

Arguments c0 {A B} _.
Arguments c1 {A B} _.
Arguments c2 {A B} _ _.

(** Kolejną innowacją są parametry, których głównym zastosowaniem jest
    polimorfizm. Dzięki parametrom możemy za jednym zamachem (tylko bez
    skojarzeń z Islamem!) zdefiniować nieskończenie wiele typów, po jednym
    dla każdego parametru. *)

Definition I_case_nondep_type : Type :=
  forall (A B P : Type) (c0' : A -> P) (c1' : B -> P) (c2' : A -> B -> P),
    I A B -> P.

(** Typ rekursora jest oczywisty: jeżeli znajdziemy rzeczy o kształtach
    takich jak konstruktory [I] z [I] zastąpionym przez [P], to możemy
    zrobić funkcję [I -> P]. Jako, że parametry są zawsze takie samo,
    możemy skwantyfikować je na samym początku. *)

Definition I_case_nondep
  (A B P : Type) (c0' : A -> P) (c1' : B -> P) (c2' : A -> B -> P)
  (i : I A B) : P :=
match i with
    | c0 a => c0' a
    | c1 b => c1' b
    | c2 a b => c2' a b
end.

(** Implementacja jest banalna. *)

Definition I_case_dep_type : Type :=
  forall (A B : Type) (P : I A B -> Type)
    (c0' : forall a : A, P (c0 a))
    (c1' : forall b : B, P (c1 b))
    (c2' : forall (a : A) (b : B), P (c2 a b)),
      forall i : I A B, P i.

(** A regułę indukcję uzyskujemy przez uzależnienie [P] od [I]. *)

Definition I_case_dep
  (A B : Type) (P : I A B -> Type)
  (c0' : forall a : A, P (c0 a))
  (c1' : forall b : B, P (c1 b))
  (c2' : forall (a : A) (b : B), P (c2 a b))
  (i : I A B) : P i :=
match i with
    | c0 a => c0' a
    | c1 b => c1' b
    | c2 a b => c2' a b
end.

End param.

(** *** Indukcja wzajemna *)

Module mutual.

Inductive Smok : Type :=
    | Wysuszony : Zmok -> Smok

with Zmok : Type :=
    | Zmoczony : Smok -> Zmok.

(** Indukcja wzajemna pozwala definiować na raz wiele typów, które mogą
    odwoływać się do siebie nawzajem. Cytując klasyków: smok to wysuszony
    zmok, zmok to zmoczony smok. *)

Definition Smok_case_nondep_type : Type :=
  forall S : Type, (Zmok -> S) -> Smok -> S.

Definition Zmok_case_nondep_type : Type :=
  forall Z : Type, (Smok -> Z) -> Zmok -> Z.

(** Reguła niezależnej analizy przypadków dla [Smok]a wygląda banalnie:
    jeżeli ze [Zmok]a potrafimy wyprodukować [S], to ze [Smok]a też.
    Dla [Zmok]a jest analogicznie. *)

Definition Smok_case_nondep
  (S : Type) (Wy : Zmok -> S) (smok : Smok) : S :=
match smok with
    | Wysuszony zmok => Wy zmok
end.

Definition Zmok_case_nondep
  (Z : Type) (Zm : Smok -> Z) (zmok : Zmok) : Z :=
match zmok with
    | Zmoczony smok => Zm smok
end.

(** Implementacja jest banalna. *)

Definition Smok_rec_type : Type :=
  forall S Z : Type, (Z -> S) -> (S -> Z) -> Smok -> S.

Definition Zmok_rec_type : Type :=
  forall S Z : Type, (Z -> S) -> (S -> Z) -> Zmok -> Z.

(** Typ rekursora jest jednak nieco bardziej zaawansowany. Żeby zdefiniować
    funkcję typu [Smok -> S], musimy mieć nie tylko rzeczy w kształcie
    konstruktorów [Smok]a, ale także w kształcie konstruktorów [Zmok]a,
    gdyż rekurencyjna struktura obu typów jest ze sobą nierozerwalnie
    związana. *)

Fixpoint Smok_rec
  (S Z : Type) (Wy : Z -> S) (Zm : S -> Z) (smok : Smok) : S :=
match smok with
    | Wysuszony zmok => Wy (Zmok_rec S Z Wy Zm zmok)
end

with Zmok_rec
  (S Z : Type) (Wy : Z -> S) (Zm : S -> Z) (zmok : Zmok) : Z :=
match zmok with
    | Zmoczony smok => Zm (Smok_rec S Z Wy Zm smok)
end.

(** Implementacja wymaga rekursji wzajemnej, ale poza nie jest jakoś
    wybitnie groźna. *)

Definition Smok_ind_type : Type :=
  forall (S : Smok -> Type) (Z : Zmok -> Type)
    (Wy : forall zmok : Zmok, Z zmok -> S (Wysuszony zmok))
    (Zm : forall smok : Smok, S smok -> Z (Zmoczony smok)),
      forall smok : Smok, S smok.

Definition Zmok_ind_type : Type :=
  forall (S : Smok -> Type) (Z : Zmok -> Type)
    (Wy : forall zmok : Zmok, Z zmok -> S (Wysuszony zmok))
    (Zm : forall smok : Smok, S smok -> Z (Zmoczony smok)),
      forall zmok : Zmok, Z zmok.

Fixpoint Smok_ind
  (S : Smok -> Type) (Z : Zmok -> Type)
  (Wy : forall zmok : Zmok, Z zmok -> S (Wysuszony zmok))
  (Zm : forall smok : Smok, S smok -> Z (Zmoczony smok))
  (smok : Smok) : S smok :=
match smok with
    | Wysuszony zmok => Wy zmok (Zmok_ind S Z Wy Zm zmok)
end

with Zmok_ind
  (S : Smok -> Type) (Z : Zmok -> Type)
  (Wy : forall zmok : Zmok, Z zmok -> S (Wysuszony zmok))
  (Zm : forall smok : Smok, S smok -> Z (Zmoczony smok))
  (zmok : Zmok) : Z zmok :=
match zmok with
    | Zmoczony smok => Zm smok (Smok_ind S Z Wy Zm smok)
end.

(** Mając rekursor, napisanie typu reguły indukcji jest banalne, podobnie
    jak jego implementacja. *)

End mutual.

(** *** Indeksy *)

Module index.

Inductive I : nat -> Type :=
    | c0 : bool -> I 0
    | c42 : nat -> I 42.

(** Ostatnią poznaną przez nas innowacją są typy indeksowane. Tutaj również
    definiujemy za jednym zamachem (ekhem...) dużo typów, ale nie są one
    niezależne jak w przypadku parametrów, lecz mogą od siebie wzajemnie
    zależeć. Słowem, tak naprawdę definiujemy przez indukcję funkcję
    typu [A_1 -> ... -> A_n -> Type/Prop], gdzie [A_i] to indeksy. *)

Definition I_case_very_nondep_type : Type :=
  forall (P : Type) (c0' : bool -> P) (c42' : nat -> P),
    forall n : nat, I n -> P.

Definition I_case_very_nondep
  (P : Type) (c0' : bool -> P) (c42' : nat -> P)
  {n : nat} (i : I n) : P :=
match i with
    | c0 b => c0' b
    | c42 n => c42' n
end.

(** Możliwych reguł analizy przypadków mamy tutaj trochę więcej niż w
    przypadku parametrów. W powyższej regule [P] nie zależy od indeksu
    [n : nat]... *)

Definition I_case_nondep_type : Type :=
  forall (P : nat -> Type) (c0' : bool -> P 0) (c42' : nat -> P 42),
    forall n : nat, I n -> P n.

Definition I_case_nondep
  (P : nat -> Type) (c0' : bool -> P 0) (c42' : nat -> P 42)
  {n : nat} (i : I n) : P n :=
match i with
    | c0 b => c0' b
    | c42 n => c42' n
end.

(** ... a w powyższej tak. Jako, że indeksy zmieniają się pomiędzy
    konstruktorami, każdy z nich musi kwantyfikować je osobno (co akurat
    nie jest potrzebne w naszym przykładzie, gdyż jest zbyt prosty). *)

Definition I_case_dep_type : Type :=
  forall (P : forall n : nat, I n -> Type)
    (c0' : forall b : bool, P 0 (c0 b))
    (c42' : forall n : nat, P 42 (c42 n)),
      forall (n : nat) (i : I n), P n i.

Definition I_case_dep
  (P : forall n : nat, I n -> Type)
  (c0' : forall b : bool, P 0 (c0 b))
  (c42' : forall n : nat, P 42 (c42 n))
  (n : nat) (i : I n) : P n i :=
match i with
    | c0 b => c0' b
    | c42 n => c42' n
end.

(** Ogólnie reguła jest taka: reguła niezależna (pierwsza) nie zależy od
    niczego, a zależna (trzecia) zależy od wszystkiego. Reguła druga jest
    pośrednia - ot, take ciepłe kluchy. *)

End index.

(** Nie zapomnijmy ponownie nakazać Coqowi generowania reguł indukcji. *)
Set Elimination Schemes.

(** ** Indukcja-indukcja *)

Module ind_ind.

(** Po powtórce nadszedł czas nowości. Zacznijmy od nazwy, która jest iście
    kretyńska: indukcja-indukcja. Każdy rozsądny człowiek zgodzi się,
    że dużo lepszą nazwą byłoby coś w stylu "indukcja wzajemna indeksowana".

    Ta alternatywna nazwa rzuca sporo światła: indukcja-indukcja to połączenie
    i uogólnienie mechanizmów definiowania typów wzajemnie induktywnych oraz
    indeksowanych typów induktywnych.

    Typy wzajemnie induktywne mogą odnosić się do siebie nawzajem, ale co
    to dokładnie znaczy? Ano to, że konstruktory każdego typu mogą brać
    argumenty wszystkch innych typów definiowanych jednocześnie z nim. To
    jest clou całej sprawy: konstruktory.

    A co to ma do typów indeksowanych? Ano, zastanówmy się, co by się stało,
    gdybyśmy chcieli zdefiniować przez wzajemną indukcję typ [A] oraz rodzinę
    typów [B : A -> Type]. Otóż nie da się: konstruktory [A] mogą odnosić
    się do [B] i vice-versa, ale [A] nie może być indeksem [B].

    Indukcja-indukcja to coś, co... tam taram tam tam... pozwala właśnie na
    to: możemy jednocześnie zdefiniować typ i indeksowaną nim rodzinę typów.
    I wszystko to ukryte pod taką smutną nazwą... lobby teoriotypowe nie
    chciało, żebyś się o tym dowiedział.

    Czas na przykład! *)

Fail

Inductive slist {A : Type} (R : A -> A -> Prop) : Type :=
    | snil : slist R
    | scons : forall (h : A) (t : slist A), ok h t -> slist A

with ok {A : Type} {R : A -> A -> Prop} : A -> slist R -> Prop :=
    | ok_snil : forall x : A, ok x snil
    | ok_scons :
        forall (h : A) (t : slist A) (p : ok h t) (x : A),
          R x h -> ok x (scons h t p).

(* ===> The reference slist was not found in the current environment. *)

(** Jako się już wcześniej rzekło, indukcja-indukcja nie jest wspierana
    przez Coqa - powyższa definicja kończy się informacją o błędzie: Coq
    nie widzi [slist] kiedy czyta indeksy [ok] właśnie dlatego, że nie
    dopuszcza on możliwości jednoczesnego definiowania rodziny (w tym
    wypadku relacji) [ok] wraz z jednym z jej indeksów, [slist].

    Będziemy zatem musieli poradzić sobie z przykładem jakoś inaczej -
    po prostu damy go sobie za pomocą aksjomatów. Zanim jednak to zrobimy,
    omówimy go dokładniej, gdyż deklarowanie aksjomatów jest niebezpieczne
    i nie chcemy się pomylić.

    Zamysłem powyższego przykładu było zdefiniowanie typu list posortowanych
    [slist R], gdzie [R] pełni rolę relacji porządku, jednocześnie z relacją
    [ok : A -> slist R -> Prop], gdzie [ok x l] wyraża, że dostawienie [x]
    na początek listy posortowanej [l] daje listę posortowaną.

    Przykład jest oczywiście dość bezsensowny, bo dokładnie to samo można
    osiągnąć bez używania indukcji-indukcji - wystarczy najpierw zdefiniować
    listy, a potem relację bycia listą posortowaną, a na koniec zapakować
    wszystko razem. Nie będziemy się tym jednak przejmować.

    Definicja [slist R] jest następująca:
    - [snil] to lista pusta
    - [scons] robi posortowaną listę z głowy [h] i ogona [t] pod warunkiem, że
      dostanie też dowód zdania [ok h t] mówiącego, że można dostawić [h] na
      początek listy [t] *)

(** Definicja [ok] też jest banalna:
    - każdy [x : A] może być dostawiony do pustej listy
    - jeżeli mamy listę [scons h t p] oraz element [x], o którym wiemy,
      że jest mniejszy od [h], tzn. [R x h], to [x] może zostać dostawiony
      do listy [scons h t p] *)

(** Jak powinny wyglądać reguły rekursji oraz indukcji? Na szczęście wciąż
    działają schematy, które wypracowaliśmy dotychczas.

    Reguła rekursji mówi, że jeżeli znajdziemy w typie [P] coś o kształcie
    [slist R], a w relacji [Q] coś o kształcie [ok], to możemy zdefiniować
    funkcję [slist R -> P] oraz [forall (x : A) (l : slist R), ok x l -> Q].

    Regułe indukcji można uzyskać dodając tyle zależności, ile tylko zdołamy
    unieść.

    Zobaczmy więc, jak zrealizować to wszystko za pomocą aksjomatów. *)

Axioms
  (slist : forall {A : Type}, (A -> A -> Prop) -> Type)
  (ok : forall {A : Type} {R : A -> A -> Prop}, A -> slist R -> Prop).

(** Najpierw musimy zadeklarować [slist], gdyż wymaga tego typ [ok]. Obie
    definicje wyglądają dokładnie tak, jak nagłówki w powyższej definicji
    odrzuconej przez Coqa.

    Widać też, że gdybyśmy chcieli zdefiniować rodziny [A] i [B], które są
    nawzajem swoimi indeksami, to nie moglibyśmy tego zrobić nawet za pomocą
    aksjomatów. Rodzi to pytanie o to, które dokładnie definicje przez
    indukcję-indukcję są legalne. Odpowiedź brzmi: nie wiem, ale może kiedyś
    się dowiem. *)

Axioms
  (snil : forall {A : Type} {R : A -> A -> Prop}, slist R)
  (scons :
    forall {A : Type} {R : A -> A -> Prop} (h : A) (t : slist R),
      ok h t -> slist R)
  (ok_snil :
    forall {A : Type} {R : A -> A -> Prop} (x : A), ok x (@snil _ R))
  (ok_scons :
    forall
      {A : Type} {R : A -> A -> Prop}
      (h : A) (t : slist R) (p : ok h t)
      (x : A), R x h -> ok x (scons h t p)).

(** Następnie definiujemy konstruktory: najpierw konstruktory [slist], a
    potem [ok]. Musimy to zrobić w tej kolejności, bo konstruktor [ok_snil]
    odnosi się do [snil], a [ok_scons] do [scons].

    Znowu widzimy, że gdyby konstruktory obu typów odnosiły się do siebie
    nawzajem, to nie moglibyśmy zdefiniować takiego typu aksjomatycznie. *)

Axiom
  (ind : forall
    (A : Type) (R : A -> A -> Prop)
    (P : slist R -> Type)
    (Q : forall (h : A) (t : slist R), ok h t -> Type)
    (Psnil : P snil)
    (Pscons :
      forall (h : A) (t : slist R) (p : ok h t),
        P t -> Q h t p -> P (scons h t p))
    (Qok_snil : forall x : A, Q x snil (ok_snil x))
    (Qok_scons :
      forall
        (h : A) (t : slist R) (p : ok h t)
        (x : A) (H : R x h),
          P t -> Q h t p -> Q x (scons h t p) (ok_scons h t p x H)),
    {f : (forall l : slist R, P l) &
    {g : (forall (h : A) (t : slist R) (p : ok h t), Q h t p) |
      f snil = Psnil /\
      (forall (h : A) (t : slist R) (p : ok h t),
        f (scons h t p) = Pscons h t p (f t) (g h t p)) /\
      (forall x : A,
        g x snil (ok_snil x) = Qok_snil x) /\
      (forall
        (h : A) (t : slist R) (p : ok h t)
        (x : A) (H : R x h),
          g x (scons h t p) (ok_scons h t p x H) =
          Qok_scons h t p x H (f t) (g h t p))
    }}).

(** Ugh, co za potfur. Spróbujmy rozłożyć go na czynniki pierwsze.

    Przede wszystkim, żeby za dużo nie pisać, zobaczymy tylko regułę indukcji.
    Teoretycznie powinny to być dwie reguły (tak jak w przypadku [Smok]a i
    [Zmok]a) - jedna dla [slist] i jedna dla [ok], ale żeby za dużo nie
    pisać, możemy zapisać je razem.

    Typ [A] i relacja [R] są parametrami obu definicji, więc skwantyfikowane
    są na samym początku. Nasza reguła pozwala nam zdefiniować przez wzajemną
    rekursję dwie funkcje, [f : forall l : slist R, P l] oraz
    [g : forall (h : A) (t : slist R) (p : ok h t), Q h t p]. Tak więc [P]
    to kodziedzina [f], a [Q] - [g].

    Teraz potrzebujemy rozważyć wszystkie możliwe przypadki - tak jak przy
    dopasowaniu do wzorca. Przypadek [snil] jest dość banalny. Przypadek
    [scons] jest trochę cięższy. Przede wszystkim chcemy, żeby konkluzja
    była postaci [P (scons h t p)], ale jak powinny wyglądać hipotezy
    indukcyjne?

    Jedyna słuszna odpowiedź brzmi: odpowiadają one typom wszystkich możliwych
    wywołań rekurencyjnych [f] i [g] na strukturalnych podtermach
    [scons h t p]. Jedynymi typami spełniającymi te warunki są [P t] oraz
    [Q h t p], więc dajemy je sobie jako hipotezy indukcyjne.

    Przypadki dla [Q] wyglądają podobnie: [ok_snil] jest banalne, a dla
    [ok_scons] konkluzja musi być jedynej słusznej postaci, a hipotezami
    indukcyjnymi jest wszystko, co pasuje.

    W efekcie otrzymujemy dwie funkcje, [f] i [g]. Tym razem następuje jednak
    mały twist: ponieważ nasza definicja jest aksjomatyczna, zagwarantować
    musimy sobie także reguły obliczania, które dotychczas były zamilaczne,
    bo wynikały z definicji przez dopasowanie do wzorca. Teraz wszystkie te
    "dopasowania" musimy napisać ręcznie w postaci odpowiednio
    skwantyfikowanych równań. Widzimy więc, że [Psnil], [Pscons], [Qok_snil]
    i [Qok_scons] odpowiadają klauzulom w dopasowaniu do wzorca.

    Ufff... udało się. Tak spreparowaną definicją aksjomatyczną możemy się
    jako-tako posługiwać: *)

Definition rec'
  {A : Type} {R : A -> A -> Prop}
  (P : Type) (snil' : P) (scons' : A -> P -> P) :
  {f : slist R -> P |
    f snil = snil' /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = scons' h (f t)
  }.
Proof.
  destruct
  (
    ind
    A R
    (fun _ => P) (fun _ _ _ => True)
    snil' (fun h _ _ t _ => scons' h t)
    (fun _ => I) (fun _ _ _ _ _ _ _ => I)
  )
  as (f & g & H1 & H2 & H3 & H4).
  exists f. split.
    exact H1.
    exact H2.
Defined.

(** Możemy na przykład dość łatwo zdefiniować niezależny rekursor tylko dla
    [slist], nie odnoszący się w żaden sposób do [ok]. Widzimy jednak, że
    "programowanie" w taki aksjomatyczny sposób jest dość ciężkie - zamiast
    eleganckich dopasowań do wzorca musimy ręcznie wpisywać argumenty do
    reguły indukcyjnej. *)

Require Import List.
Import ListNotations.

Definition toList'
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> list A |
    f snil = [] /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = h :: f t
  }.
Proof.
  exact (rec' (list A) [] cons).
Defined.

Definition toList
  {A : Type} {R : A -> A -> Prop} : slist R -> list A :=
    proj1_sig toList'.

(** Używanie takiego rekursora jest już dużo prostsze, co ilustruje powyższy
    przykład funkcji, która zapomina o tym, że lista jest posortowana i daje
    nam zwykłą listę.

    Przykładowe posortowane listy wyglądają tak: *)

Definition slist_01 : slist le :=
  scons 0
    (scons 1
      snil
      (ok_snil 1))
    (ok_scons 1 snil (ok_snil 1) 0 (le_S 0 0 (le_n 0))).

(** Niezbyt piękna, prawda? *)

Compute toList slist_01.

(** Utrapieniem jest też to, że nasza funkcja się nie oblicza. Jest tak, bo
    została zdefiniowana za pomocą reguły indukcji, która jest aksjomatem.
    Aksjomaty zaś, jak wiadomo, nie obliczają się.

    Wyniku powyższego wywołania nie będę nawet wklejał, gdyż jest naprawdę
    ohydny. *)

Lemma toList_slist_01_result :
  toList slist_01 = [0; 1].
Proof.
  unfold toList, slist_01.
  destruct toList' as (f & H1 & H2); cbn.
  rewrite 2!H2, H1. reflexivity.
Qed.

(** Najlepsze, co możemy osiągnąć, mając taką definicję, to udowodnienie, że
    jej wynik faktycznie jest taki, jak się spodziewamy. *)

(** **** Ćwiczenie *)

(** Zdefiniuj dla list posortowanych funkcję [slen], która liczy ich długość.
    Udowodnij oczywiste twierdzenie wiążące ze sobą [slen], [toList] oraz
    [length]. *)

(* begin hide *)

Definition slen'
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> nat |
    f snil = 0 /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = S (f t)}.
Proof.
  exact (rec' nat 0 (fun _ n => S n)).
Defined.

Definition slen {A : Type} {R : A -> A -> Prop} : slist R -> nat :=
  proj1_sig slen'.

Lemma slen_toList_length :
  forall {A : Type} {R : A -> A -> Prop} (l : slist R),
    slen l = length (toList l).
Proof.
  intros A R.
  eapply (projT1 (
    ind A R (fun l => slen l = length (toList l))
      (fun _ _ _ => True)
      _ _
      (fun _ => I)
      (fun _ _ _ _ _ _ _ => I))).
  Unshelve.
  all: cbn; unfold slen, toList;
  destruct slen' as (f & Hf1 & Hf2), toList' as (g & Hg1 & Hg2); cbn.
    rewrite Hf1, Hg1. cbn. reflexivity.
    intros. rewrite Hf2, Hg2, H. cbn. reflexivity.
Qed.

(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij, że przykład faktycznie jest bez sensu: zdefiniuje relację
    [sorted : (A -> A -> Prop) -> list A -> Prop], gdzie [sorted R l]
    oznacza, że lista [l] jest posortowana według porządku [R]. Używając
    [sorted] zdefiniuj typ list posortowanych [slist' R], a następnie znajdź
    dwie funkcje [f : slist R -> slist' R] i [f : slist' R -> slist R],
    które są swoimi odwrotnościami. *)

(* begin hide *)

Inductive sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
    | sorted_nil : sorted R []
    | sorted_singl : forall x : A, sorted R [x]
    | sorted_cons :
        forall (x y : A) (t : list A),
          R x y -> sorted R (y :: t) -> sorted R (x :: y :: t).

Arguments sorted_nil {A R}.
Arguments sorted_singl {A R} _.
Arguments sorted_cons {A R x y t} _ _.

Definition slist' {A : Type} (R : A -> A -> Prop) : Type :=
  {l : list A | sorted R l}.

Lemma toList_sorted :
  forall {A : Type} {R : A -> A -> Prop} (l : slist R),
    sorted R (toList l).
Proof.
  intros A R.
  refine (projT1 (ind
    A R
    (fun l => sorted R (toList l))
    (fun x t _ =>
      t = snil \/
      exists (h : A) (t' : slist R) (p : ok h t'),
        t = scons h t' p /\ R x h)
    _ _ _ _)).
  1-2: unfold toList; destruct toList' as (f & H1 & H2); cbn.
    rewrite H1. constructor.
    intros. rewrite H2. decompose [or ex and] H0; clear H0; subst.
      rewrite H1. constructor.
      rewrite H2 in *. constructor; assumption.
    intros. left. reflexivity.
    intros. decompose [or ex and] H1; clear H1; subst.
      right. exists h, snil, p. split; trivial.
      right. exists h, (scons x0 x1 x2), p. split; trivial.
Qed.

(** TODO *)

(* end hide *)

(** **** Ćwiczenie *)

(** Żeby przekonać się, że przykład był naprawdę bezsensowny, zdefiniuj
    rodzinę typów [blist : (A -> A -> Prop) -> A -> Type], gdzie elementami
    [blist R x] są listy posortowane, których elementy są [R]-większe od [x].
    Użyj [blist] do zdefiniowania typu [slist'' R], a następnie udowodnij,
    że [slist R] i [slist'' R] są sobie równoważne. *)

End ind_ind.

(** **** *)

(** Na koniec wypadałoby jeszcze wspomnieć, do czego tak naprawdę można w
    praktyce użyć indukcji-indukcji (definiowanie list posortowanych nie
    jest jedną z tych rzeczy, o czym przekonałeś się w ćwiczeniach). Otóż
    najciekawszym przykładem wydaje się być formalizacja teorii typów, czyli,
    parafrazując, implementacja Coqa w Coqu.

    Żeby się za to zabrać, musimy zdefiniować konteksty, typy i termy, a
    także relacje konwertowalności dla typów i termów. Są tutaj możliwe dwa
    podejścia:
    - Curry'ego (ang. Curry style lub mądrzej extrinsic style) - staramy
      się definiować wszystko osobno, a potem zdefiniować relacje "term x
      jest typu A w kontekście Γ", "typ A jest poprawnie sformowany w
      kontekście Γ" etc. Najważniejszą cechą tego sposobu jest to, że
      możemy tworzyć termy, którym nie da się przypisać żadnego typu oraz
      typy, które nie są poprawnie sformowane w żadnym kontekście.
    - Churcha (ang. Church style lub mądrzej intrinsic style) - definiujemy
      wszystko na raz w jednej wielkiej wzajemnej indukcji. Zamiastów
      typów definiujemy od razu predykat "typ A jest poprawnie sformowany
      w kontekście Γ", a zamiast termów definiujemy od razu relację
      "term x ma typ A w kontekście Γ". Parafrazując - wszystkie termy,
      które jesteśmy w stanie skonstruować, są poprawnie typowane (a
      wszystkie typy poprawnie sformowane w swoich kontekstach). *)

(** Zamiast tyle gadać zobaczmy, jak mogłoby to wyglądać w Coqu. Oczywiście
    będą to same nagłówki, bo podanie tutaj pełnej definicji byłoby mocno
    zaciemniającym przegięciem. *)

(*
Inductive Ctx : Type := ...

with Ty : Ctx -> Type := ...

with Term : forall Γ : Ctx, Ty Γ -> Type := ...

with TyConv : forall Γ : Ctx, Ty Γ -> Ty Γ -> Prop := ...

with
  TermConv :
    forall (Γ : Ctx) (A : Ty Γ),
      Term Γ A -> Term Γ A -> Prop := ...
*)

(** Nagłówki w tej definicji powinniśmy interpretować tak:
    - [Ctx] to typ reprezentujący konteksty.
    - [Ty] ma reprezentować typy, ale nie jest to typ, lecz rodzina typów
      indeksowana kontekstami - każdy typ jest typem w jakimś kontekście,
      np. [list A] jest typem w kontekście zawierającym [A : Type], ale
      nie jest typem w pustym kontekście.
    - [Term] ma reprezentować termy, ale nie jest to typ, lecz rodzina typów
      indeksowana kontekstami i typami - każdy term ma jakiś typ, a typy,
      jak już się rzekło, zawsze są typami w jakimś kontekście. Przykład:
      jeżeli [x] jest zmienną, to [cons x nil] jest typu [list A] w
      kontekście, w którym [x] jest typu [A], ale nie ma żadnego typu (i nie
      jest nawet poprawnym termem) w kontekście pustym ani w żadnym, w którym
      nie występuje [x].
    - [TyConv Γ A B] zachodzi, gdy typy [A] i [B] są konwertowalne, czyli
      obliczają się do tego samego (relacja taka jest potrzebna, gdyż w Coqu
      i ogólnie w teorii typów występować mogą takie typy jak [if true then
      nat else bool], który jest konwertowalny z [nat]). Jako się rzekło,
      typy zawsze występują w kontekście, więc konwertowalne mogą być też
      tylko w kontekście.
    - [TermConv Γ A x y] znaczy, że termy [x] i [y] są konwertowalne,
      np. [if true then 42 else 0] jest konwertowalne z [42]. Ponieważ każdy
      term ciągnie za sobą swój typ, [TermConv] ma jako indeks typ [A], a
      ponieważ typ ciągnie za sobą kontekst, indeksem [TermConv] jest także
      [Γ]. *)

(** Jak widać, indukcji-indukcji jest w powyższym przykładzie na pęczki -
    jest ona wręcz teleskopowa, gdyż [Ctx] jest indeksem [Ty], [Ctx] i [Ty]
    są indeksami [Term], a [Ctx], [Ty] i [Term] są indeksami [TermConv].

    Cóż, to by było na tyle w tym temacie. Ława oburzonych wyraża w tym
    momencie swoje najwyższe oburzenie na brak indukcji-indukcji w Coqu:
    https://www.sadistic.pl/lawa-oburzonych-vt22270.htm

    Jednak uszy do góry - istnieją już języki, które jakoś sobie radzą z
    indukcją-indukcją. Jednym z nich jest wspomniana we wstępie Agda,
    którą można znaleźć tu:
    https://agda.readthedocs.io/en/latest/ *)

(** **** Ćwiczenie *)

(** Typ stert binarnych [BHeap R], gdzie [R : A -> A -> Prop] jest relacją
    porządku, składa się z drzew, które mogą być albo puste, albo być węzłem
    przechowującym wartość [v : A] wraz z dwoma poddrzewami [l r : BHeap R],
    przy czym [v] musi być [R]-większe od wszystkich elementów [l] oraz [r].

    Użyj indukcji-indukcji, żeby zdefiniować jednocześnie typ [BHeap R] oraz
    relację [ok], gdzie [ok v h] zachodzi, gdy [v] jest [R]-większe od
    wszystkich elementów [h].

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie sterty [h : BHeap R]. Wskazówka:
    prawdopodobnie nie uda ci się zdefiniować [mirror]. Zastanów się,
    dlaczego jest tak trudno. *)

(* begin hide *)

Module BHeap.

Fail

Inductive BHeap {A : Type} (R : A -> A -> Prop) : Type :=
    | E : BHeap R
    | N : forall (v : A) (l r : BHeap R), ok v l -> ok v r -> BHeap R

with ok {A : Type} {R : A -> A -> Prop} : A -> BHeap R -> Prop :=
    | ok_E : forall v : A, ok v E
    | ok_N :
        forall (v x : A) (l r : BHeap A) (pl : ok x l) (pr : ok x r),
          R x v -> ok v (N x l r pl pr).

Axioms
  (BHeap : forall {A : Type} (R : A -> A -> Prop), Type)
  (ok : forall {A : Type} {R : A -> A -> Prop}, A -> BHeap R -> Prop)
  (E : forall {A : Type} {R : A -> A -> Prop}, BHeap R)
  (N :
    forall
      {A : Type} {R : A -> A -> Prop}
      (v : A) (l r : BHeap R),
        ok v l -> ok v r -> BHeap R)
  (ok_E : forall {A : Type} {R : A -> A -> Prop} (v : A), ok v (@E _ R))
  (ok_N :
    forall
      {A : Type} {R : A -> A -> Prop}
      (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r),
        R x v -> ok v (N x l r pl pr))
  (ind : forall
    (A : Type) (R : A -> A -> Prop)
    (P : BHeap R -> Type)
    (Q : forall (v : A) (h : BHeap R), ok v h -> Type)
    (PE : P E)
    (PN : forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
            P l -> P r -> Q v l pl -> Q v r pr -> P (N v l r pl pr))
    (Qok_E :
      forall v : A, Q v E (ok_E v))
    (Qok_N :
      forall
        (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r) (H : R x v),
          P l -> P r -> Q x l pl -> Q x r pr ->
            Q v (N x l r pl pr) (ok_N v x l r pl pr H)),
    {f : forall h : BHeap R, P h &
    {g : forall (v : A) (h : BHeap R) (p : ok v h), Q v h p |
      f E = PE /\
      (forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
        f (N v l r pl pr) =
        PN v l r pl pr (f l) (f r) (g v l pl) (g v r pr)) /\
      (forall v : A, g v E (ok_E v) = Qok_E v) /\
      (forall
        (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r) (H : R x v),
          g v (N x l r pl pr) (ok_N v x l r pl pr H) =
          Qok_N v x l r pl pr H (f l) (f r) (g x l pl) (g x r pr))
    }}).

(*
Definition mirror
  {A : Type} {R : A -> A -> Prop}
  :
  {f : BHeap R -> BHeap R &
  {g : forall {v : A} {h : BHeap R}, ok v h -> ok v (f h) |
    f E = E /\
    (forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
      f (N v l r pl pr) = N v (f r) (f l) (g v r pr) (g v l pl)) /\
    (forall v : A, g v E (ok_E v) = ok_E v)
  }}.
Proof.
  Check (
    ind
      A R
      (fun _ => BHeap R)). 
      (fun _ _ _ => True)
      E (fun v _ _ _ _ l' r' pl' pr' => N v r' l' pr' pl')
      (fun _ => I) (fun _ _ _ _ _ _ _ _ _ _ _ => I)
  ).
*)

End BHeap.

(* end hide *)

(** **** Ćwiczenie *)

(** Typ drzew wyszukiwań binarnych [BST R], gdzie [R : A -> A -> Prop] jest
    relacją porządku, składa się z drzew, które mogą być albo puste, albo być
    węzłem przechowującym wartość [v : A] wraz z dwoma poddrzewami
    [l r : BST R], przy czym [v] musi być [R]-większe od wszystkich elemtnów
    [l] oraz [R]-mniejsze od wszystkich elementów [r].

    Użyj indukcji-indukcji, żeby zdefiniować jednocześnie typ [BST R] wraz
    z odpowiednimi relacjami zapewniającymi poprawność konstrukcji węzła.
    Wypróbuj trzy podejścia:
    - jest jedna relacja, [oklr], gdzie [oklr v l r] oznacza, że z [v], [l] i
      [r] można zrobić węzeł
    - są dwie relacje, [okl] i [okr], gdzie [okl v l] oznacza, że [v] jest
      [R]-większe od wszystkich elementów [l], zaś [okr v r], że [v] jest
      [R]-mniejsze od wszystkich elementów [r]
    - jest jedna relacja, [ok], gdzie [ok v t] oznacza, że [v] jest
      [R]-mniejsze od wszystkich elementów [t] *)

(** Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie drzewa [t : BST R]. Wskazówka:
    dość możliwe, że ci się nie uda. *)

(* begin hide *)

(** TODO: przetłumacz na odpowiedni zestaw aksjomatów, zdefiniuj mirror *)

Module BST.

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
    | E : BST R
    | N : forall (v : A) (l r : BST R), ok v l r -> BST R

with ok {A : Type} {R : A -> A -> Prop} : A -> BST R -> BST R -> Prop :=
    | ok_EE : forall v : A, ok v E E
    | ok_EN :
        forall (v vl : A) (ll lr : BST R),
          R vl v -> ok v (N vl ll lr) E
    | ok_NE :
        forall (v vr : A) (rl rr : BST R),
          R v vr -> ok v E (N vr rl rr)
    | ok_NN :
        forall (v vl vr : A) (ll lr rl rr : BST R),
          R vl v -> R v vr -> ok v (N vl ll lr) (N vr rl rr).

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
    | E : BST R
    | N : forall (v : A) (l r : BST R), okl v l -> okr v r -> BST R

with okl {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
    | okl_E : forall v : A, okl v E
    | okl_N :
        forall (v vl : A) (ll lr : BST R),
          R vl v -> okl v (N vl ll lr)

with okr {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
    | okr_E : forall v : V, okr v E
    | okr_N :
        forall (v vr : A) (rl rr : BST R),
          R v vr -> okr v (N vr rl rr).

Definition inv {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => R y x.

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
    | E : BST R
    | N : forall (v : A) (l r : BST R),
            @ok A R v l -> @ok A (inv R) v r -> BST R

with ok {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
    | ok_E : forall v : A, ok v E
    | ok_N :
        forall (v x : A) (l r : BST R),
          R x v -> ok v (N x l r).

End BST.

(* end hide *)

(** ** Indukcja-rekursja *)

Module ind_rec.

(** A oto kolejny potfur do naszej kolekcji: indukcja-rekursja. Nazwa, choć
    brzmi tak głupio, jak "indukcja-indukcja", niesie ze sobą jednak dużo
    więcej wyobraźni: indukcja-rekursja pozwala nam jednocześnie definiować
    typy induktywne oraz operujące na nich funkcje rekurencyjne.

    Co to dokładnie znaczy? Dotychczas nasz modus operandi wyglądał tak, że
    najpierw definiowaliśmy jakiś typ induktywny, a potem przez rekursję
    definiowaliśmy operujące na nim funkcje, np:
    - najpierw zdefiniowaliśmy typ [nat], a potem dodawanie, mnożenie etc.
    - najpierw zdefiniowaliśmy typ [list A], a potem [app], [rev] etc. *)

(** Dlaczego mielibyśmy chcieć definiować typ i funkcję jednocześnie? Dla
    tego samego, co zawsze, czyli zależności - indukcja-rekursja pozwala,
    żeby definicja typu odnosiła się do funkcji, która to z kolei jest
    zdefiniowana przez rekursję strukturalną po argumencie o tym typie.

    Zobaczmy dobrze nam już znany bezsensowny przykład, czyli listy
    posortowane, tym razem zaimplementowane za pomocą indukcji-rekursji. *)

(*
Inductive slist {A : Type} (R : A -> A -> bool) : Type :=
    | snil : slist R
    | scons :
        forall (h : A) (t : slist R), ok h t = true -> slist R

with

Definition ok
  {A : Type} {R : A -> A -> bool} (x : A) (t : slist R) : bool :=
match t with
    | snil => true
    | scons h _ _ => R x h
end.
*)

(** Coq niestety nie wspiera indukcji-rekursji, a próba napisania powyższej
    definicji kończy się błędem składni, przy którym nie pomaga nawet komenda
    [Fail]. Podobnie jak poprzednio, pomożemy sobie za pomocą aksjomatów,
    jednak najpierw prześledźmy definicję.

    Typ slist działa następująco:
    - [R] to jakiś porządek. Zauważ, że tym razem [R : A -> A -> bool], a
      więc porządek jest reprezentowany przez funkcję, która go rozstrzyga
    - [snil] to lista pusta
    - [scons h t p] to lista z głową [h] i ogonem [t], zaś [p : ok h t = true]
      to dowód na to, że dostawienie [h] przed [t] daje listę posortowaną. *)

(** Tym razem jednak [ok] nie jest relacją, lecz funkcją zwracającą [bool],
    która działa następująco:
    - dla [snil] zwróć [true] - każde [x : A] można dostawić do listy pustej
    - dla [scons h _ _] zwróć wynik porównania [x] z [h] *)

(** Istotą mechanizmu indukcji-rekursji w tym przykładzie jest to, że [scons]
    wymaga dowodu na to, że funkcja [ok] zwraca [true], podczas gdy funkcja
    ta jest zdefiniowana przez rekursję strukturalną po argumencie typu
    [slist R].

    Użycie indukkcji-rekursji do zaimplementowania [slist] ma swoje zalety:
    dla konkretnych list (złożonych ze stałych, a nie ze zmiennych) dowody
    [ok h t = true] będą postaci [eq_refl], bo [ok] po prostu obliczy się
    do [true]. W przypadku indukcji-indukcji dowody na [ok h t] były całkiem
    sporych rozmiarów drzewami. Innymi słowy, udało nam się zastąpić część
    termu obliczeniami. Ten intrygujący motyw jeszcze się w przyszłości
    pojawi, gdy omawiać będziemy dowód przez reflekcję.

    Dosyć gadania! Zobaczmy, jak zakodować powyższą definicję za pomocą
    aksjomatów. *)

Axioms
  (slist : forall {A : Type}, (A -> A -> bool) -> Type)
  (ok :
    forall {A : Type} {R : A -> A -> bool}, A -> slist R -> bool)
  (snil :
    forall {A : Type} {R : A -> A -> bool}, slist R)
  (scons :
    forall
      {A : Type} {R : A -> A -> bool}
      (h : A) (t : slist R),
        ok h t = true -> slist R)
  (ok_snil :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      ok x (@snil _ R) = true)
  (ok_scons :
    forall
      {A : Type} {R : A -> A -> bool}
      (x h : A) (t : slist R) (p : ok h t = true),
        ok x (scons h t p) = R x h).

(** Najpierw musimy zadeklarować [slist], a następnie [ok], gdyż typ [ok]
    zależy od [slist]. Następnym krokiem jest zadeklarowanie konstruktorów
    [slist], a później równań definiujących funkcję [ok] - koniecznie w tej
    kolejności, gdyż równania zależą od konstruktorów.

    Jak widać, aksjomaty są bardzo proste i sprowadzają się do przepisania
    powyższej definicji odrzuconej przez Coqa. *)

Axiom
  ind : forall
    (A : Type) (R : A -> A -> bool)
    (P : slist R -> Type)
    (Psnil : P snil)
    (Pscons :
      forall (h : A) (t : slist R) (p : ok h t = true),
        P t -> P (scons h t p)),
    {f : forall l : slist R, P l |
      f snil = Psnil /\
      (forall (h : A) (t : slist R) (p : ok h t = true),
        f (scons h t p) = Pscons h t p (f t))}.

(** Innym zyskiem z użycia indukcji-rekursji jest postać reguły indukcyjnej.
    Jest ona dużo prostsza, niż w przypadku indukcji-indukcji, gdyż teraz
    definiujemy tylko jeden typ, zaś towarzysząca mu funkcja nie wymaga w
    regule niczego specjalnego - po prostu pojawia się w niej tam, gdzie
    spodziewamy się jej po definicji [slist], ale nie robi niczego
    ponad to. Może to sugerować, że zamiast indukcji-indukcji, o ile to
    możliwe, lepiej jest używać indukcji-rekursji, a predykaty i relacje
    definiować przez rekursję.

    Powyższą regułę możemy odczytać następująco:
    - [A : Type] i [R : A -> A -> bool] to parametry [slist], więc muszą się
      pojawić
    - [P : slist R -> Type] to przeciwdziedzina funkcji definiowanej za
      pomocą reguły
    - [Psnil] to wynik funkcji dla [snil]
    - [Pscons] produkuje wynik funkcji dla [scons h t p] z hipotezy
      indukcyjnej/wywołania rekurencyjnego dla [t]
    - [f : forall l : slist R, P l] to funkcja zdefiniowana przez regułę,
      zaś równania formalizują to, co zostało napisane powyżej o [Psnil]
      i [Pscons] *)

(** Termy induktywno-rekurencyjnego [slist R] wyglądają następująco
    (najpierw definiujemy sobie funkcję rozstrzygającą standardowy
    porządek na liczbach naturalnych): *)

Fixpoint leb (n m : nat) : bool :=
match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
end.

Definition slist_01 : slist leb :=
  scons 0
    (scons 1
      snil
      (ok_snil 1))
    (ok_scons 0 1 snil (ok_snil 1)).

(** Nie wygląda wiele lepiej od poprzedniej, induktywno-induktywnej wersji,
    prawda? Ta rażąca kiepskość nie jest jednak zasługą indukcji-rekursji,
    lecz kodowania za pomocą aksjomatów - funkcja [ok] się nie oblicza,
    więc zamiast [eq_refl] musimy używać aksjomatów [ok_snil] i [ok_scons].

    W tym momencie znów wkracza ława oburzonych i wyraża swoje oburzenie na
    fakt, że Coq nie wspiera indukcji-rekursji (ale Agda już tak). Gdyby
    [Coq] wspierał indukcję-rekursję, to ten term wyglądałby tak: *)

Fail Definition slist_01 : slist leb :=
  scons 0 (scons 1 snil eq_refl) eq_refl.

(** Dużo lepiej, prawda? Na koniec zobaczmy, jak zdefiniować funkcję
    zapominającą o fakcie, że lista jest posortowana. *)

Require Import List.
Import ListNotations.

Definition toList'
  {A : Type} {R : A -> A -> bool} :
  {f : slist R -> list A |
    f snil = [] /\
    forall (h : A) (t : slist R) (p : ok h t = true),
      f (scons h t p) = h :: f t
  }.
Proof.
  exact (ind A R (fun _ => list A) [] (fun h _ _ r => h :: r)).
Defined.

Definition toList
  {A : Type} {R : A -> A -> bool} : slist R -> list A :=
    proj1_sig toList'.

(** Ponownie jest to dużo prostsze, niż w przypadku indukcji-indukcji -
    wprawdzie wciąż musimy ręcznie wpisywać termy do reguły indukcji,
    ale dzięki prostocie reguły jest to znacznie łatwiejsze. Alternatywnie:
    udało nam się zaoszczędzić trochę czasu na definiowaniu reguły rekursji,
    co w przypadku indukcji-indukcji było niemal konieczne, żeby nie
    zwariować. *)

Lemma toList_slist_01_result :
  toList slist_01 = [0; 1].
Proof.
  unfold toList, slist_01.
  destruct toList' as (f & H1 & H2).
  cbn. rewrite 2!H2, H1. reflexivity.
Qed.

(** Udowodnienie, że nasza funkcja daje taki wynik jak chcieliśmy, jest
    równie proste jak poprzednio. *)

(** **** Ćwiczenie *)

(** Zdefiniuj dla list posortowanych funkcję [slen], która liczy ich długość.
    Udowodnij oczywiste twierdzenie wiążące ze sobą [slen], [toList] oraz
    [length]. Czy było łatwiej, niż w przypadku indukcji-indukcji? *)

(* begin hide *)

Definition slen'
  {A : Type} {R : A -> A -> bool} :
  {f : slist R -> nat |
    f snil = 0 /\
    forall (h : A) (t : slist R) (p : ok h t = true),
      f (scons h t p) = S (f t)}.
Proof.
  exact (ind A R (fun _ => nat) 0 (fun _ _ _ n => S n)).
Defined.

Definition slen {A : Type} {R : A -> A -> bool} : slist R -> nat :=
  proj1_sig slen'.

Lemma slen_toList_length :
  forall {A : Type} {R : A -> A -> bool} (l : slist R),
    slen l = length (toList l).
Proof.
  intros A R.
  eapply (proj1_sig
    (ind A R (fun l : slist R => slen l = length (toList l)) _ _)).
  Unshelve.
  all: cbn; unfold slen, toList;
  destruct slen' as (f & Hf1 & Hf2), toList' as (g & Hg1 & Hg2); cbn.
    rewrite Hf1, Hg1. cbn. reflexivity.
    intros. rewrite Hf2, Hg2, H. cbn. reflexivity.
Qed.

(** Czy było łatwiej, niż zrobić to samo indukcją-indukcją? Tak, ale tylko
    troszkę. *)

(* end hide *)

End ind_rec.

(** **** Ćwiczenie *)

(** No cóż, jeszcze raz to samo. Zdefiniuj za pomocą indukcji-rekursji
    jednocześnie typ stert binarnych [BHeap R], gdzie [R : A -> A -> bool]
    rozstrzyga porządek, i funkcję [ok : A -> BHeap R -> bool], gdzie
    [ok x h = true], gdy stertę [h] można podczepić pod element [x].

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie sterty [h : BHeap R]. Wskazówka:
    tym razem powinno ci się udać.

    Porównaj induktywno-rekurencyjną implementację [BHeap R] i [ok] z
    implementacją przez indukcję-indukcję. Która jest bardziej ogólna?
    Która jest "lżejsza"? Która jest lepsza? *)

(* begin hide *)
Module BHeap'.

(*
Inductive BHeap {A : Type} (R : A -> A -> bool) : Type :=
    | E : BHeap R
    | N :
      forall (v : A) (l r : BHeap R),
        ok R v l = true -> ok R v r = true -> BHeap R

with ok {A : Type} (R : A -> A -> bool) (x : A) (h : BHeap R) : bool :=
match h with
    | E => true
    | N v l r _ _ => R x v
end.
*)

Axioms
  (BHeap : forall {A : Type} (R : A -> A -> bool), Type)
  (ok : forall {A : Type} (R : A -> A -> bool) (x : A) (h : BHeap R), bool)
  (E : forall {A : Type} {R : A -> A -> bool}, BHeap R)
  (N :
    forall {A : Type} {R : A -> A -> bool} (v : A) (l r : BHeap R),
      ok R v l = true -> ok R v r = true -> BHeap R)
  (ok_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      ok R x E = true)
  (ok_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BHeap R)
      (eql : ok R v l = true) (eqr : ok R v r = true),
        ok R x (N v l r eql eqr) = R x v)
  (ind :
    forall
      {A : Type} {R : A -> A -> bool}
      (P : BHeap R -> Type)
      (P_E : P E)
      (P_N :
        forall
          (v : A) (l r : BHeap R)
          (eql : ok R v l = true) (eqr : ok R v r = true),
            P l -> P r -> P (N v l r eql eqr)),
      {f : forall h : BHeap R, P h |
        f E = P_E /\
        (forall
          (v : A) (l r : BHeap R)
          (eql : ok R v l = true) (eqr : ok R v r = true),
            f (N v l r eql eqr) = P_N v l r eql eqr (f l) (f r))}).

Definition mirror
  {A : Type} {R : A -> A -> bool} (h : BHeap R) :
  {h' : BHeap R | forall x : A, ok R x h' = ok R x h}.
Proof.
  revert h.
  apply (@ind A R (fun h : BHeap R =>
    {h' : BHeap R | forall x : A, ok R x h' = ok R x h}
  )).
    exists E. reflexivity.
    intros * [l' IHl'] [r' IHr']. eexists (N v r' l' _ _). Unshelve.
      Focus 2. rewrite IHr'. assumption.
      Focus 2. rewrite IHl'. assumption.
      intros. rewrite !ok_N. reflexivity.
Defined.

End BHeap'.
(* end hide *)

(** **** Ćwiczenie *)

(** No cóż, jeszcze raz to samo. Zdefiniuj za pomocą indukcji-rekursji
    jednocześnie typ drzew wyszukiwań binarnych [BST R], gdzie
    [R : A -> A -> bool] rozstrzyga porządek, oraz funkcje
    [oklr]/[okl] i [okr]/[ok], które dbają o odpowiednie warunki (wybierz
    tylko jeden wariant z trzech, które testowałeś w tamtym zadaniu).

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie drzewa [t : BST R]. Wskazówka:
    tym razem powinno ci się udać.

    Porównaj induktywno-rekurencyjną implementację [BST R] z implementacją
    przez indukcję-indukcję. Która jest bardziej ogólna? Która jest
    "lżejsza"? Która jest lepsza? *)

(* begin hide *)
Module BST'.

(** TODO: definicja chyba jest źle... *)

(*
Inductive BST {A : Type} (R : A -> A -> bool) : Type :=
  | E : BST R
  | N : forall (v : A) (l r : BST R),
          okl R v l = true -> okr R v l = true -> BST R

with okl {A : Type} (R : A -> A -> bool) (x : A) (t : BST R) : bool :=
match t with
  | E => true
  | N v _ _ _ _ => R x v
end

with okr {A : Type} (R : A -> A -> bool) (x : A) (t : BST R) : bool :=
match t with
  | E => true
  | N v _ _ _ _ => negb (R x v)
*)

Axioms
  (BST : forall {A : Type} (R : A -> A -> bool), Type)
  (okl : forall {A : Type} {R : A -> A -> bool} (x : A) (t : BST R), bool)
  (okr : forall {A : Type} {R : A -> A -> bool} (x : A) (t : BST R), bool)
  (E : forall {A : Type} {R : A -> A -> bool}, BST R)
  (N :
    forall
      {A : Type} {R : A -> A -> bool}
      (v : A)
      (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true), BST R)
  (okl_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      okl x (@E A R) = true)
  (okl_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true),
        okl x (N v l r eql eqr) = R x v)
  (okr_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      okr x (@E A R) = true)
  (okr_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true),
        okr x (N v l r eql eqr) = negb (R x v))
  (ind :
    forall
      {A : Type} {R : A -> A -> bool}
      (P : BST R -> Type)
      (P_E : P E)
      (P_N :
        forall
          (v : A) (l r : BST R)
          (eql : okl v l = true) (eqr : okr v r = true),
            P l -> P r -> P (N v l r eql eqr)),
      {f : forall t : BST R, P t |
        f E = P_E /\
        forall
          (v : A) (l r : BST R)
          (eql : okl v l = true) (eqr : okr v r = true),
            f (N v l r eql eqr) = P_N v l r eql eqr (f l) (f r)
      }
  ).

Definition mirror
  {A : Type} {R : A -> A -> bool} (t : BST R) :
    {t' : BST (fun x y : A => negb (R x y)) |
      (forall x : A, okl x t' = okr x t) /\
      (forall x : A, okr x t' = okl x t)}.
Proof.
  revert t.
  apply (@ind A R (fun t : BST R =>
    {t' : BST (fun x y : A => negb (R x y)) |
      (forall x : A, okl x t' = okr x t) /\
      (forall x : A, okr x t' = okl x t)
    }
  )).
    exists E. split; intro; rewrite !okl_E, !okr_E; reflexivity.
    intros v l r eql eqr (l' & IHl1 & IHl2) (r' & IHr1 & IHr2).
      eexists (N v r' l' _ _). Unshelve.
        Focus 2. rewrite IHr1, eqr. reflexivity.
        Focus 2. rewrite IHl2, eql. reflexivity.
        split; intro; rewrite okl_N, okr_N.
          reflexivity.
          destruct (R x v); reflexivity.
Defined.

End BST'.
(* end hide *)

(** Podobnie jak poprzednio, pojawia się pytanie: do czego w praktyce
    można użyć indukcji-rekursji (poza rzecz jasna głupimi strukturami
    danych, jak listy posortowane)? W świerszczykach dla bystrzaków
    (czyli tzw. "literaturze naukowej") przewija się głównie jeden (ale
    jakże użyteczny) pomysł: uniwersa.

    Czym są uniwersa i co mają wspólnego z indukcją-rekursją? Najlepiej
    będzie przekonać się na przykładzie programowania generycznego: *)

(** **** Ćwiczenie (zdecydowanie za trudne) *)

(** Zaimplementuj generyczną funkcję [flatten], która spłaszcza dowolnie
    zagnieżdżone listy list do jednej, płaskiej listy.

    [flatten 5 = [5]]

    [flatten [1; 2; 3] = [1; 2; 3]]

    [flatten [[1]; [2]; [3]] = [1; 2; 3]]

    [flatten [[[1; 2]]; [[3]]; [[4; 5]; [6]]] = [1; 2; 3; 4; 5; 6]] *)

(** Trudne, prawda? Ale robialne, a robi się to tak.

    W typach argumentów [flatten] na powyższym przykładzie widać pewien
    wzorzec: są to kolejno [nat], [list nat], [list (list nat)],
    [list (list (list nat))] i tak dalej. Możemy ten "wzorzec" bez problemu
    opisać za pomocą następującego typu: *)

Inductive FlattenType : Type :=
    | Nat : FlattenType
    | List : FlattenType -> FlattenType.

(** Żeby było śmieszniej, [FlattenType] to dokładnie to samo co [nat], ale
    przemilczmy to. Co dalej? Możemy myśleć o elementach [FlattenType] jak
    o kodach prawdziwych typów, a skoro są to kody, to można też napisać
    funkcję dekodującą: *)

Fixpoint decode (t : FlattenType) : Type :=
match t with
    | Nat => nat
    | List t' => list (decode t')
end.

(** [decode] każdemu kodowi przyporządkowuje odpowiadający mu typ. O
    kodach możemy myśleć jak o nazwach - [Nat] to nazwa [nat], zaś
    [List t'] to nazwa typu [list (decode t')], np. [List (List Nat)]
    to nazwa typu [list (list nat)].

    Para [(FlattenType, decode)] jest przykładem uniwersum.

    Uniwersum to, najprościej pisząc, worek, który zawiera jakieś typy.
    Formalnie uniwersum składa się z typu kodów (czyli "nazw" typów) oraz
    funkcji dekodującej, która przyporządkowuje kodom prawdziwe typy.

    Programowanie generyczne to programowanie funkcji, które operują na
    kolekcjach typów o dowolnych kształtach, czyli na uniwersach właśnie.
    Generyczność od polimorfizmu różni się tym, że funkcja polimorficzna
    działa dla dowolnego typu, zaś generyczna - tylko dla typu o pasującym
    kształcie.

    Jak dokończyć implementację funkcji [flatten]? Kluczowe jest zauważenie,
    że możemy zdefiniować [flatten] przez rekursję strutkuralną po argumencie
    domyślnym typu [FlattenType]. Ostatni problem to jak zrobić, żeby Coq sam
    zgadywał kod danego typu - dowiemy się tego w rozdziale o klasach.

    Co to wszystko ma wspólnego z uniwersami? Ano, jeżeli chcemy definiować
    bardzo zaawansowane funkcje generyczne, musimy mieć do dyspozycji bardzo
    potężne uniwersa i to właśnie je zapewnia nam indukcja-rekursja. Ponieważ
    w powyższym przykładzie generyczność nie była zbyt wyrafinowana, nie było
    potrzeby używania indukcji-rekursji, jednak uszy do góry: przykład nieco
    bardziej skomplikowanego uniwersum pojawi się jeszcze w tym rozdziale. *)

(** **** Ćwiczenia *)

(** Nieco podchwytliwe zadanie: zdefiniuj uniwersum funkcji [nat -> nat],
    [nat -> (nat -> nat)], [(nat -> nat) -> nat],
    [(nat -> nat) -> (nat -> nat)] i tak dalej, dowolnie zagnieżdżonych.

    Zagadka: czy potrzebna jest nam indukcja-rekursja? *)

(** ** Indeksowana indukcja-rekursja *)

(** Za siedmioma górami, za siedmioma lasami, za siedmioma rzekami, za
    siedmioma budkami telefonicznymi, nawet za indukcją-rekursją (choć
    tylko o kroczek) leży indeksowana indukcja-rekursja, czyli połączenie
    indukcji-rekursji oraz indeksowanych rodzin typów.

    Jako, że w porównaniu do zwykłej indukcji-rekursji nie ma tu za wiele
    innowacyjności, przejdźmy od razu do przykładu przydatnej techniki,
    którą nasza tytułowa bohaterka umożliwia, a zwie się on metodą
    induktywnej dziedziny.

    Pod tą nazwą kryje się sposób definiowania funkcji, pozwalający oddzielić
    samą definicję od dowodu jej terminacji. Jeżeli ten opis nic ci nie mówi,
    nie martw się: dotychczas definiowaliśmy tylko tak prymitywne funkcje, że
    tego typu fikołki nie były nam potrzebne.

    Metoda induktywnej dziedziny polega na tym, żeby zamiast funkcji
    [f : A -> B], która nie jest strukturalnie rekurencyjna (na co Coq
    nie pozwala) napisać funkcję [f : forall x : A, D x -> B], gdzie
    [D : A -> Type] jest "predykatem dziedziny", który sprawia, że dziwna
    rekursja z oryginalnej definicji [f] staje się rekursją strukturalną
    po dowodzie [D x]. Żeby zdefiniować oryginalne [f : A -> B] wystarczy
    udowodnić, że każde [x : A] spełnia predykat dziedziny.

    Co to wszystko ma wspólnego z indeksowaną indukcją-rekursją? Już piszę.
    Otóż metoda ta nie wymaga w ogólności indukcji-rekursji - ta staje się
    potrzebna dopiero, gdy walczymy z bardzo złośliwymi funkcjami, czyli
    takimi, w których rekursja jest zagnieżdżona, tzn. robimy wywołanie
    rekurencyjne na wyniku poprzedniego wywołania rekurencyjnego.

    Predykat dziedziny dla takiej funkcji musi zawierać konstruktor w stylu
    "jeżeli wynik wywołania rekurencyjnego na x należy do dziedziny, to x też
    należy do dziedziny".To właśnie tu ujawnia się indukcja-rekursja: żeby
    zdefiniować predykat dziedziny, musimy odwołać się do funkcji (żeby móc
    powiedzieć coś o wyniku wywołania rekurencyjnego), a żeby zdefiniować
    funkcję, musimy mieć predykat dziedziny.

    Brzmi skomplikowanie? Jeżeli czegoś nie rozumiesz, to jesteś debi...
    a nie, czekaj. Jeżeli czegoś nie rozumiesz, to nie martw się: powyższy
    przykład miał na celu jedynie zilustrować jakieś praktyczne zastosowanie
    indeksowanej indukcji-rekursji. Do metody induktywnej dziedziny powrócimy
    w kolejnym rozdziale. Pokażemy, jak wyeliminować z niej indukcję-rekursję,
    tak żeby uzyskane za jej pomocą definicje można było odpalać w Coqu.
    Zobaczymy też, jakimi sposobami dowodzić, że każdy element dziedziny
    spełnia predykat dziedziny, co pozwoli nam odzyskać oryginalną definicję
    funkcji, a także dowiemy się, jak z "predykatu" o typie [D : A -> Type]
    zrobić prawdziwy predykat [D : A -> Prop]. *)

(** ** Indukcja-indukcja-rekursja *)

(** Ufff... przebrnęliśmy przez indukcję-indukcję i (indeksowaną)
    indukcję-rekursję. Czy mogą istnieć jeszcze potężniejsze i bardziej
    innowacyjne sposoby definiowania typów przez indukcję?

    Ależ oczywiście. Jest nim... uwaga uwaga, niespodzianka...
    indukcja-indukcja-rekursja, która jest nie tylko strasznym
    potfurem, ale też powinna dostać Oskara za najlepszą nazwę.

    Chodzi tu oczywiście o połączenie indukcji-indukcji i indukcji-rekursji:
    możemy jednocześnie zdefiniować jakiś typ [A], rodzinę typów [B]
    indeksowaną przez [A] oraz operujące na nich funkcje, do których
    konstruktory [A] i [B] mogą się odwoływać.

    Nie ma tu jakiejś wielkiej filozofii: wszystkiego, co powinieneś wiedzieć
    o indukcji-indukcji-rekursji, dowiedziałeś się już z dwóch poprzednich
    podrozdziałów. Nie muszę chyba dodawać, że ława oburzonych jest oburzona
    faktem, że Coq nie wspiera indukcji-indukcji-rekursji.

    Rodzi się jednak to samo super poważne pytanie co zawsze, czyli do czego
    można tego tałatajstwa użyć? Przez całkiem długi czas nie miałem pomysłu,
    ale okazuje się, że jest jedno takie zastosowanie i w sumie narzuca się
    ono samo.

    Przypomnij sobie metodę induktywno-rekurencyjnej dziedziny, czyli jedno
    ze sztandarowych zastosowań indeksowanej indukcji-rekursji. Zaczynamy od
    typu [I : Type], na którym chcemy zdefiniować funkcję o niestandardowym
    kształcie rekursji. W tym celu definiujemy dziedzinę [D : I -> Type]
    wraz z funkcją [f : forall i : I, D i -> R].

    Zauważmy, jaki jest związek typu [I] z funkcją [f]: najpierw jest typ,
    potem funkcja. Co jednak, gdy musimy [I] oraz [f] zdefiniować razem za
    pomocą indukcji-rekursji? Wtedy [f] może być zdefiniowane jedynie za
    pomocą rekursji strukturalnej po [I], co wyklucza rekursję o fikuśnym
    kształcie...

    I tu wchodzi indukcja-indukcja-rekursja, cała na biało. Możemy użyć
    jej w taki sposób, że definiujemy jednocześnie:
    - typ [I], który odnosi się do funkcji [f]
    - predykat dziedziny [D : I -> Type], który jest indeksowany przez [I]
    - funkcję [f], która zdefiniowana jest przez rekursję strukturalną po
      dowodzie należenia do dziedziny

    Jak widać, typ zależy od funkcji, funkcja od predykatu, a predykat od
    typu i koło się zamyka.

    Następuje jednak skądinąd uzasadnione pytanie: czy faktycznie istnieje
    jakaś sytuacja, w której powyższy schemat działania jest tym słusznym?
    Odpowiedź póki co może być tylko jedna: nie wiem, ale się domyślam. *)

(** ** Najstraszniejszy potfur *)

(** Na koniec dodam jeszcze na zachętę (albo zniechętę, zależy jakie kto
    ma podejście), że istnieje jeszcze jeden potfur, straszniejszy nawet
    niż indukcja-indukcja-rekursja, ale jest on zbyt straszny jak na ten
    rozdział i być może w ogóle zbyt straszny jak na tę książkę - panie
    boże, daj odwagę na omówienie go! *)

(** * Dobre, złe i podejrzane typy induktywne *)

(** Poznana przez nas dotychczas definicja typów induktywnych (oraz wszelkich
    ich ulepszeń, jak indukcja-indukcja, indukcja-rekursja etc.) jest
    niepełna. Tak jak świat pełen jest złoczyńców oszukujących starszych
    ludzi metodą "na wnuczka", tak nie każdy typ podający się za induktywny
    faktycznie jest praworządnym obywatelem krainy typów induktywnych. *)

(** Na szczęście typy induktywne to istoty bardzo prostolinijne, zaś te złe
    można odróżnić od tych dobrych gołym okiem, za pomocą bardzo prostego
    kryterium: złe typy induktywne to te, które nie są ściśle pozytywne.
    Zanim jednak dowiemy się, jak rozpoznawać złe typy, poznajmy najpierw
    dwa powody, przez które złe typy induktywne są złe. *)

(** ** Nieterminacja jako źródło zła na świecie *)

(** Przyjrzyjmy się poniższemu typowemu przypadkowi negatywnego typu
    induktywnego (czyli takiego, który wygląda na induktywny, ale ma
    konstruktory z negatywnymi wystąpieniami argumentu indukcyjnego): *)

Fail Inductive wut (A : Type) : Type :=
    | C : (wut A -> A) -> wut A.

(* ===> The command has indeed failed with message:
        Non strictly positive occurrence of "wut"
        in "(wut A -> A) -> wut A". *)

(** Uwaga: poprzedzenie komendą [Fail] innej komendy oznajmia Coqowi, że
    spodziewamy się, iż komenda zawiedzie. Coq akceptuje komendę [Fail c],
    jeżeli komenda [c] zawodzi, i wypisuje komunikat o błędzie. Jeżeli
    komenda [c] zakończy się sukcesem, komenda [Fail c] zwróci błąd.
    Komenda [Fail] jest przydatna w sytuacjach takich jak obecna, gdy
    chcemy zilustrować fakt, że jakaś komenda zawodzi.

    Pierwszym powodem nielegalności nie-ściśle-pozytywnych typów induktywnych
    jest to, że unieważniają one filozoficzną interpretację teorii typów i
    ogólnie wszystkiego, co robimy w Coqu. W praktyce problemy filozoficzne
    mogą też prowadzić do sprzeczności.

    Załóżmy, że Coq akceptuje powyższą definicję [wut]. Możemy wtedy napisać
    następujący program: *)

Fail Definition loop (A : Type) : A :=
  let f (w : wut A) : A :=
    match w with
        | C g => g w
    end
  in f (C f).

(** Już sam typ tego programu wygląda podejrzanie: dla każdego typu [A]
    zwraca on element typu [A]. Nie dziwota więc, że możemy uzyskać z niego
    dowód fałszu. *)

Fail Definition santa_is_a_pedophile : False := loop False.

(** Paradoksalnie jednak to nie ta rażąca sprzeczność jest naszym największym
    problemem - nie z każdego złego typu induktywnego da się tak łatwo dostać
    sprzeczność (a przynajmniej ja nie umiem; systematyczny sposób dostawania
    sprzeczności z istnienia takich typów zobaczymy później). W rzeczywistości
    jest nim nieterminacja.

    Nieterminacja (ang. nontermination, divergence) lub kolokwialniej
    "zapętlenie" to sytuacja, w której program nigdy nie skończy się
    wykonywać. Ta właśnie bolączka jest przypadłością [loop], czego nie
    trudno domyślić się z nazwy.

    Dlaczego tak jest? Przyjrzyjmy się definicji [loop]. Za pomocą [let]a
    definiujemy funkcję [f : wut A -> A], która odpakowuje swój argument
    [w], wyciąga z niego funkcję [g : wut A -> A] i aplikuje [g] do [w].
    Wynikiem programu jest [f] zaaplikowane do siebie samego zawiniętego
    w konstruktor [C].

    Przyjrzyjmy się, jak przebiegają próby wykonania tego nieszczęsnego
    programu:

    [loop A =]

    [let f := ... in f (C f) =]

    [let f := ... in match C f with | C g => g (C f) end =]

    [let f := ... in f (C f)]

    i tak dalej.

    Nie powinno nas to dziwić - praktycznie rzecz biorąc aplikujemy [f] samo
    do siebie, zaś konstruktor [C] jest tylko pośrednikiem sprawiającym, że
    typy się zgadzają. Ogólniej sytuacja, w której coś odnosi się samo do
    siebie, nazywa się autoreferencją i często prowadzi do różnych wesołych
    paradoksów. *)

(** **** Ćwiczenie *)

(** Poniższą zagadkę pozwolę sobie wesoło nazwać "paradoks hetero". Zagadka
    brzmi tak:

    Niektóre słowa opisują same siebie, np. słowo "krótki" jest krótkie,
    a niektóre inne nie, np. słowo "długi" nie jest długie. Podobnie słowo
    "polski" jest słowem polskim, ale słowo "niemiecki" nie jest słowem
    niemieckim. Słowa, które nie opisują samych siebie będziemy nazywać
    słowami heterologicznymi. Pytanie: czy słowo "heterologiczny" jest
    heterologiczne? *)

(** Czujesz sprzeczność? Innym przyk... dobra, wystarczy tych głupot.

    Przyjrzyjmy się teraz problemom filozoficznym powodowanym przez
    nieterminację. W skrócie: zmienia ona fundamentalne właściwości
    obliczeń, co prowadzi do zmiany interpretacji pojęcia typu, zaś
    to pociąga za sobą kolejne przykre skutki, takie jak np. to, że
    reguły eliminacji tracą swoje uzasadnienie.

    Brzmi mega groźnie, prawda? Kiedy wspomniałem o tym Sokratesowi, to
    sturlał się z podłogi na sufit bez pośrednictwa ściany.

    Na szczęście tak naprawdę, to sprawa jest prosta. W Coqu wymagamy, aby
    każde obliczenie się kończyło. Wartości, czyli końcowe wyniki obliczeń
    (które są też nazywane postaciami kanonicznymi albo normalnymi), możemy
    utożsamiać z elementami danego typu. Dla przykładu wynikami obliczania
    termów typu [bool] są [true] i [false], więc możemy myśleć, że są to
    elementy typu [bool] i [bool] składa się tylko z nich. To z kolei daje
    nam uzasadnienie reguły eliminacji (czyli indukcji) dla typu [bool]:
    żeby udowodnić [P : bool -> Prop] dla każdego [b : bool], wystarczy
    udowodnić [P true] i [P false], gdyż [true] i [false] są jedynymi
    elementami typu [bool].

    Nieterminacja obraca tę jakże piękną filozoficzną wizję w perzynę:
    nie każde obliczenie się kończy, a przez to powstają nowe, "dziwne"
    elementy różnych typów. [loop bool] nigdy nie obliczy się do [true] ani
    do [false], więc możemy traktować je jako nowy element typu [bool]. To
    sprawia, że [bool], typ z założenia dwuelementowy, ma teraz co najmniej
    trzy elementy - [true], [false] i [loop bool]. Z tego też powodu reguła
    eliminacji przestaje obowiązywać, bo wymaga ona dowodów jedynie dla
    [true] i [false], ale milczy na temat [loop bool]. Moglibyśmy próbować
    naiwnie ją załatać, uwzględniając ten dodatkowy przypadek, ale tak po
    prawdzie, to nie wiadomo nawet za bardzo jakie jeszcze paskudztwa
    rozpanoszyły się w typie [bool] z powodu nieterminacji.

    Morał jest prosty: nieterminacja to wynalazek szatana, a negatywne
    typy induktywne to też wynalazek szatana. *)

(** ** Twierdzenie Cantora *)

(** Zanim zaczniemy ten rozdział na poważnie, mam dla ciebie wesoły łamaniec
    językowy:

    Cantor - kanciarz, który skradł zza kurtyny kantoru z Kantonu kontury
    kartonu Koranicznemu kanarowi, który czasem karał karczystych kafarów
    czarami za karę za kantowanie i za zakatowanie zza kontuaru konarem
    kontrkulturowych kuluarowych karłów.

    Dobra, wystarczy. Reszta tego podrozdziału będzie śmiertelnie poważna,
    a przyjrzymy się w niej jednemu z mega klasycznych twierdzeń z końca
    XIX w. głoszącemu mniej więcej, że "zbiór potęgowy zbioru liczb
    naturalnych ma większą moc od zbioru liczb naturalnych".

    Co za bełkot, pomyślisz zapewne. Ten podrozdział poświęcimy właśnie temu,
    żeby ów bełkot nieco wyklarować. Jeżeli zaś zastanawiasz się, po co nam
    to, to odpowiedź jest prosta - na (uogólnionym) twierdzeniu Cantora
    opierać się będzie nasza systematyczna metoda dowodzenia nielegalności
    negatywnych typów induktywnych.

    Oczywiście oryginalne sformułowanie twierdzenia powstało na długo przed
    powstaniem teorii typów czy Coqa, co objawia się np. w tym, że mówi ono
    o _zbiorze_ liczb naturalnych, podczas gdy my dysponujemy _typem_ liczb
    naturalnych. Musimy więc oryginalne sformułowanie lekko przeformułować,
    a także wprowadzić wszystkie niezbędne nam pojęcia. *)

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.

(** Pierwszym niezbędnym pojęciem jest pojęcie surjekcji. Powyższa definicja
    głosi, że funkcja jest surjektywna, gdy każdy element przeciwdziedziny
    jest wynikiem funkcji dla pewnego elementu dziedziny. Surjekcja to
    funkcja, która jest surjektywna.

    O co chodzi w tej definicji? Samo słowo "surjekcja" pochodzi od fr.
    "sur" - "na" oraz łac. "iacere" - "rzucać". Ubogim tłumaczeniem na
    polski może być słowo "narzut".

    Idea jest taka, że surjekcja [f : A -> B] "narzuca" swoją dziedzinę
    [A] na przeciwdziedzinę [B] tak, że [A] "pokrywa" całe [B]. Innymi
    słowy, każdy element [b : B] jest pokryty przez jakiś element [a : A],
    co wyraża równość [f a = b]. Oczywiście to [a] nie musi być unikalne -
    [b] może być pokrywane przez dużo różnych [a]. Jak widać, dokładnie to
    jest napisane w powyższej definicji.

    Mówiąc jeszcze prościej: jeżeli [f : A -> B] jest surjekcją, to typ
    [A] jest większy (a precyzyjniej mówiący, nie mniejszy) niż typ [B].
    Oczywiście nie znaczy to, że jeżeli [f] nie jest surjekcją, to typ
    [A] jest mniejszy niż [B] - mogą przecież istnieć inne surjekcje.
    Powiemy, że [A] jest mniejszy od [B], jeżeli nie istnieje żadna
    surjekcja między nimi.

    Spróbujmy rozrysować to niczym Jacek Gmoch... albo nie, bo nie umiem
    jeszcze rysować, więc zamiast tego będzie przykład i ćwiczenie. *)

Definition isZero (n : nat) : bool :=
match n with
    | 0 => true
    | _ => false
end.

Lemma surjective_isZero : surjective isZero.
Proof.
  unfold surjective. destruct b.
    exists 0. cbn. reflexivity.
    exists 42. cbn. reflexivity.
Qed.

(** Funkcja [isZero], która sprawdza, czy jej argument jest zerem, jest
    surjekcją, bo każdy element typu [bool] może być jej wynikiem -
    [true] jest wynikiem dla [0], zaś [false] jest jej wynikiem dla
    wszystkich innych argumentów. Wobec tego możemy skonkludować, że
    typ [nat] jest większy niż typ [bool] i w rzeczywistości faktycznie
    tak jest: [bool] ma dwa elementy, a [nat] nieskończenie wiele.

    Do kwestii tego, który typ ma ile elementów wrócimy jeszcze w rozdziale
    o typach i funkcjach. Tam też zapoznamy się lepiej z surjekcjami i
    innymi rodzajami funkcji. Tymczasem ćwiczenie: *)

(** **** Ćwiczenie *)

(** Czy funkcja [plus 5] jest surjekcją? A funkcja [fun n : nat => minus n 5]?
    Sprawdź swoje odpowiedzi w Coqu. Na koniec filozoficznie zinterpretuj
    otrzymany wynik.

    Wskazówka: [minus] to funkcja z biblioteki standardowej, która
    implementuje odejmowanie liczb naturalnych z obcięciem, tzn. np.
    [2 - 5 = 0]. Użyj [Print]a, żeby dokładnie zbadać jej definicję. *)

(* begin hide *)
(* Jest oczywiste, że [+ 5] nie jest surjekcją, zaś [- 5] tak. *)
(* end hide *)

(** Pozostaje jeszcze kwestia tego, czym jest "zbiór potęgowy zbioru liczb
    naturalnych". Mimo groźnej nazwy sprawa jest prosta: jest to archaiczne
    określenie na typ funkcji [nat -> bool]. Każdą funkcję [f : nat -> bool]
    możemy interpretować jako pewną kolekcję (czyli właśnie zbiór) elementów
    typu [nat], zaś [f n], czyli wynik [f] na konkretnym [n], mówi nam, czy
    [n] znajduje się w tej kolekcji, czy nie.

    To w zasadzie wyczerpuje zestaw pojęć potrzebnych nam do sformułowania
    twierdzenia. Pojawiająca się w oryginalnej wersji "większa moc" to po
    prostu synonim określenia "większy", które potrafimy już wyrażać za
    pomocą pojęcia surjekcji. Tak więc nowszą (czyli bardziej postępową)
    wersję twierdzenia Cantora możemy sformułować następująco: nie istnieje
    surjekcja z [nat] w [nat -> bool]. Lub jeszcze bardziej obrazowo: [nat]
    jest mniejsze niż [nat -> bool]. *)

Theorem Cantor :
  forall f : nat -> (nat -> bool), ~ surjective f.
Proof.
  unfold surjective. intros f Hf.
  pose (diagonal := fun n : nat => negb (f n n)).
  destruct (Hf diagonal) as [n Hn].
  apply (f_equal (fun h : nat -> bool => h n)) in Hn.
  unfold diagonal in Hn. destruct (f n n); inversion Hn.
Qed.

(** Dowód twierdzenia jest równie legendarny jak samo twierdzenie, a na
    dodatek bajecznie prosty i niesamowicie użyteczny - jeżeli będziesz
    zajmował się w życiu matematyką i informatyką, spotkasz go w jeszcze
    wielu odsłonach. Metoda stojąca za dowodem nazywana bywa argumentem
    przekątniowym - choć nazwa ta może się wydawać dziwna, to za chwilę
    stanie się zupełnia jasna.

    O co więc chodzi w powyższym dowodzie? Po pierwsze zauważmy, że
    mamy do czynienia z funkcją [f : nat -> (nat -> bool)], czyli
    funkcją, która bierze liczbę naturalną i zwraca funkcję z liczb
    naturalnych w [bool]. Pamiętajmy jednak, że [->] łączy w prawo
    i wobec tego typ [f] możemy zapisać też jako [nat -> nat -> bool].
    Tak więc [f] jest funkcją, która bierze dwie liczby naturalne i
    zwraca element typu [bool].

    Dzięki temu zabiegowi możemy wyobrażać sobie [f] jako dwuwymiarową
    tabelkę, której wiersze i kolumny są indeksowane liczbami naturalnymi,
    a komórki w tabelce wypełnione są wartościami typu [bool]. Przyjmijmy,
    że pierwszy argument [f] to indeks wiersza, zaś drugi to indeks kolumny.
    W takim układzie [f n m] to wartość [n]-tej funkcji na argumencie [m].
    Wobec tego twierdzenie możemy sparafrazować mówiąc, że każda funkcja
    [nat -> bool] znajduje się w którymś wierszu tabelki.

    To tyle wyobraźni - możemy już udowodnić twierdzenie. Na początku
    oczywiście bierzemy dowolne [f] oraz zakładamy, że jest surjekcją,
    uprzednio odwijając definicję bycia surjekcją.

    Teraz musimy jakoś wyciągnąć sprzeczność z hipotezy [Hf], czyli,
    używając naszej tabelkowej parafrazy, znaleźć funkcję z [nat] w
    [bool], która nie znajduje się w tabelce. A nie znajdować się w
    tabelce, panie Ferdku, to znaczy: różnić się od każdej funkcji z
    tabelki na jakimś argumencie.

    Zamiast jednak szukać takiej funkcji po omacku, skonstruujmy ją
    z tego, co mamy pod ręką - czyli z naszej tabelki. Jak przerobić
    funkcje z tabelki na nową, której w nie ma w tabelce? Tu właśnie
    ujawnia się geniuszalność Cantora: użyjemy metody przekątniowej,
    czyli spojrzymy na przekątną naszej tabelki.

    Definiujemy więc nową funkcję [diagonal : nat -> bool] następująco:
    dla argumentu [n : nat] bierzemy funkcję z [n]-tego wiersza w tabelce,
    patrzymy na [n]-tą kolumnę, czyli na wartość funkcji na argumencie
    [n], i zwracamy negację tego, co tam znajdziemy. Czujesz sprzeczność?

    Nasze założenie mówi, że [diagonal] znajduje się w którymś wierszu
    tabelki - niech ma on numer [n]. Wiemy jednak, że [g] różni się od
    [n]-tej funkcji z tabelki na argumencie [n], gdyż zdefiniowaliśmy ją
    jako negację tej właśnie komórki w tabelce. Dostajemy stąd równość
    [f n n = diagonal n = negb (f n n)], co po analizie przypadków daje
    ostatecznie [true = false] lub [false = true].

    Voil� ! Sprzeczność osiągnięta, a zatem początkowe założenie było
    błędne i nie istnieje żadna surjekcja z [nat] w [nat -> bool]. *)

(** **** Ćwiczenie *)

(** Udowodnij, że nie ma surjekcji z [nat] w [nat -> nat]. Czy jest surjekcja
    z [nat -> bool] w [(nat -> bool) -> bool]? A w [nat -> bool -> bool]? *)

(** Poznawszy twierdzenie Cantora, możemy powrócić do ścisłej pozytywności,
    czyż nie? Otóż nie, bo twierdzenie Cantora jest biedne. Żeby czerpać
    garściami niebotyczne profity, musimy najpierw uogólnić je na dowolne
    dwa typy [A] i [B] znajdując kryterium mówiące, kiedy nie istnieje
    surjekcja z [A] w [A -> B]. *)

Theorem Cantor' :
  forall {A B : Type} (f : A -> (A -> B)) (modify : B -> B),
    (forall b : B, modify b <> b) -> ~ surjective f.
Proof.
  unfold surjective. intros A B f modify H Hf.
  pose (g := fun x : A => modify (f x x)).
  destruct (Hf g) as [x Hx].
  apply (f_equal (fun h => h x)) in Hx.
  unfold g in Hx. apply (H (f x x)).
  symmetry. assumption.
Qed.

(** Uogólnienie jest dość banalne. Najpierw zastępujemy [nat] i [bool] przez
    dowolne typy [A] i [B]. W oryginalnym twierdzeniu nie użyliśmy żadnej
    właściwości liczb naturalnych, więc nie musimy szukać żadnych kryteriów
    dla typu [A]. Nasza tabelka może równie dobrze być indeksowana elementami
    dowolnego typu - dalej jest to tabelka i dalej ma przekątną.

    Twierdzenie było jednak zależne od pewnej właściwości [bool], mianowicie
    funkcja [diagonal] była zdefiniowana jako negacja przekątnej. Było nam
    jednak potrzeba po prostu funkcji, która dla każdego elementu z przekątnej
    zwraca element [bool] od niego różny. Ponieważ [bool] ma dokładnie dwa
    elementy, to negacja jest jedyną taką funkcją.

    Jednak w ogólnym przypadku dobra będzie dowolna [B]-endofunkcja bez
    punktów stałych. Ha! Nagły atak żargonu bezzębnych ryb, co? Zróbmy
    krótką przerwę, żeby zbadać sposób komunikacji tych czarodziejskich
    zwierząt pływających po uczelnianych korytarzach.

    Endofunkcja to funkcja, która ma taką samą dziedzinę i przeciwdziedzinę.
    Można się zatem domyślać, że [B]-endofunkcja to funkcja o typie [B -> B].
    Punkt stały zaś to takie [x], że [f x = x]. Jest to więc dokładnie ta
    własność, której chcemy, żeby pożądana przez nas funkcja nie miała dla
    żadnego [x]. Jak widać, żargon bezzębnych ryb jest równie zwięzły jak
    niepenetrowalny dla zwykłych śmiertelników.

    Podsumowując: w uogólnionym twierdzeniu Cantora nie wymagamy niczego od
    [A], zaś od [B] wymagamy tylko, żeby istniała funkcja [modify : B -> B],
    która spełnia [forall b : B, modify b <> b]. Dowód twierdzenia jest taki
    jak poprzednio, przy czym zastępujemy użycie [negb] przez [modify]. *)

(** **** Ćwiczenie *)

(** Znajdź jedyny słuszny typ [B], dla którego nie istnieje żadna
    [B]-endofunkcja bez punktów stałych.

    Podpowiedź: to zadanie jest naprawdę proste i naprawdę istnieje jedyny
    słuszny typ o tej właściwości.

    Pytanie (bardzo trudne): czy da się udowodnić w Coqu, że istnieje
    dokładnie jeden taki typ? Jeżeli tak, to w jakim sensie typ ten
    jest unikalny i jakich aksjomatów potrzeba do przepchnięcia dowodu? *)

(* begin hide *)

Lemma unit_unique_type_without_endofunction_without_fixpoints :
  (forall {A : Type} (x y : A), {x = y} + {x <> y}) ->
  forall A : Type,
    (forall f : A -> A, exists x : A, f x = x) ->
      exists (f : A -> unit) (g : unit -> A),
        (forall x : A, g (f x) = x).
Proof.
  intros K A H.
  destruct (H (fun x : A => x)) as [x eq].
  exists (fun _ => tt), (fun _ => x).
  intro y.
  pose (f := fun a : A =>
    match K A a x with
        | left _ => y
        | _ => x
    end).
  specialize (H f).
  destruct H as [z H].
  unfold f in H.
  destruct (K A z x); congruence.
Qed.

(* end hide *)

(** ** Twierdzenie Cantora jako młot na negatywność *)

(** Z Cantorem po naszej stronie możemy wreszcie kupić ruble... ekhem,
    możemy wreszcie zaprezentować ogólną metodę dowodzenia, że negatywne
    typy induktywne prowadzą do sprzeczności. Mimo szumnej nazwy ogólna
    metoda nie jest aż taka ogólna i często będziemy musieli się bonusowo
    napracować. *)

Module Example1.

(** Otworzymy sobie nowy moduł, żeby nie zaśmiecać globalnej przestrzeni
    nazw - wszystkie nasze złe typy będą się nazywały [wut]. Przy okazji,
    zdecydowanie powinieneś nabrać podejrzeń do tej nazwy - jeżeli coś w
    tej książce nazywa się [wut], to musi to być złowrogie, podejrzane
    paskudztwo. *)

Axioms
  (wut : Type -> Type)
  (C : forall {A : Type}, (wut A -> A) -> wut A)
  (dcase : forall
    (A : Type)
    (P : wut A -> Type)
    (PC : forall f : wut A -> A, P (C f)),
      {f : forall w : wut A, P w |
        forall g : wut A -> A, f (C g) = PC g}).

(** [wut] to aksjomatyczne kodowanie tego samego typu, o którym poprzednio
    tylko udawaliśmy, że istnieje. Zauważmy, że nie jest nam potrzebna
    reguła indukcji - wystarczy jeden z prostszych eliminatorów, mianowicie
    [dcase], czyli zależna reguła analizy przypadków. *)

Definition bad (A : Type) : wut A -> (wut A -> A).
Proof.
  apply (dcase A (fun _ => wut A -> A)).
  intro f. exact f.
Defined.

(** Dlaczego typ [wut A] jest nielegalny, a jego definicja za pomocą komendy
    [Inductive] jest odrzucana przez Coqa? Poza wspomnianymi w poprzednim
    podrozdziale problemami filozoficznymi wynikającymi z nieterminacji,
    jest też drugi, bardziej namacalny powód: istnienie typu [wut A] jest
    sprzeczne z (uogólnionym) twierdzeniem Cantora.

    Powód tej sprzeczności jest dość prozaiczny: za pomocą konstruktora [C]
    możemy z dowolnej funkcji [wut A -> A] zrobić element [wut A], a skoro
    tak, to dowolne [w : wut A] możemy odpakować i wyjąć z niego funkcję
    [f : wut A -> A]. *)

Lemma bad_sur :
  forall A : Type, surjective (bad A).
Proof.
  unfold surjective. intros A f.
  unfold bad. destruct (dcase _) as [g H].
  exists (C f). apply H.
Qed.

(** Skoro możemy włożyć dowolną funkcję, to możemy także wyjąć dowolną
    funkcję, a zatem mamy do czynienia z surjekcją. *)

Lemma worst : False.
Proof.
  apply (Cantor' (bad bool) negb).
    destruct b; inversion 1.
    apply bad_sur.
Qed.

(** W połączeniu zaś z twierdzeniem Cantora surjekcja [wut A -> (wut A -> A)]
    prowadzi do sprzeczności - wystarczy za [A] wstawić [bool]. *)

End Example1.

(** Przykład może ci się jednak wydać niezadowalający - typ [wut] jest
    przecież dość nietypowy, bo ma tylko jeden konstruktor. A co, gdy
    konstruktorów jest więcej?

    Początkowo miałem opisać kilka przypadków z większą liczbą konstruktorów,
    ale stwierdziłem, że jednak mi się nie chce. W ćwiczeniach zobaczymy, czy
    będziesz w stanie sam wykombinować, jak się z nimi uporać. *)

(** **** Ćwiczenie *)

(** Poniższe paskudztwo łamie prawo ścisłej pozytywności nie jednym, lecz
    aż dwoma swoimi konstruktorami.

    Zakoduj ten typ aksjomatycznie i udowodnij, że jego istnienie prowadzi
    do sprzeczności. Metoda jest podobna jak w naszym przykładzie, ale
    trzeba ją troszkę dostosować do zastanej sytuacji. *)

Module Exercise1.

Fail Inductive wut : Type :=
    | C0 : (wut -> bool) -> wut
    | C1 : (wut -> nat) -> wut.

(* begin hide *)
Axioms
  (wut : Type)
  (C0 : (wut -> bool) -> wut)
  (C1 : (wut -> nat) -> wut)
  (ind : forall
    (P : wut -> Type)
    (PC0 : forall f : wut -> bool, P (C0 f))
    (PC1 : forall f : wut -> nat, P (C1 f)),
      {f : forall w : wut, P w |
        (forall g : wut -> bool, f (C0 g) = PC0 g) /\
        (forall g : wut -> nat, f (C1 g) = PC1 g)
      }
  ).

Definition bad :
  wut -> (wut -> bool).
Proof.
  apply (ind (fun _ => wut -> bool)).
    intro f. exact f.
    intros _ _. exact true.
Defined.

Lemma bad_sur :
  forall (f : wut -> bool), exists w : wut, bad w = f.
Proof.
  intro. unfold bad. destruct (ind _) as (g & H1 & H2).
  exists (C0 f). apply H1.
Defined.
(* end hide *)

Lemma wut_illegal : False.
(* begin hide *)
Proof.
  destruct (bad_sur (fun w : wut => negb (bad w w))).
  unfold bad in H. destruct (ind _).
  apply (f_equal (fun f => f x)) in H.
  destruct (x0 x x); inversion H.
Qed.
(* end hide *)

End Exercise1.

(** **** Ćwiczenie *)

(** Poniższe paskudztwo ma jeden konstruktor negatywny, a drugi pozytywny,
    niczym typowa panienka z borderlinem...

    Polecenie jak w poprzednim ćwiczeniu. *)

Module Exercise2.

Fail Inductive wut : Type :=
    | C0 : (wut -> wut) -> wut
    | C1 : nat -> wut.

(* begin hide *)
Axioms
  (wut : Type)
  (C0 : (wut -> wut) -> wut)
  (C1 : nat -> wut)
  (ind : forall
    (P : wut -> Type)
    (PC0 : forall f : wut -> wut, P (C0 f))
    (PC1 : forall n : nat, P (C1 n)),
      {f : forall w : wut, P w |
        (forall g : wut -> wut, f (C0 g) = PC0 g) /\
        (forall n : nat, f (C1 n) = PC1 n)
      }
  ).

Definition bad :
  wut -> (wut -> wut).
Proof.
  apply (ind (fun _ => wut -> wut)).
    intro f. exact f.
    intros _ w. exact w.
Defined.

Lemma bad_sur :
  forall (f : wut -> wut), exists w : wut, bad w = f.
Proof.
  intro. unfold bad. destruct (ind _) as (g & H1 & H2).
  exists (C0 f). apply H1.
Defined.

Definition discern : wut -> bool.
Proof.
  apply ind; intros _.
    exact true.
    exact false.
Defined.

Lemma discern' :
  forall (f : wut -> wut) (n : nat),
    C0 f = C1 n -> False.
Proof.
  intros. apply (f_equal discern) in H.
  unfold discern in H. destruct (ind _) as (g & p & q).
  rewrite p, q in H. inversion H.
Qed.

Definition change : wut -> wut.
Proof.
  apply (ind (fun _ => wut)).
    intro. exact (C1 0).
    intro. apply (C0 (fun w => w)).
Defined.

Lemma change_neq :
  forall w : wut, change w <> w.
Proof.
  apply ind.
    intros f H. unfold change in H. destruct (ind _) as (g & H1 & H2).
      rewrite H1 in H. eapply discern'. symmetry. exact H.
    intros n H. unfold change in H. destruct (ind _) as (g & H1 & H2).
      rewrite H2 in H. apply discern' in H. assumption.
Qed.
(* end hide *)

Lemma wut_illegal : False.
(* begin hide *)
Proof.
  destruct (bad_sur (fun w : wut => change (bad w w))).
  unfold bad in H. destruct (ind _).
  apply (f_equal (fun f => f x)) in H.
  apply (change_neq (x0 x x)).
  symmetry. assumption.
Qed.
(* end hide *)

End Exercise2.

(** **** Ćwiczenie *)

(** Poniższy typ reprezentuje termy beztypowego rachunku lambda, gdzie [V]
    to typ reprezentujący zmienne. Co to za zwierzątko ten rachunek lambda
    to my się jeszcze przekonamy... chyba, oby.

    Taki sposób reprezentowania rachunku lambda (i ogólnie składni języków
    programowania) nazywa się HOAS, co jest skrótem od ang. Higher Order
    Abstract Syntax. W wielu językach funkcyjnych jest to popularna technika,
    ale w Coqu, jak zaraz udowodnisz, jest ona nielegalna. Ława oburzonych
    jest rzecz jasna oburzona! *)

Module Exercise3.

Fail Inductive Term (V : Type) : Type :=
    | Var : V -> Term V
    | Lam : (Term V -> Term V) -> Term V
    | App : Term V -> Term V -> Term V.

(* begin hide *)
Axiom
  (Term : Type -> Type)
  (Var : forall {V : Type}, V -> Term V)
  (Lam : forall {V : Type}, (Term V -> Term V) -> Term V)
  (App : forall {V : Type}, Term V -> Term V -> Term V)
  (case : forall
    (V : Type)
    (P : Term V -> Type)
    (PVar : forall v : V, P (Var v))
    (PLam : forall g : Term V -> Term V, P (Lam g))
    (PApp : forall t1 t2 : Term V, P (App t1 t2)),
      {f : forall t : Term V, P t |
        (forall v : V, f (Var v) = PVar v) /\
        (forall g : Term V -> Term V, f (Lam g) = PLam g) /\
        (forall t1 t2 : Term V, f (App t1 t2) = PApp t1 t2)}).

Definition bad {V : Type} : Term V -> (Term V -> Term V).
Proof.
  apply (case _ (fun _ => Term V -> Term V)).
    intros _. exact (fun x => x).
    intro f. exact f.
    intros _ _. exact (fun x => x).
Defined.

Definition discern {V : Type}  : Term V -> nat.
Proof.
  apply (case V (fun _ => nat)); repeat intros _.
    exact 0.
    exact 1.
    exact 2.
Defined.
(* end hide *)

Lemma Term_illegal : False.
(* begin hide *)
Proof.
  eapply (Cantor' (@bad unit)). Unshelve. all: cycle 1.
    red. intro f. exists (Lam f). unfold bad. destruct (case _).
      decompose [and] a. apply H1.
    apply case; intros.
      exact (App (Var tt) (Var tt)).
      exact (Var tt).
      exact (Var tt).
    apply case; cbn; intros;
    destruct (case _) as [f H];
    decompose [and] H; clear H;
    rewrite ?H0, ?H2, ?H3;
    intro; apply (f_equal discern) in H;
    unfold discern in H; destruct case; decompose [and] a;
    congruence.
Qed.
(* end hide *)

End Exercise3.

(** **** Ćwiczenie *)

(** Poniższe bydle jest najgorsze z możliwych - póki co nie wiem, jak to
    udowodnić. Powodzenia! *)

Module Exercise4.

Fail Inductive wut : Type :=
    | C : (wut -> wut) -> wut.

(* begin hide *)
Axioms
  (wut : Type)
  (C : (wut -> wut) -> wut)
  (ind : forall
    (P : wut -> Type)
    (PC : forall f : wut -> wut, (forall w : wut, P (f w)) -> P (C f)),
      {f : forall w : wut, P w |
        forall g : wut -> wut,
          f (C g) = PC g (fun w => f (g w))
      }
    ).

Definition bad :
  wut -> (wut -> wut).
Proof.
  apply (ind (fun _ => wut -> wut)).
    intros f _. exact f.
Defined.

Lemma bad_sur :
  surjective bad.
Proof.
  unfold surjective. intro f. exists (C f).
  unfold bad. destruct (ind _). apply e.
Defined.

Definition change : wut -> wut.
Proof.
  apply ind.
  intros f g. exact (g (C f)).
(*  intro w. exact (C (fun _ => w)).*)

(*  apply (ind (fun _ => wut)).*)
  
(*  intro f. apply f. exact (C (fun _ => C f)).*)
Defined.

Lemma change_neq :
  forall w : wut, change w <> w.
Proof.
  apply ind. intros f H' H.
  pose (H'' := H' (C f)).
  unfold change in *. destruct (ind _).
Admitted.
(* end hide *)

Lemma wut_illegal : False.
(* begin hide *)
Proof.
  apply (Cantor' bad change).
    apply change_neq.
    unfold surjective. apply bad_sur.
Qed.
(* end hide *)

End Exercise4.

(** ** Poradnik rozpoznawania negatywnych typów induktywnych *)

(** Skoro już wiemy, że negatywne typy induktywne są wynalazkiem szatana,
    to czas podać proste kryterium na ich rozpoznawanie. Jeżeli jesteś
    sprytny, to pewnie sam zdążyłeś już zauważyć ogólną regułę. Jednak aby
    nie dyskryminować osób mało sprytnych, trzeba napisać ją wprost.

    Kryterium jest banalne. Mając dany typ [T] musimy rzucić okiem na jego
    konstruktory, a konkretniej na ich argumenty. Argumenty nieindukcyjne
    (czyli o typach, w których nie występuje [T]) są zupełnie niegroźnie.
    Interesować nas powinny jedynie argumenty indukcyjne, czyli takie, w
    których występuje typ [T].

    Niektóre typy argumentów indukcyjnych są niegroźne, np. [T * T], [T + T],
    [list T] albo [{t : T | P t}], ale powodują one, że Coq nie potrafi
    wygenerować odpowiedniej reguły indukcji i zadowala się jedynie regułą
    analizy przypadków. Nie prowadzą one do sprzeczności, ale powinniśmy ich
    unikać.

    Argument typu [T * T] można zastąpić dwoma argumentami typu [T]
    i podobnie dla [{t : T | P t}]. Konstruktor z argumentem typu [T + T]
    możemy rozbić na dwa konstruktory (i powinniśmy, bo jest to bardziej
    czytelne). Konstruktor z wystąpieniem [list T] możemy przerobić na
    definicję przez indukcję wzajemną (ćwiczenie: sprawdź jak), ale lepiej
    chyba po prostu zaimplementować regułę indukcji ręcznie. *)

Inductive T0 : Type :=
    | c0 : T0
    | c1 : nat -> T0
    | c2 : T0 -> T0
    | c3 : nat * T0 -> T0
    | c4 : T0 * T0 -> T0
    | c5 : T0 + T0 -> T0
    | c6 : list T0 -> T0.

(** Rodzaje nieszkodliwych typów argumentów widać na powyższym przykładzie.
    Konstruktory [c0] i [c1] są nieindukcyjne, więc są ok. Konstruktor [c2]
    jest indukcyjny - jest jeden argument typu [T0]. Zauważ, że typem
    konstruktora [c2] jest [T0 -> T0], ale nie oznacza to, że [T0]
    występuje po lewej stronie strzałki!

    Jest tak, gdyż ostatnie wystąpienie [T0] jest konkluzją konstruktora
    [c2]. Ważne są tylko wystąpienia po lewej stronie strzałki w argumentach
    (gdyby konstruktor [c2] nie był legalny, to jedynymi legalnymi typami
    induktywnymi byłyby enumeracje).

    Konstruktory [c3], [c4], [c5] i [c6] są induktywne i również w pełni
    legalne, ale są one powodem tego, że Coq nie generuje dla [T0] reguły
    indukcji, a jedynie regułę analizy przypadków (choć nazwa się ona
    [T0_ind]). *)

(** **** Ćwiczenie *)

(** Zrefaktoryzuj powyższy upośledzony typ. *)

(* begin hide *)
(** TODO *)
(* end hide *)

(** Problem pojawia się dopiero, gdy typ [T] występuje po lewej stronie
    strzałki, np. [T -> bool], [T -> T], [(T -> T) -> T], lub gdy jest
    skwantyfikowany uniwersalnie, np. [forall t : T, P t],
    [forall f : (forall t : T, P t), Q f].

    W trzech poprzednich podrozdziałach mierzyliśmy się z sytuacjami, gdy
    typ [T] występował bezpośrednio na lewo od strzałki, ale oczywiście
    może on być dowolnie zagnieżdżony. Dla każdego wystąpienia [T] w
    argumentach możemy policzyć, na lewo od ilu strzałek (albo jako
    jak mocno zagnieżdżona dziedzina kwantyfikacji) się ono znajduje.
    Liczbę tę nazywać będziemy niedobrością. W zależności od niedobrości,
    wystąpienie nazywamy:
    - 0 - wystąpienie ściśle pozytywne
    - liczba nieparzysta - wystąpienie negatywne
    - liczba parzysta (poza 0) - wystąpienie pozytywne *)

(** Jeżeli w definicji mamy wystąpienie negatywne, to typ możemy nazywać
    negatywnym typem induktywnym (choć oczywiście nie jest to typ
    induktywny). Jeżeli nie ma wystąpień negatywnych, ale są wystąpienia
    pozytywne, to typ nazywamy pozytywnym typem induktywnym (lub nie ściśle
    pozytywnym typem induktywnym), choć oczywiście również nie jest to typ
    induktywny. Jeżeli wszystkiego wystąpienia są ściśle pozytywne, to mamy
    do czynienia po prostu z typem induktywnym.

    Podobne nazewnictwo możemy sobie wprowadzić dla konstruktorów
    (konstruktory negatywne, pozytywne i ściśle pozytywne), ale nie
    ma sensu, bo za tydzień i zapomnisz o tych mało istotnych detalach.
    Ważne, żebyś zapamiętał najważniejsze, czyli ideę. *)

Fail Inductive T1 : Type :=
    | T1_0 : T1 -> T1
    | T1_1 : (T1 -> T1) -> T1
    | T1_2 : ((T1 -> T1) -> T1) -> T1
    | T1_3 : forall (t : T1) (P : T1 -> Prop), P t -> T1.

(** W powyższym przykładzie wystąpienie [T1] w pierwszym argumencie
    [T1_0] jest ściśle pozytywne (na lewo od 0 strzałek). Pierwsze
    wystąpienie [T1] w [T1_1] jest negatywne (na lewo od 1 strzałki),
    a drugie ściśle pozytywne (na lewo od 0 strzałek). Pierwsze
    wystąpienie [T1] w [T1_2] jest pozytywne (na lewo od 2 strzałek),
    drugie negatywne (na lewo od 1 strzałki), trzecie zaś ściśle
    pozytywne (na lewo od 0 strzałek). Pierwsze wystąpienie [T1] w
    [T1_3] jest negatywne (dziedzina kwantyfikacji), drugie zaś
    pozytywne (na lewo od jednej strzałki, ale ta strzałka jest w
    typie, po którym kwantyfikujemy).

    Konstruktor [T1_0] jest ściśle pozytywne, zaś konstruktory [T1_1],
    [T1_2] oraz [T1_3] są negatywne. Wobec tego typ [T1] jest negatywnym
    typem induktywnym (czyli wynalazkiem szatana, którego zaakceptowanie
    prowadzi do sprzeczności). *)

(** **** Ćwiczenie *)

Fail Inductive T2 : Type :=
    | T2_0 : forall f : (forall g : (forall t : T2, nat), Prop), T2
    | T2_1 : (((((T2 -> T2) -> T2) -> T2) -> T2) -> T2) -> T2
    | T2_2 :
      ((forall (n : nat) (P : T2 -> Prop),
        (forall t : T2, nat)) -> T2) -> T2 -> T2 -> T2.

(** Policz niedobrość każdego wstąpienia [T2] w powyższej definicji.
    Sklasyfikuj konstruktory jako negatywne, pozytywne lub ściśle
    pozytywne. Następnie sklasyfikuj sam typ jako negatywny, pozytywny
    lub ściśle pozytywny. *)

(** **** Ćwiczenie *)

(* Inductive T : Type := *)

(** Rozstrzygnij, czy następujące konstruktory spełniają kryterium ścisłej
    pozytywności. Jeżeli tak, narysuj wesołego jeża. Jeżeli nie, napisz
    zapętlającą się funkcję podobną do [loop] (zakładamy, że typ [T] ma
    tylko ten jeden konstruktor). Następnie sprawdź w Coqu, czy udzieliłeś
    poprawnej odpowiedzi.
    - [| C1 : T]
    - [| C2 : bool -> T]
    - [| C3 : T -> T]
    - [| C4 : T -> nat -> T]
    - [| C5 : forall A : Type, T -> A -> T]
    - [| C6 : forall A : Type, A -> T -> T]
    - [| C7 : forall A : Type, (A -> T) -> T]
    - [| C8 : forall A : Type, (T -> A) -> T]
    - [| C9 : (forall x : T, T) -> T]
    - [| C10 : (forall (A : Type) (x : T), A) -> T]
    - [| C11 : forall A B C : Type,
                  A -> (forall x : T, B) -> (C -> T) -> T] *)

(* begin hide *)
(* C1-C7 są legalne, C8-C11 nie. *)
(* end hide *)

(** ** Kilka bonusowych pułapek *)

(** Wiemy już, że niektóre typy argumentów indukcyjnych są ok ([T * T],
    [list T]), a niektóre inne nie ([T -> T], [forall t : T, ...]).
    Uważny i żądny wiedzy czytelnik (daj boże, żeby tacy istnieli) zeche
    zapewne postawić sobie pytanie: które dokładnie typy argumentów
    indukcyjnych są ok, a które są wynalazkiem szatana?

    Najprościej będzie sprawę zbadać empirycznie, czyli na przykładzie.
    Żeby zaś przykład był reprezentatywny, niech parametrem definicji
    będzie dowolna funkcja [F : Type -> Type]. *)

Fail Inductive wut (F : Type -> Type) : Type :=
    | wut_0 : F (wut F) -> wut F.
(* ===> The command has indeed failed with message:
        Non strictly positive occurrence of "wut" in
        "F (wut F) -> wut F". *)

(** Jak widać, jeżeli zaaplikujemy [F] do argumentu indukcyjnego, to Coq
    krzyczy, że to wystąpienie nie jest ściśle pozytywne. Dlaczego tak
    jest, skoro [F] nie jest ani strzałką, ani kwantyfikatorem uniwersalnym?
    Dlatego, że choć nie jest nimi, to może nimi zostać. Jeżeli zdefiniujemy
    sobie gdzieś na boku [F := fun A : Type => A -> bool], to wtedy
    [wut_0 F : (wut F -> bool) -> wut F], a z takim diabelstwem już się
    mierzyliśmy i wiemy, że nie wróży ono niczego dobrego.

    Morał z tej historii jest dość banalny: gdy definiujemy typ induktywny
    [T], jedynymi prawilnymi typami dla argumentu indukcyjnego są [T] oraz
    typy funkcji, które mają [T] jako konkluzję ([A -> T], [A -> B -> T]
    etc.). Wszystkie inne albo rodzą problemy z automatyczną generacją
    reguł indukcji ([T * T], [list T]), albo prowadzą do sprzeczności
    ([T -> T], [forall t : T, ...]), albo mogą prowadzić do sprzeczności,
    jeżeli wstawi się za nie coś niedobrego ([F T]). *)

(** **** Ćwiczenie *)

Module wutF.

Definition F (A : Type) : Type := A -> bool.

(** Zakoduj aksjomatycznie rodzinę typów [wut] z powyższego przykładu.
    Następnie wstaw za parametr zdefiniowane powyżej [F] i udowodnij,
    że typ [wut F] prowadzi do sprzeczności. *)

(* begin hide *)
Axioms
  (wut : (Type -> Type) -> Type)
  (wut_0 : forall {F : Type -> Type}, F (wut F) -> wut F)
  (wut_ind :
    forall
      (F : Type -> Type)
      (P : wut F -> Type)
      (Pwut_0 : forall x : F (wut F), P (wut_0 x)),
        {f : forall x : wut F, P x |
          forall x : F (wut F), f (wut_0 x) = Pwut_0 x}).

Definition bad : wut F -> wut F -> bool.
Proof.
  apply (wut_ind F (fun _ => wut F -> bool)).
  unfold F. intro f. exact f.
Defined.

Lemma bad_sur :
  surjective bad.
Proof.
  unfold surjective.
  intro f. exists (wut_0 f).
  unfold bad. destruct (wut_ind _).
  rewrite e. reflexivity.
Qed.

Lemma bad_not_sur :
  ~ surjective bad.
Proof.
  unfold surjective. intro H.
  destruct (H (fun w : wut F => negb (bad w w))) as [w eq].
  apply (f_equal (fun f => f w)) in eq.
  unfold bad in eq. destruct (wut_ind _).
  destruct (x w w); inversion eq.
Qed.
(* end hide *)

Lemma wut_illegal : False.
(* begin hide *)
Proof.
  apply bad_not_sur. apply bad_sur.
Qed.
(* end hide *)

End wutF.

(** To jeszcze nie koniec wrażeń na dziś - póki co omówiliśmy wszakże
    kryterium ścisłej pozytywności jedynie dla bardzo prostych typów
    induktywnych. Słowem nie zająknęliśmy się nawet na temat typów
    wzajemnie induktywnych czy indeksowanych typów induktywnych. Nie
    trudno będzie nam jednak uzupełnić naszą wiedzę, gdyż w przypadku
    oby tych mechanizmów kryterium ścisłej pozytywności wygląda podobnie
    jak w znanych nam już przypadkach. *)

Fail Inductive X : Type :=
    | X0 : X
    | X1 : (Y -> X) -> X

with Y : Type :=
    | Y0 : Y
    | Y1 : X -> Y.

(* ===> The command has indeed failed with message:
        Non strictly positive occurrence of "Y"
        in "(Y -> X) -> X". *)

(** Jak widać, definicja [X] i [Y] przez wzajemną indukcję jest nielegalna,
    gdyż jedyny argument konstruktora [X1] ma typ [Y -> X]. Mogłoby wydawać
    się, że wszystko jest w porządku, wszakże [X] występuje tutaj na pozycji
    ściśle pozytywnej. Jednak ponieważ jest to definicja przez indukcję
    wzajemną, kryterium ścisłej pozytywności stosuje się nie tylko do
    wystąpień [X], ale także do wystąpień [Y] - wszystkie wystąpienia [X]
    oraz [Y] muszą być ściśle pozytywne zarówno w konstruktorach typu [X],
    jak i w konstruktorach typu [Y]. *)

(** **** Ćwiczenie *)

(** Zakoduj aksjomatycznie definicję typów [X] i [Y]. Spróbuj napisać
    zapętlającą się funkcję [loop] (czy raczej dwie wzajemnie rekurencyjne
    zapętlające się funkcje [loopx] i [loopy]), a następnie udowodnij za
    pomocą twierdzenia Cantora, że typy [X] i [Y] są nielegalne. *)

Module XY.

(* begin hide *)

Axioms
  (X Y : Type)
  (X0 : X)
  (X1 : (Y -> X) -> X)
  (Y0 : Y)
  (Y1 : X -> Y)
  (dcase :
    forall
      (P : X -> Type) (Q : Y -> Type)
      (PX0 : P X0)
      (PX1 : forall f : Y -> X, P (X1 f))
      (QY0 : Q Y0)
      (QY1 : forall x : X, Q (Y1 x)),
        {f : forall x : X, P x &
        {g : forall y : Y, Q y |
          f X0 = PX0 /\
          (forall h : Y -> X, f (X1 h) = PX1 h) /\
          g Y0 = QY0 /\
          (forall x : X, g (Y1 x) = QY1 x)}})
  (dcaseX :
    forall
      (P : X -> Type)
      (PX0 : P X0)
      (PX1 : forall f : Y -> X, P (X1 f)),
        {f : forall x : X, P x &
          f X0 = PX0 /\
          forall h : Y -> X, f (X1 h) = PX1 h})
  (dcaseY :
    forall
      (P : Y -> Type)
      (PY0 : P Y0)
      (PY1 : forall x : X, P (Y1 x)),
        {f : forall y : Y, P y &
          f Y0 = PY0 /\
          forall x : X, f (Y1 x) = PY1 x}).

Definition bad : X -> (X -> X).
Proof.
  apply (dcaseX (fun _ => X -> X)).
    intro x. exact x.
    intros f x. exact (f (Y1 x)).
Defined.

Require Import FunctionalExtensionality.

Lemma bad_sur :
  surjective bad.
Proof.
  unfold surjective. intro f.
  unfold bad. destruct (dcaseX _) as (bad & eq1 & eq2).
  exists (X1 (projT1 (dcaseY (fun _ => X) X0 f))).
  rewrite eq2.
  extensionality x. cbn.
  destruct (dcaseY _) as (aux & eq1' & eq2').
  cbn. rewrite eq2'. reflexivity.
Qed.

Definition discern : X -> bool.
Proof.
  apply dcaseX.
    exact true.
    intros _. exact false.
Defined.

Definition change : X -> X.
Proof.
  apply dcaseX.
    exact (X1 (fun _ => X0)).
    intros _. exact X0.
Defined.

Lemma change_neq :
  forall x : X, change x <> x.
Proof.
  intros x H. apply (f_equal discern) in H.
  unfold change in H; destruct (dcaseX _) as (change & eq1 & eq2).
  unfold discern in H; destruct (dcaseX _) as (discern & eq1' & eq2').
  revert x H.
  apply (dcaseX (fun x => discern (change x) = discern x -> False)); intros.
    rewrite eq1, eq1', eq2' in H. inversion H.
    rewrite eq2, eq1', eq2' in H. inversion H.
Qed.
(* end hide *)

Lemma XY_illegal : False.
(* begin hide *)
Proof.
  apply (Cantor' bad change change_neq). apply bad_sur.
Qed.

Definition loop (x : X) : X := bad x x.

Lemma loop_nontermination :
  X0 = loop (X1 (projT1 (dcaseY (fun _ => X) X0 loop))).
Proof.
  unfold loop, bad.
  destruct (dcaseX _) as (bad & eq1 & eq2).
  destruct (dcaseY _) as (aux & eq1' & eq2'); cbn.
  rewrite eq2. rewrite eq2'.
Abort.
(* end hide *)

End XY.

(** ** Jeszcze więcej pułapek *)

(** To już prawie koniec naszej wędrówki przez świat nielegalnych typów
    "induktywnych". Dowiedzieliśmy się, że negatywne typy induktywne
    prowadzą do nieterminacji i nauczyliśmy się wykorzystywać twierdzenie
    Cantora do dowodzenia nielegalności takich typów.

    Poznaliśmy też jednak klasyfikację typów wyglądających na induktywne
    (ściśle pozytywne, pozytywne, negatywne), a w szczególności pojęcie
    "niedobrości" indukcyjnego wystąpienia definiowanego typu w konstruktorze
    (upraszczając, na lewo od ilu strzałek znajduje się to wystąpienie).

    Piszę "jednak", gdyż z jej powodu możemy czuć pewien niedosyt - wszystkie
    dotychczasowe przykłady były typami negatywnymi o niedobrości równej 1.
    Podczas naszej intelektualnej wędrówki zwiedziliśmy mniej miejscówek,
    niż moglibyśmy chcieć. W tym podrozdziale spróbujemy ten przykry niedosyt
    załatać, rozważając (nie ściśle) pozytywne typy induktywne. Zobaczymy
    formalny dowód na to, że nie są one legalne (lub, precyzyjniej pisząc,
    dowód na to, że conajmniej jeden z nich nie jest legalny). Zanim jednak
    to się stanie, zobaczmy, czy wypracowane przez nas techniki działają na
    negatywne typy induktywne o niedobrości innej niż 1. *)

Module T3.

Fail Inductive T3 : Type :=
    | T3_0 : (((T3 -> bool) -> bool) -> bool) -> T3.

(** Przyjrzyjmy się powyższej definicji. Występienie indukcyjne typu [T3]
    ma współczynnik niedobrości równy 3, gdyż znajduje się na lewo od 3
    strzałek. Prawe strony wszystkich z nich to [bool]. *)

Axioms
  (T3 : Type)
  (T3_0 : (((T3 -> bool) -> bool) -> bool) -> T3)
  (T3_case :
    forall
      (P : T3 -> Type)
      (PT3_0 : forall f : ((T3 -> bool) -> bool) -> bool, P (T3_0 f)),
        {f : forall x : T3, P x |
          forall g : ((T3 -> bool) -> bool) -> bool,
            f (T3_0 g) = PT3_0 g}).

(** Po ciężkich bojach, przez które przeszedłeś, aksjomatyczne kodowanie
    tego typu nie powinno cię dziwić. Warto zauważyć jedynie, że do naszej
    dyspozycji mamy jedynie regułę zależnej analizy przypadków, gdyż nie
    wiadomo, jak miałyby wyglądać wywołania indukcyjne.

    Zanim zobaczymy, jak pokazać nielegalność tego typu metodą Cantora,
    przypomnijmy sobie pewien kluczowy fakt dotyczący negacji i jego
    banalne uogólnienie. *)

(** **** Ćwiczenie *)

Lemma triple_negation :
  forall P : Prop, ~ ~ ~ P -> ~ P.
(* begin hide *)
Proof.
  intros P f x. apply f. intro g. apply g. exact x.
Qed.
(* end hide *)

Lemma triple_arrow :
  forall A B : Type, (((A -> B) -> B) -> B) -> (A -> B).
(* begin hide *)
Proof.
  intros A B f x. apply f. intro g. apply g. exact x.
Qed.
(* end hide *)

(** Ćwiczenie to przypomina nam, że jeżeli chodzi o spamowanie negacją, to
    są w zasadzie tylko trzy sytuacje:
    - brak negacji
    - pojedyncza negacja
    - podwójna negacja *)

(** Jeżeli mamy do czynienia z większą liczbą negacji, to możemy zdejmować
    po dwie aż dojdziemy do któregoś z powyższych przypadków. Ponieważ
    negacja to tylko implikacja, której kodziedziną jest [False], a nie
    korzystamy w dowodzie z żadnych specjalnych właściwości [False],
    analogiczna właściwość zachodzi także dla dowolnego innego [B : Type]. *)

Definition bad : T3 -> (T3 -> bool).
Proof.
  apply (T3_case (fun _ => T3 -> bool)).
  intros f x. apply f. intro g. apply g. exact x.
Defined.

(** Wobec powyższych rozważań definicja funkcji bad zupełnie nie powinna
    cię zaskakiwać. Szczerze pisząc, reszta dowodu również nie jest jakoś
    specjalnie wymagająca czy oświecająca. *)

(** **** Ćwiczenie *)

(** Dokończ dowód. *)

Lemma bad_sur :
  surjective bad.
(* begin hide *)
Proof.
  unfold surjective.
  intro f. exists (T3_0 (fun g => g f)).
  unfold bad. destruct (T3_case _).
  rewrite e. reflexivity.
Qed.
(* end hide *)

Theorem T3_illegal : False.
(* begin hide *)
Proof.
  apply (Cantor' bad negb).
    destruct b; inversion 1.
    exact bad_sur.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Napisanie zapętlającej się funkcji [loop : T3 -> bool] też nie jest
    jakoś wybitnie trudne. Napisz ją i udowodnij (nieformlanie), że
    istnieje takie [x : T3], że [loop x] się zapętla. *)

(* begin hide *)
Fail Fixpoint loop (x : T3) : bool :=
match x with
    | T3_0 f => f (fun g : T3 -> bool => g (T3_0 f))
end.

(**
  Niech f := fun g => g loop

  loop (T3_0 f) =
  f (fun g => g (T3_0 f))
  loop (T3_0 f) =
  ...
*)

(* end hide *)

End T3.

(** Morał z powyższych rozważań jest prosty: nasze techniki działają także
    na negatywne typy induktywne o niedobrości równej 3. Myślę, że jesteś
    całkiem skłonny uwierzyć też, że zadziałają na te o niedobrości równej
    5, 7 i tak dalej.

    To wszystko jest prawdą jednak tylko wtedy, gdy wszystkie typy po prawych
    stronach strzałek będą takie same. A co, gdy będą różne? *)

Module T4.

Fail Inductive T4 : Type :=
    | c0 : (((T4 -> bool) -> nat) -> Color) -> T4.

Axioms
  (T4 : Type)
  (c0 : (((T4 -> bool) -> nat) -> Color) -> T4)
  (dcase :
    forall
      (P : T4 -> Type)
      (Pc0 : forall f : ((T4 -> bool) -> nat) -> Color, P (c0 f)),
        {f : forall x : T4, P x |
          forall g : ((T4 -> bool) -> nat) -> Color,
            f (c0 g) = Pc0 g}).

(** Powyższy przykład jest podobny do poprzedniego, ale tym razem zamiast
    trzech wystąpień [bool] mamy [bool], [nat] oraz [Color] (to typ, który
    zdefiniowaliśmy na samym początku tego rozdziału, gdy uczyliśmy się
    o enumeracjach). *)

Definition bad : T4 -> (T4 -> bool).
Proof.
  apply (dcase (fun _ => T4 -> _)).
  intros f x.
  apply (
    fun c : Color =>
    match c with
        | R => true
        | _ => false
    end).
  apply f. intro g.
  apply (fun b : bool => if b then 0 else 1).
  exact (g x).
Defined.

(** Nasz modus operandi będzie taki jak poprzednio: spróbujemy wyjąć z
    elementu [T4] funkcję typu [T4 -> bool]. W tym celu używamy zależnej
    reguły analizy przypadków i wprowadzamy rzeczy do kontekstu.

    Tym razem nie możemy jednak bezpośrednio zaaplikować [f], gdyż jej
    kodziedziną jest [Color], a my musimy skonstruować coś typu [bool].
    Możemy temu jednak zaradzić aplikując do celu skonstruowaną naprędce
    funkcję typu [Color -> bool]. Ta funkcja powinna być surjekcją (jeśli
    nie wierzysz, sprawdź, co się stanie, jeżeli zamienimy ją na funckję
    stałą).

    Możemy już zaaplikować [f] i wprowadzić [g] do kontekstu. Chcielibyśmy
    teraz zaaplikować [g], ale nie możemy, bo typy się nie zgadzają - [g]
    zwraca [bool], a my musimy skonstruować liczbę naturalną. Robimy tutaj
    to samo co poprzednio - aplikujemy do celu jakąś funkcję [bool -> nat].
    Tym razem nie musi ona być surjekcją (nie jest to nawet możliwe, gdyż
    nie ma surjekcji z [bool] w [nat]). Dzięki temu możemy zaaplikować [g]
    i zakończyć, używając [g x]. *)

Require Import FunctionalExtensionality.

(** Żeby pokazać, że [bad] jest surjekcją, będziemy potrzebować aksjomatu
    ekstensjonalności dla funkcji (ang. functional extensionality axiom,
    w skrócie funext). Głosi on, że dwie funkcje [f, g : A -> B] są równe,
    jeżeli uda nam się pokazać, że dają równe wyniki dla każdego argumentu
    (czyli [forall x : A, f x = g x]).

    Importując powyższy moduł zakładamy prawdziwość tego aksjomatu oraz
    uzyskujemy dostęp do taktyki [extensionality], która ułatwia dowody
    wymagające użycia ekstensjonalności. *)

Lemma bad_sur :
  surjective bad.
Proof.
  unfold surjective. intro f.
  unfold bad. destruct (dcase _) as [bad eq].
  exists (c0 (
    fun g : (T4 -> bool) -> nat =>
    match g f with
       | 0 => R
       | _ => G
    end)).
  rewrite eq.
  extensionality t.
  destruct (f t); reflexivity.
Qed.

(** Dowód jest prawie taki jak zawsze: odwijamy definicję surjektywności i
    wprowadzamy hipotezy do kontekstu, a następnie odwijamy definicję [bad]
    i rozbijamy ją dla czytelności na właściwą funkcję [bad] oraz równanie
    [eq].

    Następnie musimy znaleźć [a : T4], które [bad] mapuje na [f]. Zaczynamy
    od [c0], bo jest to jedyny konstruktor [T4]. Bierze on jako argument
    funkcję typu [((T4 -> bool) -> nat) -> Color]. Żeby ją wyprodukować,
    bierzemy na wejściu funkcję [g : (T4 -> bool) -> nat] i musimy zrobić
    coś typu [Color].

    Nie może to być jednak byle co - musimy użyć [f], a jedynym sensownym
    sposobem, żeby to zrobić, jest zaaplikować [g] do [f]. Musimy zadbać
    też o to, żeby odwrócić funkcje konwertujące [Color -> bool] oraz
    [bool -> nat], których użyliśmy w definicji [bad]. Pierwsza z nich
    konwertowała [R] (czyli kolor czerwony) na [true], a inne kolory na
    [false], zaś druga konwertowała [true] na [0], a [false] na [1].
    Wobec tego dopasowując [g f : nat] musimy przekonwertować [0] na [R],
    zaś [1] na coś innego niż [R], np. na [G] (czyli kolor zielony).

    Znalazłszy odpowiedni argument, możemy przepisać równanie definiujące
    [bad]. To już prawie koniec, ale próba użycia taktyki [reflexivity] w
    tym momencie skończyłaby się porażką. Na ratunek przychodzi nam
    aksjomat ekstensjonalności, którego używamy pisząc [extensionality t].
    Dzięki temu pozostaje nam pokazać jedynie, że [f t] jest równe tej
    drugie funkcji dla argumentu [t]. W tym celu rozbijamy [f t], a oba
    wyrażenia okazują się być konwertowalne. *)

Theorem T4_illegal : False.
Proof.
  apply (Cantor' bad negb).
    destruct b; inversion 1.
    apply bad_sur.
Qed.

(** Skoro mamy surjekcję z [T4] w [T4 -> bool], katastrofy nie da się
    uniknąć.

    Moglibyśmy się też zastanowić nad napisaniem zapętlającej się funkcji
    [loop], ale coś czuję, że ty coś czujesz, że byłoby to babranie się
    w niepotrzebnym problemie. Wobec tego (oczywiście o ile dotychczas
    się nie skapnąłeś) poczuj się oświecony! *)

Definition loop (x : T4) : bool := bad x x.

(** Ha! Tak tak, [loop] nie jest niczym innym niż lekko rozmnożoną wersją
    [bad]. *)

Lemma loop_nontermination :
  true = loop (c0 (
    fun g : (T4 -> bool) -> nat =>
    match g loop with
       | 0 => R
       | _ => G
    end)).
Proof.
  unfold loop, bad. destruct (dcase _) as [bad eq].
  rewrite 5!eq.
Abort.

(** A skoro [loop] to tylko inne [bad], to nie powinno cię też wcale a
    wcale zdziwić, że najbardziej oczywisty argument, dla którego [loop]
    się zapętla, jest żywcem wzięty z dowodu [bad_sur] (choć oczywiście
    musimy zastąpić [f] przez [loop]).

    Oczywiście niemożliwe jest, żeby formalnie udowodnić w Coqu, że coś
    się zapętla. Powyższy lemat ma być jedynie demonstracją - ręczne
    rozpisanie tego przykładu byłoby zbyt karkołomne. Jak widać z dowodu,
    przepisywanie równania definiującego [bad] tworzy wesołą piramidkę
    zrobioną z [match]y i [if]ów. Jeżeli chcesz poczuć pełnię zapętlenia,
    wypbróuj taktykę [rewrite !eq] - zapętli się ona, gdyż równanie [eq]
    można przepisywać w nieskończoność. *)

End T4.

(** Mogłoby się wydawać, że teraz to już na pewno nasze metody działają na
    wszystkie możliwe negatywne typy induktywne. Cytując Tadeusza Sznuka:
    "Nic bardziej mylnego!". *)

Module T5.

Axioms
  (T5 : Type)
  (c0 : (((T5 -> nat) -> bool) -> Color) -> T5)
  (dcase :
    forall
      (P : T5 -> Type)
      (Pc0 : forall f : ((T5 -> nat) -> bool) -> Color, P (c0 f)),
        {f : forall x : T5, P x |
          forall g : ((T5 -> nat) -> bool) -> Color,
            f (c0 g) = Pc0 g}).

(** Rzućmy okiem na powyższy typ. Wygląda podobnie do poprzedniego, ale jest
    nieco inny - typy [nat] i [bool] zamieniły się miejscami. Jakie rodzi to
    konsekwencje? Sprawdźmy. *)

Definition bad : T5 -> (T5 -> nat).
Proof.
  apply (dcase (fun _ => T5 -> _)).
  intros f x.
  apply (
    fun c : Color =>
    match c with
        | R => 0
        | G => 1
        | B => 2
    end).
  apply f. intro g.
  apply isZero. exact (g x).
Defined.

(** Definicja [bad] jest podobna jak poprzednio, ale tym razem konwertujemy
    [Color] na [nat] za pomocą funkcji, która nie jest surjekcją. *)

Require Import FunctionalExtensionality.

Lemma bad_sur :
  surjective bad.
Proof.
  unfold surjective. intro f.
  unfold bad. destruct (dcase _) as [bad eq].
  exists (c0 (
    fun g : (T5 -> nat) -> bool =>
    match g f with
        | true => R
        | false => B
    end)).
  rewrite eq. extensionality t.
  destruct (f t); cbn.
    reflexivity.
Abort.

(** Dowód również przebiega podobnie jak poprzednio. Załamuje się on dopiero,
    gdy na samym końcu rozbijamy wyrażenie [f t] i upraszczamy używając [cbn].
    W pierwszym podcelu [0 = 0] jeszcze jakoś udaje się nam udowodnić, ale w
    drugim naszym oczom ukazuje się cel [2 = S n].

    Problem polega na tym, że [f t] może być dowolną liczbą naturalną, ale
    zastosowana przez nas funkcja konwertująca [Color -> nat] może zwracać
    jedynie [0], [1] lub [2]. Teraz widzimy jak na dłoni, skąd wziął się
    wymóg, by funkcja konwertująca była surjekcją. *)

Definition loop (x : T5) : nat := bad x x.

Lemma loop_nontermination :
  42 = loop (c0 (
    fun g : (T5 -> nat) -> bool =>
    match g loop with
        | true => R
        | false => G
    end)).
Proof.
  unfold loop, bad. destruct (dcase _) as [bad eq].
  rewrite 15!eq.
Abort.

(** Co ciekawe, mimo że nie jesteśmy w stanie pokazać surjektywności [bad],
    to wciąż możemy użyć tej funkcji do zdefiniowania zapętlającej się
    funkcji [loop], zupełnie jak w poprzednim przykładzie.

    Niesmak jednak pozostaje, gdyż szczytem naszych ambicji nie powinno być
    ograniczanie się do zdefiniowania [loop], lecz do formalnego udowodnienia
    nielegalności [T5]. Czy wszystko stracone? Czy umrzemy? Tu dramatyczna
    pauza.

    Nie.

    Okazuje się, że jest pewien trikowy sposób na rozwiązanie tego problemu,
    a mianowicie: zamiast próbować wyjąć z [T5] funkcję [T5 -> nat], wyjmiemy
    stamtąd po prostu funckję [T5 -> bool] i to mimo tego, że jej tam nie ma!
*)

Definition bad' : T5 -> (T5 -> bool).
Proof.
  apply (dcase (fun _ => T5 -> _)).
  intros f x.
  apply (
    fun c : Color =>
    match c with
        | R => true
        | _ => false
    end).
  apply f. intro g.
  apply isZero. exact (g x).
Defined.

(** W kluczowych momentach najpierw konwertujemy [Color] na [bool] tak jak
    w jednym z poprzednich przykładów, a potem konwertujemy [nat] na [bool]
    za pomocą funkcji [isZero]. *)

Require Import FunctionalExtensionality.

Lemma bad'_sur :
  surjective bad'.
Proof.
  unfold surjective. intro f.
  unfold bad'. destruct (dcase _) as [bad' eq].
  exists (c0 (
    fun g : (T5 -> nat) -> bool =>
      if g (fun t : T5 => if f t then 0 else 1) then R else G)).
  rewrite eq.
  extensionality t.
  destruct (f t); cbn; reflexivity.
Qed.

(** Ponieważ obydwie nasze funkcję konwertujące były surjekcjami, możemy je
    teraz odwrócić i wykazać ponad wszelką wątpliwość, że [bad'] faktycznie
    jest surjekcją. *)

Theorem T5_illegal : False.
Proof.
  apply (Cantor' bad' negb).
    destruct b; inversion 1.
    apply bad'_sur.
Qed.

(** Spróbujmy podsumować, co tak naprawdę stało się w tym przykładzie.

    Tym razem, mimo że do [T5] możemy włożyć dowolną funkcję [T5 -> nat],
    to nie możemy jej potem wyjąć, uzyskując surjekcję, gdyż zawadzają
    nam w tym typy po prawych stronach strzałek ([bool] i [Color]), które
    mają za mało elementów, żeby móc surjektywnie przekonwertować je na
    typ [nat].

    Jednak jeżeli mamy wszystkie możliwe funkcje typu [T5 -> nat], to
    możemy przerobić je (w locie, podczas "wyciągania") na wszystkie
    możliwe funkcje typu [T5 -> bool], składając je z odpowiednią
    surjekcją (np. [isZero]). Ponieważ typ [bool] i [Color] jesteśmy
    w stanie surjektywnie przekonwertować na [bool], reszta procesu
    działa podobnie jak w poprzednich przykładach. *)

Definition loop' (x : T5) : bool := bad' x x.

Lemma loop_nontermination :
  true = loop' (c0 (
    fun g : (T5 -> nat) -> bool =>
    match g (fun t : T5 => if loop' t then 0 else 1) with
        | true => R
        | false => G
    end)).
Proof.
  unfold loop', bad'. destruct (dcase _) as [bad' eq].
  rewrite 15!eq.
Abort.

(** Takie trikowe [bad'] wciąż pozwala nam bez większych przeszkód
    zdefiniować zapętlającą się funkcję [loop']. Osiągnęliśmy więc
    pełen sukces.

    W ogólności nasz trik możnaby sformułować tak: jeżeli mamy konstruktor
    negatywny typu [T], to możemy wyjąć z niego funkcję [T -> A], gdzie [A]
    jest najmniejszym z typów występujących po prawych stronach strzałek.

    No, teraz to już na pewno mamy obcykane wszystkie przypadki, prawda?
    Tadeuszu Sznuku przybywaj: "Otóż nie tym razem!". *)

End T5.

Module T6.

Axioms
  (T6 : Type)
  (c0 : (((T6 -> unit) -> bool) -> Color) -> T6)
  (dcase :
    forall
      (P : T6 -> Type)
      (Pc0 : forall f : ((T6 -> unit) -> bool) -> Color, P (c0 f)),
        {f : forall x : T6, P x |
          forall g : ((T6 -> unit) -> bool) -> Color,
            f (c0 g) = Pc0 g}).

(** Kolejnym upierdliwym przypadkiem, burzącym nawet nasz ostateczny
    trik, jest sytuacja, w której po prawej stronie strzałki wystąpi
    typ [unit]. Oczywiście zgodnie z trikiem możemy z [T6] wyciągnąć
    surjekcję [T6 -> unit], ale jest ona oczywiście bezużyteczna, bo
    taką samą możemy zrobić za darmo, stale zwracając po prostu [tt].
    Surjekcja ta nie wystarcza rzecz jasna, żeby odpalić twierdzenie
    Cantora.

    Tym razem jednak nie powinniśmy spodziewać się, że upierdliwość tę
    będzie dało się jakoś obejść. Typ [T6 -> unit] jest jednoelementowy
    (jedynym elementem jest [fun _ => tt]) podobnie jak [unit]. Bardziej
    poetycko możemy powiedzieć, że [T6 -> unit] i [unit] są izomorficzne,
    czyli prawie równe - różnią się tylko nazwami elementów ("nazwa"
    jedynego elementu [unit]a to [tt]).

    Skoro tak, to typ konstruktora [c0], czyli
    [(((T6 -> unit) -> bool) -> Color) -> T6)], możemy równie dobrze
    zapisać jako [((unit -> bool) -> Color) -> T6)]. Zauważmy teraz,
    że [unit -> bool] jest izomorficzne z [bool], gdyż ma tylko dwa
    elementy, a mianowicie [fun _ => true] oraz [fun _ => false].
    Tak więc typ [c0] możemy jeszcze prościej zapisać jako
    [(bool -> Color) -> T6], a to oznacza, że typ [T6] jest jedynie
    owijką na funkcje typu [bool -> Color]. Twierdzenie Cantora nie
    pozwala tutaj uzyskać sprzeczności.

    Czy zatem takie typy sa legalne? Syntaktycznie nie - Coq odrzuca je
    podobnie jak wszystkie inne negatywne typy induktywne. Semantycznie
    również nie - o ile nie możemy uzyskać jawnej sprzeczności, to nasze
    rozważania o nieterminacji wciąż są w mocy.

    Przypomnij sobie poprzedni przykład i nieudaną próbę wyłuskania z
    [T5] surjekcji [T5 -> nat]. Udało nam się zaimplementować funkcję
    [bad], której surjektywności nie potrafiliśmy pokazać, ale pomimo
    tego bez problemu udało nam się użyć jej do napisania funkcji [loop].
    W obecnym przykładzie jest podobnie i nieterminacja to najlepsze, na
    co możemy liczyć. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [bad], a następnie użyj jej do zdefiniowania funkcji
    [loop]. Zademonstruj w sposób podobny jak poprzednio, że [loop] się
    zapętla. *)

(* begin hide *)
Definition bad : T6 -> (T6 -> unit).
Proof.
  apply (dcase (fun _ => T6 -> _)).
  intros f x.
  apply (
    fun c : Color =>
    match c with
        | R => tt
        | G => tt
        | B => tt
    end).
  apply f. intro g.
  apply (
    fun u : unit =>
    match u with
        | tt => true
    end).
  exact (g x).
Defined.

Definition loop (x : T6) : unit := bad x x.

Lemma loop_nontermination :
  tt = loop (c0 (
    fun g : (T6 -> unit) -> bool =>
    match g loop with
        | true => R
        | false => G
    end)).
Proof.
  unfold loop, bad. destruct (dcase _) as [bad eq].
  rewrite 4!eq.
Abort.
(* end hide *)

End T6.

(** No, teraz to już na pewno wiemy wszystko... *)

(** **** Ćwiczenie *)

(** Otóż nie do końca. Ostatnim hamulcowym, groźniejszym nawet niż [unit],
    jest wystąpienie po prawej stronie strzałki typu (czy raczej zdania)
    [False]. W tym przypadku nie tylko nie pomaga nam Cantor, ale nie
    pomaga też nieterminacja, gdyż najzwyczajniej w świecie nie da się
    zdefiniować żadnej funkcji.

    Jako, że za cholerę nie wiem, co z tym fantem zrobić, zostawiam go tobie
    jako ćwiczenie: wymyśl metodę pokazywania nielegalności negatywnych typów
    induktywnych, w których po prawej stronie strzałki jest co najmniej
    jedno wystąpienie [False]. *)

Module T8.

Axioms
  (T8 : Type)
  (c0 : (((T8 -> bool) -> False) -> Color) -> T8)
  (dcase :
    forall
      (P : T8 -> Type)
      (Pc0 : forall f : ((T8 -> bool) -> False) -> Color, P (c0 f)),
        {f : forall x : T8, P x |
          forall g : ((T8 -> bool) -> False) -> Color,
            f (c0 g) = Pc0 g}).

(* begin hide *)

Definition bad : T8 -> (T8 -> bool).
Proof.
  apply (dcase (fun _ => T8 -> _)).
  intros f x.
  apply (
    fun c : Color =>
    match c with
        | R => true
        | _ => false
    end).
  apply f. intro g.
Abort.

(* end hide *)

End T8.



(** ** Promocja 2 w 1 czyli paradoksy Russella i Girarda *)

(** _Istnieje teoria, że jeśli kiedyś ktoś się dowie, dlaczego powstało i
    czemu służy uniwersum, to zniknie ono i zostanie zastąpione czymś
    znacznie dziwaczniejszym i jeszcze bardziej pozbawionym sensu_. *)

(** _Istnieje także teoria, że dawno już tak się stało_. *)

(** Douglas Adams, _Restauracja na końcu wszechświata_ *)

(** W poprzednich podrozdziałach poznaliśmy twierdzenie Cantora oraz
    nauczyliśmy się używać go jako młota na negatywne typy induktywne.

    W tym podrozdziale zapoznamy się z dwoma paradoksami (a precyzyjniej
    pisząc, z dwoma wersjami tego samego paradoksu), które okażą się być
    ściśle powiązane z twierdzeniem Cantora, a które będą służyć nam gdy
    staniemy w szranki z negatwynymi typami induktywno-rekurencyjnymi
    (czyli tymi, które definiuje się przez indukcję-rekursję). O tak: w
    tym podrozdziale, niczym Thanos, staniemy do walki przeciw uniwersum!

    Zacznijmy od paradoksu Russella. Jest to bardzo stary paradoks, odkryty
    w roku 1901 przez... zgadnij kogo... gdy ów człek szukał dziury w całym
    w naiwnej teorii zbiorów (która to teoria jest już od dawna martwa).

    Sformułowanie paradoksu brzmi następująco: niech V będzie zbiorem
    wszystkich zbiorów, które nie należą same do siebie. Pytanie: czy
    V należy do V?

    Gdzie tu paradoks? Otóż jeżeli V należy do V, to na mocy definicji V,
    V nie należy do V. Jeżeli zaś V nie należy do V, to na mocy definicji V,
    V należy do V. Nie trzeba chyba dodawać, że jednoczesne należenie i
    nienależenie prowadzi do sprzeczności. *)

(** **** Ćwiczenie *)

(** To genialne ćwiczenie wymyśliłem dzięki zabłądzeniu na esperanckiej
    Wikipedii (ha! nikt nie spodziewał się esperanckiej Wikipedii w
    ćwiczeniu dotyczącym paradoksu Russella). Ćwiczenie brzmi tak:

    W Wikipedii niektóre artykuły są listami (nie, nie w sensie typu
    induktywnego :)), np. lista krajów według PKB per capita. Pytanie:
    czy można stworzyć w Wikipedii listę wszystkich list? Czy na liście
    wszystkich list ona sama jest wymieniona? Czy można w Wikipedii
    stworzyć listę wszystkich list, które nie wymieniają same siebie? *)

(** Na czym tak naprawdę polega paradoks? Jakiś mądry (czyli przemądrzały)
    filozof mógłby rzec, że na nadużyciu pojęcia zbioru... albo czymś
    równie absurdalnym. Otóż nie! Paradoks Russella polega na tym samym,
    co cała masa innych paradoksów, czyli na autoreferencji.

    Z autoreferencją spotkaliśmy się już co najmniej raz, w rozdziale
    pierwszym. Przypomnij sobie, że golibroda goli tych i tylko tych,
    którzy sami siebie nie golą. Czy golibroda goli sam siebie?

    Takie postawienie sprawy daje paradoks. Podobnie z Russellem: V zawiera
    te i tylko te zbiory, które nie zawierają same siebie. Czy V zawiera
    V? Wot, paradoks. Żeby lepiej wczuć się w ten klimat, czas na więcej
    ćwiczeń. *)

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

(** Dobra, wystarczy już tych paradoksów... a nie, czekaj. Przecież został
    nam do omówienia jeszcze paradoks Girarda. Jednak poznawszy już tajniki
    autoreferencji, powinno pójść jak z płatka.

    Paradoks Girarda to paradoks, który może zaistnieć w wielu systemach
    formalnych, takich jak teorie typów, języki programowania, logiki i
    inne takie. Źródłem całego zła jest zazwyczaj stwierdzenie w stylu
    [Type : Type]. *)

Check Type.
(* ===> Type : Type *)

(** O nie! Czyżbyśmy właśnie zostali zaatakowani przez paradoks Girarda?
    W tym miejscu należy przypomnieć (albo obwieścić - niestety nie pamiętam,
    czy już o tym wspominałem), że [Type] jest w Coqu jedynie synonimem dla
    czegoś w stylu [Type(i)], gdzie [i] jest "poziomem" sortu [Type], zaś
    każde [Type(i)] żyje tak naprawdę w jakimś [Type(j)], gdzie [j] jest
    większe od [i] - typy niższego poziomu żyją w typach wyższego poziomu.
    Będziesz mógł ów fakt ujrzeć na własne oczy, gdy w CoqIDE zaznaczysz
    opcję [View > Display universe levels]. *)

Check Type.
(* ===> Type@{Top.590} : Type@{Top.590+1} *)

(** Jak widać, jest mniej więcej tak jak napisałem wyżej. Nie przejmuj się
    tym tajemniczym [Top] - to tylko nic nieznaczący bibelocik. W twoim
    przypadku również poziom uniwersum może być inny niż [590]. Co więcej,
    poziom ten będzie się zwiększał wraz z każdym odpaleniem komendy [Check
    Type] (czyżbyś pomyślał właśnie o doliczeniu w ten sposób do zyliona?).

    Skoro już wiemy, że NIE zostaliśmy zaatakowani przez paradoks Girarda,
    to w czym problem z tym całym [Type : Type]? Jakiś przemądrzały (czyli
    mądry) adept informatyki teoretycznej mógłby odpowiedzieć, że to zależy
    od konkretnego systemu formalnego albo coś w tym stylu. Otóż niet! Jak
    zawsze, chodzi oczywiście o autoreferencję.

    Gdyby ktoś był zainteresowany, to najlepsze dotychczas sformułowanie
    paradoksu znalazłem (zupełnie przez przypadek, wcale nie szukając) w
    pracy "An intuitionistic theory of types" Martina-Löfa (swoją drogą,
    ten koleś wymyślił podstawy dużej części wszystkiego, czym się tutaj
    zajmujemy). Można ją przeczytać tu (paradoks Girarda jest pod koniec
    pierwszej sekcji):
    archive-pml.github.io/martin-lof/pdfs
    /An-Intuitionistic-Theory-of-Types-1972.pdf

    Nasze sformułowanie paradoksu będzie w sumie podobne do tego z powyższej
    pracy (co jest w sumie ciekawe, bo wymyśliłem je samodzielnie i to przez
    przypadek), ale dowód sprzeczności będzie inny - na szczęście dużo
    prostszy (albo i nie...).

    Dobra, koniec tego ględzenia. Czas na konkrety. *)

(*
Fail Inductive U : Type :=
    | Pi : forall (A : U) (B : El A -> U), U
    | UU : U

with El (u : U) : Type :=
match u with
    | Pi A B => forall x : El A, B x
    | UU => U
end.
*)

(** Powyższa induktywno-rekurencyjna definicja typu [U] (i interpretującej
    go funkcji [El]), którą Coq rzecz jasna odrzuca (uczcijmy ławę oburzonych
    minutą oburzenia) to definicja pewnego uniwersum.

    W tym miejscu wypadałoby wytłumaczyć, czym są uniwersa. Otóż odpowiedź
    jest dość prosta: uniwersum składa się z typu [U : Type] oraz funkcji
    [El : U -> Type]. Intuicja w tym wszystkim jest taka, że elementami
    typu [U] są nazwy typów (czyli bytów sortu [Type]), zaś fukncja [El]
    zwraca typ, którego nazwę dostanie.

    Choć z definicji widać to na pierwszy rzut oka, to zaskakujący może
    wydać ci się fakt, że w zasadzie każdy typ można zinterpretować jako
    uniwersum i to zazwyczaj na bardzo wiele różnych sposobów (tyle ile
    różnych interpretacji [El] jesteśmy w stanie wymyślić). Najlepiej
    będzie, jeżeli przemyślisz to wszystko w ramach ćwiczenia. *)

(** **** Ćwiczenie *)

(** Ćwiczenie będzie konceptualne, a składa się na nie kilka łamigłówek:
    - zinterpretuj [False] jako uniwersum
    - zinterpretuj [unit] jako uniwersum (ile jest możliwych sposobów?)
    - czy istnieje uniwersum, które zawiera nazwę samego siebie? Uwaga:
      to nie jest tak proste, jak może się wydawać na pierwszy rzut oka.
    - wymyśl ideologicznie słuszną interpretację typu [nat] jako uniwersum
      (tak, jest taka). Następnie wymyśl jakąś głupią interpretację [nat]
      jako uniwersum. Dlaczego ta interpretacja jest głupia?
    - zdefiniuj uniwersum, którego elementami są nazwy typów funkcji z
      n-krotek liczb naturalnych w liczby naturalne. Uwaga: rozwiązanie
      jest bardzo eleganckie i możesz się go nie spodziewać.
    - czy istnieje uniwersum, którego interpretacja jest surjekcją? Czy
      da się w Coqu udowodnić, że tak jest albo nie jest? Uwaga: tak
      bardzo podchwytliwe, że aż sam się złapałem. *)

(* begin hide *)

(** Odpowiedzi:
    - [False] to uniwersum puste, w którym nic nie ma - a myślałeś, że co?
    - [unit] to uniwersum zawierające nazwę jednego, wybranego typu - też
      niezbyt odkrywcza odpowiedź. Interpretacji jest tyle ile typów.
    - Tak, istnieje uniwersum zawierające nazwę samego siebie, np. [unit].
    - Ideologicznie słuszna interpretacja [nat] to uniwersum typów
      skończonych - [El n] to typ n-elementowy. Głupia interpretacja:
      każde [n] jest nazwą dla tego samego typu, np. [nat].
    - Tutaj mały twist, bo tym uniwersum też jest [nat]
    - Tutaj też trochę twist, bo takie uniwersum oczywiście istnieje i
      nazywa się... baram bam bam bam... fanfary... [Type]! No cóż, nie
      tego się spodziewałeś, prawda? A co do tego, czy istnieje takie
      induktywne uniwersum, to myślę, że dla każdego kandydata z osobna
      dałoby się pokazać, że nie jest ono wystarczająco dobre. *)

(* end hide *)

(** Skoro wiemy już, czym są uniwersa, przyjrzyjmy się temu, które właśnie
    zdefiniowaliśmy. Żebyś nie musiał w rozpaczy przewijać do góry, tak
    wygląda aksjomatyczne kodowanie tego uniwersum: *)

Module PoorUniverse.

Axioms
  (U : Type)
  (El : U -> Type)

  (Pi : forall (A : U) (B : El A -> U), U)
  (UU : U)

  (El_Pi :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = forall (x : El A), El (B x))
  (El_UU : El UU = U)

  (ind : forall
    (P : U -> Type)
    (PPi :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Pi A B))
    (PUU : P UU),
      {f : forall u : U, P u |
        (forall (A : U) (B : El A -> U),
          f (Pi A B) =
          PPi A B (f A) (fun x : El A => f (B x))) /\
        (f UU = PUU)
      }
  ).

(** [U] to typ, którego elementami są nazwy typów, zaś [El] jest jego
    interpretacją. Nazwy możemy tworzyć tylko na dwa sposoby: jeżeli [A : U]
    jest nazwą typu, zaś [B : El A -> U] jest rodziną nazw typów indeksowaną
    przez elementy typu [A], to [Pi A B] jest nazwą typu
    [forall x : El A, El (B x)]. Drugim konstruktorem jest [UU], które
    oznacza nazwę samego uniwersum, tzn. [El UU = U].

    Reguła indukcji jest dość prosta: jeżeli [P : U -> Type] jest rodziną
    typów (tych prawdziwych) indeksowaną przez [U] (czyli nazwy typów), to
    żeby zdefiniować funkcję [f : forall u : U, P u] musimy mieć dwie rzeczy:
    po pierwsze, musimy pokazać, że [P (Pi A B)] zachodzi, gdy zachodzi [P A]
    oraz [P (B x)] dla każdego [x : El A]. Po drugie, musi zachodzić [P UU].

    Mimo, że uniwersum wydaje się biedne, jest ono śmiertelnie sprzeczne,
    gdyż zawiera nazwę samego siebie. Jeżeli rozwiązałeś (poprawnie, a nie
    na odwal!) ostatnie ćwiczenie, to powinieneś wiedzieć, że niektóre
    uniwersa mogą zawierać nazwy samego siebie i wcale to a wcale nie daje
    to żadnych problemów.

    Dlaczego więc w tym przypadku jest inaczej? Skoro [UU] nie jest złe samo
    w sobie, to problem musi leżeć w [Pi], bo niby gdzie indziej? Zobaczmy
    więc, gdzie kryje się sprzeczność. W tym celu posłużymy się twierdzeniem
    Cantora: najpierw pokażemy surjekcję [U -> (U -> U)], a potem, za pomocą
    metody przekątniowej, że taka surjekcja nie może istnieć. *)

(*
Definition bad (u : U) : U -> U :=
match u with
    | Pi UU B => B
    | _ => fun u : U => U
end.
*)

(** Jeżeli dostajemy [Pi A B], gdzie [A] to [UU], to wtedy [B : El A -> U]
    tak naprawdę jest typu [U -> U] (bo [El UU = U]). W innych przypadkach
    wystarczy po prostu zwrócić funkcję identycznościową. Niestety Coq nie
    wspiera indukcji-rekursji (ława oburzonych), więc funkcję [bad] musimy
    zdefiniować ręcznie: *)

Definition bad : U -> (U -> U).
Proof.
  apply (ind (fun _ => U -> U)).
    Focus 2. exact (fun u : U => u).
    intros A B _ _. revert A B.
      apply (ind (fun A : U => (El A -> U) -> (U -> U))).
        intros; assumption.
        intro B. rewrite El_UU in B. exact B.
Defined.

(** Powyższa definicja za pomocą taktyk działa dokładnie tak samo jak
    nieformalna definicja [bad] za pomocą dopasowania do wzorca. Jedyna
    różnica jest taka, że [El UU] nie jest definicyjnie równe [U], lecz
    są one jedynie zdaniowo równe na mocy aksjomatu [El_UU : El UU = U].
    Musimy więc przepisać go w [B], żeby typy się zgadzały.

    Zanim będziemy mogli pokazać, że [bad] jest surjekcją, czeka nas kilka
    niemiłych detali technicznych (gdyby [El UU] i [U] były definicyjnie
    równe, wszystkie te problemy by zniknęły). *)

Check eq_rect.
(* ===> forall (A : Type) (x : A) (P : A -> Type),
          P x -> forall y : A, x = y -> P y *)

Check eq_rect_r.
(* ===> forall (A : Type) (x : A) (P : A -> Type),
          P x -> forall y : A, y = x -> P y *)

(** [eq_rect] oraz [eq_rect_r] to groźnie wyglądające lematy, ale sprawa tak
    na prawdę jest dość prosta: to one wykonują całą pracę za każdym razem,
    kiedy używasz taktyki [rewrite]. Jeżeli cel jest postaci [P x] i użyjemy
    na nim [rewrite H], gdzie [H : x = y], to [rewrite] zamienia cel na
    [eq_rect _ _ _ cel _ H], które jest już typu [P y]. [eq_rect_r] działa
    podobnie, ale tym razem równość jest postaci [y = x] (czyli obrócona).

    Ponieważ w definicji [bad] używaliśmy [rewrite]'a, to przy dowodzeniu,
    że [bad] jest surjekcją, będziemy musieli zmierzyć się właśnie z
    [eq_rect] i [eq_rect_r]. Stąd poniższy lemat, który mówi mniej więcej,
    że jeżeli przepiszemy z prawa na lewo, a potem z lewa na prawo, to tak,
    jakby nic się nie stało. *)

Lemma right_to_left_to_right :
  forall
    (A : Type) (P : A -> Type) (x y : A) (p : x = y) (u : P y),
      eq_rect x P (@eq_rect_r A y P u x p) y p = u.
Proof.
  destruct p. cbn. reflexivity.
Qed.

(** Dowód jest banalny. Ponieważ [eq_rect] i [eq_rect_r] są zdefiniowane
    przez dopasowanie do wzorca [p : x = y], to wystarczy [p] potraktować
    [destruct]em, a dalej wszystko już ładnie się oblicza. *)

Lemma bad_sur :
  surjective bad.
Proof.
  unfold surjective, bad; intro f.
  destruct (ind _) as [bad [bad_Pi bad_UU]].
  destruct (ind _) as [bad' [bad'_Pi bad'_UU]].
  pose (f' := eq_rect_r (fun T : Type => T -> U) f El_UU).
  exists (Pi UU f'). unfold f'.
  rewrite bad_Pi, bad'_UU, right_to_left_to_right. reflexivity.
Qed.

(** Dlaczego [bad] jest surjekcją? Intuicyjnie pisząc, każdą funkcję
    [U -> U] możemy włożyć do konstruktora [Pi] jako jego drugi argument,
    jeżeli tylko zamienimy pierwsze [U] na [El UU]. Skoro każdą możemy
    tam włożyć, to każdą możemy wyjąć. Ot i cały sekret.

    Technicznie dowód realizujemy tak: odwijamy definicje i wprowadzamy do
    kontekstu funkcję [f]. Następnie rozbijamy [ind _] pochodzące z definicji
    [bad], rozkładając w ten sposób definicję [bad] na właściwe [bad] (sama
    funkcja), [bad'] (wewnętrzna funkcja pomocnicza) oraz równania dla [bad]
    i [bad'] dla poszczególnych przypadków.

    Następnie musimy znaleźć takie [a : U], że [bad a = f]. Robimy to, co
    zasugerowałem wyżej, czyli w [f : U -> U] pierwsze [U] zamieniamy na
    [El UU], uzyskując w ten sposób [f']. Temu właśnie służy użycie
    [eq_rect_r] (nie używamy [rewrite], bo potrzeba nam większej precyzji).

    Wobec tego szukanym przez nas elementem [U], któremu [bad] przyporządkuje
    [f], jest [Pi UU f']. Możemy w tym miejscu odwinąć definicję [f']. Gdyby
    Coq wspierał indukcję-rekursję, to w tym miejscu wystarczyłoby użyć tylko
    [reflexivity] - [bad (Pi UU f')] obliczyłoby się do [f] na mocy definicji
    [bad] oraz dzięki temu, że [El UU] obliczyłoby się do [U]. Niestety Coq
    nie wspiera indukcji rekursji (ława oburzonych), więc musimy wszystkie
    te trzy kroki obliczeń wykonać ręcznie za pomocą taktyki [rewrite].

    Ufff, udało się! Jeżeli przeraża cię ten dowód - nie martw się. Chodzi
    w nim o to samo, o co chodziło w poprzednich dowodach bycia surjekcją.
    Ten jest po prostu trochę bardziej skomplikowany, bo indukcja-rekursja
    jest nieco bardziej skomplikowana do użycia w Coqu niż prymitywniejsze
    formy indukcji. *)

Definition change : U -> U.
Proof.
  apply ind.
    intros. exact UU.
    exact (Pi UU (fun _ => UU)).
Defined.

(** Teraz czas udowodnić, że [bad] nie jest surjekcją. Zrobimy to metodą
    przekątniową, a w tym celu potrzebować będziemy funkcji [U -> U], która
    dla każdego argumentu zwraca coś, co jest od niego różne.

    Na szczęście sprawa jest prosta: jeżeli argumentem jest [Pi A B], to
    zwracamy [UU], zaś jeżeli [UU], to zwracamy [Pi UU (fun _ => UU)]. *)

Definition discern : U -> bool.
Proof.
  apply ind.
    intros. exact true.
    exact false.
Defined.

(** Przydałaby się też funkcja, która pozwoli nam rozróżnić konstruktory
    typu [U]. Normalnie użylibyśmy do tego taktyki [inversion], ale
    używamy kodowania aksjomatycznego, więc [inversion] nie zadziała i
    musimy ręcznie zaimplementować sobie coś w jej stylu.

    Nasza funkcja dla [Pi] zwraca [true], a dla [UU] daje [false]. *)

Lemma change_neq :
  forall u : U, change u <> u.
Proof.
  apply ind.
    intros A B H1 H2 eq.
      apply (f_equal discern) in eq.
      unfold change, discern in eq.
      destruct (ind _) as [d [d_Pi d_UU]],
               (ind _) as [ch [ch_Pi ch_UU]].
      rewrite d_Pi, ch_Pi, d_UU in eq. inversion eq.
    intro eq.
      apply (f_equal discern) in eq.
      unfold change, discern in eq.
      destruct (ind _) as [d [d_Pi d_UU]],
               (ind _) as [ch [ch_Pi ch_UU]].
      rewrite ch_UU, d_Pi, d_UU in eq. inversion eq.
Qed.

(** Wypadałoby też pokazać, ża nasza funkcja działa tak, jak sobie tego
    życzymy. Dowód jest bardzo prosty, ale aksjomatyczne kodowanie znacznie
    go zaciemnia.

    Zaczynamy od indukcji po [u : U]. W pierwszym przypadku mamy hipotezę
    [eq : change (Pi A B) = Pi A B], a skoro tak, to po zaaplikowaniu
    [discern] musi być także [discern (change (Pi A B)) = discern (Pi A B)].

    Następnie rozkładamy definicje [change] i [discern] na atomy ([change]
    nazywa się teraz [ch], a [discern] nazywa się [d]). Przepisujemy
    odpowiednie równania w hipotezie [eq], dzięki czemu uzyskujemy
    [false = true], co jest sprzeczne. Drugi przypadek jest analogiczny. *)

Lemma bad_not_sur :
  ~ surjective bad.
Proof.
  unfold surjective. intro.
  destruct (H (fun u : U => change (bad u u))) as [u eq].
  apply (f_equal (fun f => f u)) in eq.
  apply (change_neq (bad u u)). symmetry. assumption.
Qed.

(** Teraz możemy już pokazać, że [bad] nie jest surjekcją. W tym celu
    wyobraźmy sobie [bad] jako kwadratową tabelkę, której wiersze i
    kolumny są indeksowane przez [U]. Tworzymy nową funkcję [U -> U]
    biorąc elementy z przekątnej i modyfikując je za pomocą [change].

    Skoro [bad] jest surjekcją, to ta nowa funkcja musi być postaci
    [bad u] dla jakiegoś [u : U]. Aplikując obie strony jeszcze raz
    do [u] dostajemy równanie [bad u u = change (bad u u)], które
    jest sprzeczne na mocy lematu [change_neq]. *)

Definition U_illegal : False.
Proof.
  apply bad_not_sur. apply bad_sur.
Qed.

(** Ponieważ [bad] jednocześnie jest i nie jest surjekcją, nastepuje nagły
    atak sprzeczności. Definicja uniwersum [U] przez indukcję-rekursję jest
    nielegalna. Tak właśnie prezentują się paradoksy Russella i Girarda w
    Coqowym wydaniu. *)

End PoorUniverse.

(** **** Ćwiczenie *)

(** Tak naprawdę, to w tym podrozdziale byliśmy co najwyżej bieda-Thanosem,
    gdyż uniwersum, z którym się ścieraliśmy, samo było biedne. W niniejszym
    ćwiczeniu zmierzysz się z uniwersum, które zawiera też nazwy typu pustego,
    typu [unit] i liczb naturalnych, nazwy produktów, sum i funkcji, a także
    sum zależnych.

    Mówiąc wprost: zakoduj aksjomatycznie poniższą definicję uniwersum [U],
    a następnie udowodnij, że jest ona nielegalna. Nie powinno to być
    trudne - metoda jest podobna jak w przypadku biednego uniwersum. *)

Module NonPoorUniverse.

(*
Fail Inductive U : Type :=
    | Empty : U
    | Unit : U
    | Nat : U
    | Prod : U -> U -> U
    | Sum : U -> U -> U
    | Arr : U -> U -> U
    | Pi : forall (A : U) (B : El A -> U), U
    | Sigma: forall (A : U) (B : El A -> U), U
    | UU : U

with El (u : U) : Type :=
match u with
    | Empty => Empty_set
    | Unit => unit
    | Nat => nat
    | Prod A B => El A * El B
    | Sum A B => El A + El B
    | Arr A B => El A -> El B
    | Pi A B => forall x : El A, B x
    | Sigma A B => {x : El A & El (B x)}
    | UU => U
end.
*)

(* begin hide *)
Axioms
  (U : Type)
  (El : U -> Type)

  (Empty : U)
  (Unit : U)
  (Nat : U)
  (Prod : U -> U -> U)
  (Sum : U -> U -> U)
  (Arr : U -> U -> U)
  (Pi : forall (A : U) (B : El A -> U), U)
  (Sigma : forall (A : U) (B : El A -> U), U)
  (UU : U)

  (El_Empty : El Empty = Empty_set)
  (El_Unit : El Unit = unit)
  (El_Nat : El Nat = nat)
  (El_Prod : forall A B : U, El (Prod A B) = (El A * El B)%type)
  (El_Sum : forall A B : U, El (Sum A B) = (El A + El B)%type)
  (El_Arr : forall A B : U, El (Arr A B) = El A -> El B)
  (El_Pi :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = forall (x : El A), El (B x))
  (El_Sigma :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = {x : El A & El (B x)})
  (El_UU : El UU = U)

  (ind : forall
    (P : U -> Type)
    (PEmpty : P Empty)
    (PUnit : P Unit)
    (PNat : P Nat)
    (PProd :
      forall A B : U, P A -> P B -> P (Prod A B))
    (PSum :
      forall A B : U, P A -> P B -> P (Sum A B))
    (PArr :
      forall A B : U, P A -> P B -> P (Arr A B))
    (PPi :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Pi A B))
    (PSigma :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Sigma A B))
    (PUU : P UU),
      {f : forall A : U, P A |
        (f Empty = PEmpty) /\
        (f Unit = PUnit) /\
        (f Nat = PNat) /\
        (forall A B : U,
          f (Prod A B) = PProd A B (f A) (f B)) /\
        (forall A B : U,
          f (Sum A B) = PSum A B (f A) (f B)) /\
        (forall A B : U,
          f (Arr A B) = PArr A B (f A) (f B)) /\
        (forall (A : U) (B : El A -> U),
          f (Pi A B) =
          PPi A B (f A) (fun x : El A => f (B x))) /\
        (forall (A : U) (B : El A -> U),
          f (Sigma A B) =
          PSigma A B (f A) (fun x : El A => f (B x))) /\
        (f UU = PUU)
      }).

Definition bad : U -> (U -> U).
Proof.
  apply (ind (fun _ => U -> U)).
    1-6,8-9: intros; assumption.
    intros A B _ _. revert A B.
      apply (ind (fun A : U => (El A -> U) -> (U -> U))).
        1-8: intros; assumption.
        intro f. rewrite El_UU in f. exact f.
Defined.

Lemma right_to_left_to_right :
  forall
    (A : Type) (P : A -> Type) (x y : A) (p : x = y) (u : P y),
      eq_rect x P (@eq_rect_r A y P u x p) y p = u.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma bad_sur :
  surjective bad.
Proof.
  unfold surjective, bad; intro f.
  destruct (ind _) as [g H]; decompose [and] H; clear H.
  destruct (ind _) as [h H']; decompose [and] H'; clear H'.
  pose (f' := eq_rect_r (fun T : Type => T -> U) f El_UU).
  exists (Pi UU f').
  rewrite H6. rewrite H17.
  unfold f'. rewrite right_to_left_to_right. reflexivity.
Qed.

Definition change : U -> U.
Proof.
  apply ind.
    exact Nat.
    all: intros; exact Empty.
Defined.

Definition discern : U -> nat.
Proof.
  apply ind; intros.
    exact 0.
    exact 1.
    exact 2.
    exact 3.
    exact 4.
    exact 5.
    exact 6.
    exact 7.
    exact 8.
Defined.

Ltac help H :=
  apply (f_equal discern) in H;
  cbn in H; unfold discern in H;
  destruct (ind _) as [help Hhelp];
  decompose [and] Hhelp; clear Hhelp;
  congruence.

Lemma change_neq :
  forall u : U, change u <> u.
Proof.
  apply ind; unfold change;
  destruct (ind _) as [f H]; decompose [and] H; clear H;
  intros; try help H; help H9.
Qed.

Lemma bad_not_sur :
  ~ surjective bad.
Proof.
  unfold surjective. intro.
  destruct (H (fun u : U => change (bad u u))) as [u eq].
  apply (f_equal (fun f => f u)) in eq.
  apply (change_neq (bad u u)). symmetry. assumption.
Qed.
(* end hide *)

Theorem U_illegal : False.
(* begin hide *)
Proof.
  apply bad_not_sur. apply bad_sur.
Qed.
(* end hide *)

End NonPoorUniverse.

(** ** Pozytywne typy induktywne *)

(** Na koniec rozprawimy się z pozytywnymi typami "induktywnymi" (ale tylko
    do pewnego stopnia; tak po prawdzie, to raczej one rozprawią się z
    nami). *)

Fail Inductive Pos : Type :=
    | Pos0 : ((Pos -> bool) -> bool) -> Pos.
(* ===> The command has indeed failed with message:
        Non strictly positive occurrence of "Pos" in
        "((Pos -> bool) -> bool) -> Pos". *)

(** Coq odrzuca powyższą definicję typu [Pos], gdyż pierwsze wystąpienie [Pos]
    w typie konstruktora [Pos0] nie jest ściśle pozytywne. I faktycznie - gdy
    policzymy niedobrość tego wystąpienia zgodnie z naszym wzorem, to wyjdzie,
    że wynosi ona 2, gdyż [Pos] występuje na lewo od dwóch strzałek (pamiętaj,
    że najbardziej zewnętrzna strzałka, czyli ta, na prawo od której też jest
    [Pos], nie liczy się - wzór dotyczy tylko argumentów konstruktora, a nie
    całego konstruktora). *)

Axioms
  (Pos : Type)
  (Pos0 : ((Pos -> bool) -> bool) -> Pos)
  (dcase :
    forall
      (P : Pos -> Type)
      (PPos0 : forall g : (Pos -> bool) -> bool, P (Pos0 g)),
        {f : forall x : Pos, P x |
          forall g : (Pos -> bool) -> bool,
            f (Pos0 g) = PPos0 g}).

(** Spróbujmy zawalczyć z typem [Pos] naszą metodą opartą o twierdzenie
    Cantora. Najpierw kodujemy typ [Pos] aksjomatycznie, a następnie
    spróbujemy zdefiniować [bad], czyli surjekcję z [Pos] w [Pos -> bool]. *)

Definition bad : Pos -> (Pos -> bool).
Proof.
  apply (dcase (fun _ => Pos -> bool)).
  intros f x.
  apply f. intro y.
  apply f. intro z.
  apply f. intro w.
  (* ad infinitum *)
Abort.

(** Mogłoby się wydawać, że wyciągnięcie z [Pos] funkcji [Pos -> bool]
    nie może być trudniejsze, niż zabranie dziecku cukierka. Niestety
    jednak nie jest tak, gdyż w [Pos] tak naprawdę nie ma żadnej takiej
    funkcji - jest funkcja [(Pos -> bool) -> bool], a to już zupełnie
    coś innego.

    Żeby lepiej zrozumieć tę materię, musimy metaforycznie zinterpretować
    znany nam już współczynnik niedobrości i wynikający z niego podział
    na wystąpienia ściśle pozytywne, pozytywne i negatywne. Dzięki tej
    interpretacji dowiemy się też, dlaczego nieparzysta niedobrość jest
    negatywna, a niezerowa parzysta jest pozytywna.

    Najprościej jest zinterpretować wystąpienia ściśle pozytywne, gdyż
    mieliśmy już z nimi sporo do czynienia. Weźmy konstruktor
    [cons : A -> list A -> list A]. Jest tutaj jedno ściśle pozytywne
    wystąpienie typu [list A], które możemy interpretować tak: gdy
    używamy dopasowania do wzorca i dopasuje się [cons h t], to "mamy"
    element [t] typu [list A]. Ot i cała filozofia.

    Załóżmy teraz na chwilę, że Coq akceptuje negatywne i pozytywne
    typy induktywne. Co by było, gdybyśmy dopasowali konstruktor postaci
    [c : (T -> bool) -> T]? Tym razem nie mamy elementu typu [T], lecz
    funkcję [f : T -> bool]. Parafrazując: musimy "dać" funkcji [f]
    element typu [T], żeby dostać [bool].

    A co by było, gdybyśmy dopasowali konstruktor postaci
    [c : ((T -> bool) -> bool) -> T]? Tym razem również nie mamy żadnego
    elementu typu [T], lecz funkcję [f : ((T -> bool) -> bool)].
    Parafrazując: musimy dać funkcji [f] jakąś funkcję typu [T -> bool],
    żeby dostać [bool]. Ale gdy konstruujemy funkcję [T -> bool], to na
    wejściu dostajemy [T]. Tak więc początkowo nie mamy żadnego [T], ale
    gdy o nie poprosimy, to możemy je dostać. Ba! Jak pokazuje przykład,
    możemy dostać bardzo dużo [T].

    Taka właśnie jest różnica między ścisłą pozytywnością (mamy coś),
    negatywnością (musimy coś dać) i pozytywnością (możemy coś dostać,
    i to nawet w dużej liczbie sztuk). Zauważmy, że jedynie w przypadku
    negatywnym możemy wyjąć z [T] funkcję [T -> coś] (chyba, że zawadza
    nam [unit] lub [False]), bo to jedyny przypadek, gdy żądają od nas
    [T] (a skoro żądają [T], to muszą mieć funkcję, która coś z tym [T]
    zrobi). W przypadku pozytywnym nie ma żadnej takiej funkcji - to my
    dostajemy [T] i musimy coś z niego wyprodukować, więc to my jesteśmy
    tą funkcją!

    Ufff... mam nadzieję, że powyższa bajeczka jest sformułowana zrozumiale,
    bo lepszego wytłumaczenia nie udało mi się wymyślić.

    Moglibyśmy w tym miejscu zastanowić się, czy nie uda nam się pokazać
    sprzeczności choć na metapoziomie, poprzez napisanie nieterminującej
    funkcji [loop]. Szczerze pisząc, to niezbyt w to wierzę. Przypomnij
    sobie, że okazało się, że funkcja [loop] jest bardzo ściśle powiązana
    z funkcją [bad], zaś esencja nieterminacji polegała na przekazaniu
    do [loop] jako argument czegoś, co zawierało [loop] jako podterm
    (jeżeli nie zauważyłeś, to wszystkie nasze nieterminujące funkcje
    udało nam się zdefiniować jedynie za pomocą reguły zależnej analizy
    przypadków - bez indukcji, bez rekursji!). To daje nam jako taką
    podstawę by wierzyć, że nawet nieterminacja nie jest w tym przypadku
    osiągalna. *)

(* begin hide *)
Definition loop : Pos -> bool.
Proof.
  apply dcase.
  intros f.
  apply f. intro x.
Abort.

(* f : (Pos -> bool) -> bool *)

Fail Fixpoint loop (x : Pos) : bool :=
match x with
    | Pos0 f => f loop
end.

(*

    Niech x := Pos0 (fun y : Pos -> bool => 

    loop (Pos0 (fun _ => true)) =
    (fun _ => true) loop =
    true

*)
(* end hide *)

(** W tym momencie należy sobie zadać zasadnicze pytanie: dlaczego w ogóle
    pozytywne typy induktywne są nielegalne? Przecież odróżnienie wystąpienia
    pozytywnego od negatywnego nie jest czymś trudnym, więc Coq nie może ich
    od tak po prostu nie rozróżniać - musi mieć jakiś powód!

    I faktycznie, powód jest. Nie ma on jednak wiele wspólnego z mechanizmem
    (pozytywnych) typów induktywnych samym w sobie, a z impredykatywnością
    sortu [Prop]. Trudne słowo, co? Nie pamiętam, czy już to wyjaśniałem,
    więc wyjaśnię jeszcze raz.

    Impredykatywność (lub też impredykatywizm) to pewna forma autoreferencji,
    która czasem jest nieszkodliwa, a czasem bardzo mordercza. Przyjrzyjmy
    się następującej definicji: "wujek Janusz to najbardziej wąsata osoba w
    tym pokoju". Definicja ta jest impredykatywna, gdyż definiuje ona wujka
    Janusza poprzez wyróżnienie go z pewnej kolekcji osób, ale definicja tej
    kolekcji osób musi odwoływać się do wujka Janusza ("w pokoju są wujek
    Janusz, ciocia Grażynka, Sebastianek i Karynka"). W Coqu impredykatywny
    jest sort [Prop], co ilustruje przykład: *)

Definition X : Prop := forall P : Prop, P.

(** Definicja zdania [X] jest impredykatywna, gdyż kwantyfikujemy w niej po
    wszystkich zdaniach ([forall P : Prop]), a zatem kwantyfikujemy także
    po zdaniu [X], które właśnie definiujemy.

    Impredykatywność sortu [Prop] jest niegroźna (no chyba, że pragniemy
    pozytywnych typów induktywnych, to wtedy jest), ale impredykatywność
    dla [Type] byłaby zabójcza, co zresztą powinien nam był uświadomić
    paradoks Russella.

    Dobra, koniec gadania. Poniższy przykład pośrednio pochodzi z sekcji
    3.1 pracy "Inductively defined types", której autorami są Thierry
    Coquand oraz Christine Pauling-Mohring, zaś bezpośrednio jest przeróbką
    kodu wziętego z
    vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive *)

Fail Inductive Pos' : Type :=
    | Pos'0 : ((Pos' -> Prop) -> Prop) -> Pos'.

Axioms
  (Pos' : Type)
  (Pos'0 : ((Pos' -> Prop) -> Prop) -> Pos')
  (dcase' :
    forall
      (P : Pos' -> Type)
      (PPos'0 : forall g : (Pos' -> Prop) -> Prop, P (Pos'0 g)),
        {f : forall x : Pos', P x |
          forall g : (Pos' -> Prop) -> Prop,
            f (Pos'0 g) = PPos'0 g}).

(** Jak widać, podejrzanym typem jest [Pos'], bliźniaczo podobne do [Pos],
    ale zamiast [bool] występuje tutaj [Prop]. *)

Definition unwrap : Pos' -> ((Pos' -> Prop) -> Prop).
Proof.
  apply (dcase' (fun _ => (Pos' -> Prop) -> Prop)).
  intros f. exact f.
Defined.

(** Zaczynamy od zdefiniowania funkcji odwijającej konstruktor. *)

Lemma Pos'0_inj :
  forall x y : (Pos' -> Prop) -> Prop,
    Pos'0 x = Pos'0 y -> x = y.
Proof.
  intros.
  apply (f_equal unwrap) in H. unfold unwrap in H.
  destruct (dcase' _) as [unwrap eq].
  rewrite 2!eq in H.
  assumption.
Qed.

(** Dzięki [unwrap] możemy łatwo pokazać, że konstruktor [Pos'0] jest
    injekcją (to coś, co w przypadku zwykłych typów induktywnych dostajemy
    za darmo od taktyki [inversion], ale cóż, nie tym razem!). *)

Definition i {A : Type} : A -> (A -> Prop) := 
  fun x y => x = y.

Lemma i_inj :
  forall (A : Type) (x y : A), i x = i y -> x = y.
Proof.
  unfold i. intros.
  apply (f_equal (fun f => f y)) in H.
  rewrite H. reflexivity.
Qed.

(** Kolejnym krokiem jest zdefiniowanie funkcji [i], która jest injekcją
    z dowolnego typu [A] w typ [A -> Prop]. Zauważmy, że krok ten w
    kluczowy sposób korzysta z równości, żyjącej w sorcie [Prop] - gdyby
    zamiast [Prop] było [bool], nie moglibyśmy zdefiniować tej injekcji. *)

Definition f (P : Pos' -> Prop) : Pos' := Pos'0 (i P).

Lemma f_inj :
  forall P Q : Pos' -> Prop, f P = f Q -> P = Q.
Proof.
  unfold f. intros.
  apply (f_equal unwrap) in H. unfold unwrap in H.
  destruct (dcase' _) as [unwrap eq].
  rewrite 2!eq in H.
  apply i_inj in H. assumption.
Qed.

(** Składając ze soba [i] oraz konstruktor [Pos'0] dostajemy injekcję z
    [Pos' -> Prop] w [Pos']. *)

Definition wut (x : Pos') : Prop :=
  exists P : Pos' -> Prop, f P = x /\ ~ P x.

Definition x : Pos' := f wut.

(** Tutaj następują największe czary, które używają impredykatywności. Nie
    mam żadnego dobrej bajeczki, która by je wyjaśniała. *)

Lemma paradox : wut x <-> ~ wut x.
Proof.
  split.
    destruct 1 as (P & H1 & H2). intro H.
      unfold x in H1. apply f_inj in H1. subst. contradiction.
    intro H. unfold wut. exists wut. split.
      unfold x. reflexivity.
      assumption.
Qed.

(** [paradox] to twierdzenie, które chwyta esencję całej sprawy. Z lewa na
    prawo rozbijamy dowód [wut x] i dostajemy predykat [P]. Wiemy, że
    [f P = x], ale [x = f wut], a ponieważ [f] jest injekcją, to [P = wut].
    To jednak kończy się sprzecznością, bo [wut x], ale [~ P x].

    Z prawa na lewo jest łatwiej. Mamy [~ wut x] i musimy udowodnić [wut x].
    Wystarczy, że istnieje pewien predykat, na który wybieramy oczywiście
    [wut], który spełnia [f wut = x], co jest prawdą na mocy definicji [x],
    oraz [~ wut x], co zachodzi na mocy założenia. *)

Theorem Pos'_illegal : False.
Proof.
  pose paradox. firstorder.
Qed.

(** No i bum. Jak widać, pozytywne typy induktywne prowadzą do sprzeczności,
    ale nie ma to z nimi wiele wspólnego, za to ma wiele wspólnego z sortem
    [Prop] i jego impredykatywnością. *)

(** * Podsumowanie *)

(** To już koniec naszej przydługiej podróży przez mechanizmy definiowania
    typów przez indukcję. W jej trakcie nauczyliśmy się bardzo wielu rzeczy.

    Zaczęliśmy od definiowania prostych enumeracji, operujących na nich
    funkcji definiowanych za pomocą dopasowania do wzorca oraz omówienia
    mechanizmu obliczania wyniku funkcji.

    Następnie poznaliśmy różne rozszerzenia tego podstawowego pomysłu
    definiowania typu za pomocą konstruktorów reprezentujących możliwe
    wartości:
    - rekurencję, dzięki której możemy definiować typy, których
      termy mają najprzeróżniejsze drzewiaste kształty
    - parametryzowane typy induktywne, których głównym zastosowaniem
      jest definiowanie kontenerów o takich samych kształtach, ale
      różnych przechowywanych typach
    - indukcję wzajemną, w praktyce niezbyt użyteczną, dzięki której
      możemy na raz zdefiniować wiele typów odnoszących się do siebie
      nawzajem
    - indeksowane rodziny typów induktywnych, dzięki którym możemy
      przez indukcję definiować predykaty oraz relacje
    - indukcję-indukcję, dzięki której możemy jednocześnie zdefiniować
      typ oraz indeksowaną nim rodzinę typów
    - indukcję-rekursję, dzięki której możemy jednoczesnie zdefiniować
      typ oraz funkcję operującą na tym typie *)

(** Nauczyliśmy się definiować funkcje przez rekursję oraz dowodzić ich
    właściwości przez indukcję. Poznaliśmy definicje poznanych w pierwszym
    rozdziale spójników logicznych oraz odpowiadających im konstrukcji na
    typach, a także definicję bardzo ważnej rodziny typów, czyli równości.

    Poznaliśmy podstawowe obiekty, którymi musi potrafić posługiwać
    się każdy programista, informatyk czy matematyk, a mianowicie
    wartości boolowskie, liczby naturalne oraz listy.

    Nauczyliśmy się formułować i implementować reguły indukcyjne (TODO:
    opisać to w głównym tekście, a nie dopiero w przypomnieniu), a także,
    co powiązane, programować listy przy pomocy foldów i unfoldów.

    Na końcu poznaliśmy kryterium ścisłej pozytywności, które obowiązuje
    wszystkie definicje typów induktywnych. Dowiedzieliśmy się, że negatywne
    typy induktywne prowadzą do nieterminacji, która jest złem wcielonym.
    Poznaliśmy pojęcie surjekcji oraz twierdzenie Cantora, które również
    zabrania negatywnym typom induktywnym istnienia.

    Poznaliśmy też paradoks Russela/Girarda i jego związek z twierdzeniem
    Cantora, autoreferencją oraz ideą uniwersum zdefiniowanego za pomocą
    indukcji-rekursji.

    Ostatecznie dowiedzieliśmy się, że pozytywne typy induktywne także są
    nielegalne, choć jesteśmy wobec nich raczej bezsilni, no chyba że chodzi
    o impredykatywny (tego słowa też się nauczyliśmy) sort [Prop].

    Całkiem sporo, prawda? Nie? No to w kolejnych rozdziałach będzie jeszcze
    więcej. *)