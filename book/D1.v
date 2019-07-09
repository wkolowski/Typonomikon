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
    "dopasowywanie do wzorca" (ang. pattern matching; w dalszej części
    będę używał nazwy angielskiej). Pozwala ono sprawdzić, którego
    konstruktora użyto do zrobienia dopasowywanej wartości. Podobnym
    tworem występującym w językach imperatywnych jest instrukcja
    switch, ale pattern matching jest od niej dużo potężniejszy.

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
    wszystkie możliwe redukcje, czyli program zostanie wykonany. Do
    jego wykonania możemy też użyć komend [Eval simpl] oraz [Eval
    compute] (a od wersji Coqa 8.5 także [Eval cbn]). *)

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
    simpl. reflexivity.
    simpl. reflexivity.
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
    taktyki [simpl] redukujemy (czyli wykonujemy) programy
    [negb (negb true)] i [negb (negb false)]. Zauważ, że
    byłoby to niemożliwe, gdyby argument był postaci [b]
    (nie można wtedy zaaplikować żadnej redukcji), ale jest
    jak najbardziej możliwe, gdy jest on postaci [true] albo
    [false] (wtedy redukcja przebiega jak w przykładzie). Na
    koniec używamy taktyki [reflexivity], która potrafi udowodnić
    cel postaci [a = a].

    [destruct] jest taktykowym odpowiednikiem pattern matchingu
    i bardzo często jest używany, gdy mamy do czynienia z czymś,
    co zostało za jego pomocą zdefiniowane.

    Być może poczułeś dyskomfort spowodowany tym, że cel postaci
    [a = a] można udowodnić dwoma różnymi taktykami ([reflexivity]
    oraz [trivial]) albo że termy można redukować na cztery różne
    sposoby ([Eval simpl], [Eval compute], [Eval cbv], [Eval cbn]).
    Niestety, będziesz musiał się do tego przyzwyczaić — język
    taktyka Coqa jest strasznie zabałaganiony i niesie ze sobą
    spory bagaż swej mrocznej przeszłości. Na szczęście od niedawna
    trwają prace nad jego ucywilizowaniem, czego pierwsze efekty
    widać już od wersji 8.5. W chwilach desperacji uratować może
    cię jedynie dokumentacja:
    - https://coq.inria.fr/refman/tactic-index.html
    - https://coq.inria.fr/refman/Reference-Manual010.html *)

Theorem negb_involutive' :
  forall b : bool, negb (negb b) = b.
Proof.
  destruct b; simpl; reflexivity.
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
  destruct b1, b2, b3; simpl; trivial.
Qed.
(* end hide *)

Theorem andb_comm :
  forall b1 b2 : bool,
    andb b1 b2 = andb b2 b1.
(* begin hide *)
Proof.
  destruct b1, b2; simpl; trivial.
Qed.
(* end hide *)

Theorem orb_assoc :
  forall b1 b2 b3 : bool,
    orb b1 (orb b2 b3) = orb (orb b1 b2) b3.
(* begin hide *)
Proof.
  destruct b1, b2, b3; simpl; trivial.
Qed.
(* end hide *)

Theorem orb_comm :
  forall b1 b2 : bool,
    orb b1 b2 = orb b2 b1.
(* begin hide *)
Proof.
  destruct b1, b2; simpl; reflexivity.
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

(** Zdefiniuj funkcję [opposite], które danemu kierunkowi przyporządkowuje
    kierunek do niego przeciwny (czyli północy przyporządkowuje południe
    etc.). Wymyśl i udowodnij jakąś ciekawę specyfikację dla tej funkcji
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

(** Zdefiniuj funkcję [is_opposite], która bierze dwa kierunki i zwraca
    [true], gdy są one przeciwne oraz [false] w przeciwnym wypadku. Wymyśl
    i udowodnij jakąś specyfikację dla tej funkcji. Wskazówka: jakie są jej
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

(** Pokaż, że funkcje [turnL], [turnR] oraz [opposite] są injekcjami i
    surjekcjami (co to dokładnie znacz, dowiemy się później). Uwaga: to
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

(** **** Ćwiczenie (różne enumeracje) TODO *)

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

(** Wymyśl do nich jakieś ciekawe funkcje i twierdzenia. *)

(* begin hide *)
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
    (choć i tutaj rozgałęzienie będzie nieco zdegenerowane ­- każdy term
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
    Wymyśl taką definicję, która na pierwszy rzut oka nie jest
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
  intro. simpl. trivial.
Qed.

(** Tak prosty dowód nie powinien nas dziwić — wszakże twierdzenie to
    wynika wprost z definicji (spróbuj zredukować "ręcznie" wyrażenie
    [0 + n]). *)

Theorem plus_n_O_try1 :
  forall n : nat, plus n 0 = n.
Proof.
  intro. destruct n.
    trivial.
    simpl. f_equal.
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
    simpl. f_equal. assumption.
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
  induction n as [| n']; simpl; intros.
    rewrite plus_n_O. trivial.
    induction m as [| m'].
      simpl. rewrite plus_n_O. trivial.
      simpl. rewrite IHn'. rewrite <- IHm'. simpl. rewrite IHn'.
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
    simpl. trivial.
    simpl. assumption.
Restart.
  induction n; trivial.
Qed.
(* end hide *)

Theorem mult_1_l :
  forall n : nat, mult 1 n = n.
(* begin hide *)
Proof.
  destruct n as [| n'].
    simpl. trivial.
    simpl. rewrite plus_n_O. trivial.
Restart.
  destruct n; simpl; try rewrite plus_n_O; trivial.
Qed.
(* end hide*)

Theorem mult_1_r :
  forall n : nat, mult n 1 = n.
(* begin hide *)
Proof.
  induction n.
    simpl. trivial.
    simpl. rewrite IHn. trivial.
Restart.
  induction n; simpl; try rewrite IHn; trivial.
Qed.
(* end hide *)

(** Jeżeli ćwiczenie było za proste i czytałeś podrozdział o kombinatorach
    taktyk, to spróbuj udowodnić:
    - dwa pierwsze twierdzenia używając nie więcej niż 2 taktyk
    - trzecie bez użycia indukcji, używając nie więcej niż 4 taktyk
    - czwarte używając nie więcej niż 4 taktyk *)

(** Wszystkie dowody powinny być nie dłuższe niż pół linijki. *)

(** **** Ćwiczenie (inne dodawanie) *)

(** Dodawanie można alternatywnie zdefiniować także w sposób przedstawiony
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
    simpl. rewrite plus'_S. rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem plus'_comm :
  forall n m : nat, plus' n m = plus' m n.
(* begin hide *)
Proof.
  intros. generalize dependent n. induction m as [| m']; simpl; intros.
    rewrite plus'_0_n. trivial.
    rewrite IHm'. simpl. trivial.
Qed.
(* end hide *)

Theorem plus'_is_plus :
  forall n m : nat, plus' n m = plus n m.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intro.
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
    konstruktorów są różne. Jest to konieczne, gdyż za pomocą pattern
    machingu możemy rozróżnić różne konstruktory — gdyby były one
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
  rewrite <- H. simpl. trivial.
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
    swoją funkcję bezpośrednio w miejscu, w którym chcesz jej użyć.  *)

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
    można rozróżnić za pomocą dopasowania do wzorca. *)

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

(** ** Ścisła pozytywność *)

(** Poznana przez nas dotychczas definicja typów induktywnych jest niepełna,
    gdyż pominęliśmy kryterium ścisłej pozytywności. Rozważmy następujący
    typ: *)

Fail Inductive wut (A : Type) : Type :=
    | C : (wut A -> A) -> wut A.

(** Uwaga: poprzedzenie komendą [Fail] innej komendy oznajmia Coqowi, że
    spodziewamy się, iż komenda zawiedzie. Coq akceptuje komendę [Fail c],
    jeżeli komenda [c] zawodzi, i wypisuje komunikat o błędzie. Jeżeli
    komenda [c] zakończy się sukcesem, komenda [Fail c] zwróci błąd.

    Komenda [Fail] jest przydatna w sytuacjach takich jak obecna, gdy
    chcemy zilustrować fakt, że jakaś komenda zawodzi. *)

(* Error: Non strictly positive occurrence of "wut"
   in "(wut A -> A) -> wut A". *)

(** Żeby zrozumieć ten komunikat o błędzie, musimy najpierw przypomnieć
    sobie składnię konstruktorów. Konstruktory typu induktywnego [T] będą
    mieć (w dość sporym uproszczeniu) postać [arg1 -> ... -> argN -> T] —
    są to funkcje biorące pewną (być może zerową) ilość argumentów, a ich
    przeciwdziedziną jest definiowany typ [T].

    Jeżeli definiowany typ [T] nie występuje nigdzie w typach argumentów
    [arg1 ... argN], sytuacja jest klarowna i wszystko jest w porządku.
    W przeciwnym wypadku, w zależności od postaci typów argumentów, mogą
    pojawić się problemy.

    Jeżeli typ któregoś z argumentów jest równy [T], nie ma problemu — jest
    to po prostu argument rekurencyjny. Jeżeli jest on postaci [A -> T] dla
    dowolnego typu [A], również nie ma problemu — dzięki argumentom o takich
    typach możemy reprezentować np. drzewa o nieskończonym współczynniku
    rozgałęzienia. Mówimy, że w [A -> T] typ [T] występuje w pozycji (ściśle)
    pozytywnej. Podobnie, [T] występuje na pozycji ściśle pozytywnej w [T].

    Problem pojawia się dopiero, gdy typ argumentu jest postaci [T -> A]
    lub podobnej (np. [A -> T -> B], [T -> T -> A -> B] etc.). W takich
    przypadkach mówimy, że typ [T] występuje na pozycji negatywnej (albo
    "nie-ściśle-pozytywnej").

    Pierwszym, stosunkowo błahym problemem jest fakt, że typy łamiące
    kryterium ścisłej pozytywności nie mają modeli teoriozbiorowych —
    znaczy to po prostu, że nie można reprezentować ich w teorii zbiorów
    za pomocą żadnych zbiorów. Dla wielu matematyków stanowi to problem
    natury praktycznej (są przyzwyczajeni do teorii zbiorów) lub
    filozoficznej.

    Problem ten wynika z faktu, że konstruktory typów induktywnych są
    injekcjami, zaś typy argumentów, w których definiowany typ występuje
    na pozycji negatywnej, są "za duże". Np. w przypadku typu [wut bool]
    konstruktor [C] jest injekcją z [wut bool -> bool] w [wut bool].
    Gdybyśmy chcieli interpretować typy jako zbiory, to zbiór
    [wut bool -> bool] jest "za duży", by można było go wstrzyknąć do
    [wut bool], gdyż jest w bijekcji ze zbiorem potęgowym [wut bool], a
    w teorii zbiorów powszechnie wiadomo, że nie ma injekcji ze zbioru
    potęgowego jakiegoś zbioru do niego samego.

    Nie przejmuj się, jeżeli nie rozumiesz powyższego paragrafu — nie
    jest to główny powód obowiązywania kryterium ścisłej pozytywności,
    wszak jako buntownicy zajmujący się teorią typów nie powinniśmy
    zbytnio przejmować się teorią zbiorów.

    Prawdziwy powód jest inny: dopuszczenie typów łamiących kryterium
    ścisłej pozytywności prowadzi do sprzeczności. Gdyby były one
    legalne, legalna byłaby również poniższa definicja: *)

Fail Definition y (A : Type) : A :=
  let f := (fun x : wut A => match x with | C f' => f' x end)
  in f (C f).

(** Jak widać, gdyby definicja typu [wut] została dopuszczona,
    moglibyśmy uzyskać zapętlający się program umożliwiający nam
    stworzenie elementu dowolnego typu i to bez użycia słowa
    kluczowego [Fixpoint] (program ten jest nazywany zazwyczaj
    kombinatorem Y, ang. Y combinator). Stąd już niedaleko do
    popadnięcia w zupełną sprzeczność: *)

Fail Definition santa_is_a_pedophile : False := y False.

(** UPDATE: dodatkowe wyjaśnienie. Dlaczego [y] się zapętla? Otóż: *)

(** [y False =
     let f := ... in f (C f) =
     let f := ... in match C f with | C f' => f' (C f) end =
     let f := ... in f (C f)] i tak dalej. *)

(** **** Ćwiczenie *)

(* Inductive T : Type := *)

(** Rozstrzygnij, czy następujące konstruktory spełniają kryterium ścisłej
    pozytywności. Następnie sprawdź w Coqu, czy udzieliłeś poprawnej
    odpowiedzi.
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
  intros. simpl. reflexivity.
Qed.

Theorem app_nil_r :
  forall (A : Type) (l : list A), l ++ [] = l.
Proof.
  induction l as [| h t].
    simpl. reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.

(** Sposoby dowodzenia są analogiczne jak w przypadku liczb naturalnych.
    Pierwsze twierdzenie zachodzi na mocy samej definicji funkcji [app]
    i dowód sprowadza się do wykonania programu za pomocą taktyki [simpl].
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
  intro. simpl. reflexivity.
Qed.
(* end hide *)

Theorem length_cons :
  forall (A : Type) (h : A) (t : list A), length (h :: t) <> 0.
(* begin hide *)
Proof.
  simpl. intros. inversion 1.
Qed.
(* end hide *)

Theorem length_app :
  forall (A : Type) (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
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
    https://coq.inria.fr/refman/command-index.html *)

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
    wyczarować term dowolnego typu [A], używając pattern matchingu z
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
  destruct p. simpl. trivial.
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
  induction n as [| n']; simpl; intros.
    trivial.
    induction m as [| m']; rewrite plus_comm; simpl; intros.
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
  intros n m Hn Hm. destruct Hn, Hm; simpl.
    constructor.
    constructor. assumption.
    rewrite plus_comm. simpl. constructor. assumption.
    rewrite plus_comm. simpl. do 2 constructor.
Abort.

(** Niestety, taktyka [destruct] okazała się za słaba. Predykat [even] jest
    induktywny, a zatem bez indukcji się nie obędzie. Rozwiązaniem naszych
    problemów nie będzie jednak indukcja po [n] lub [m], lecz po dowodzie na
    to, że [n] jest parzyste. *)

Theorem even_sum :
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [| n' Hn'].
    simpl. assumption.
    simpl. constructor. assumption.
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
  induction n as [| n']; simpl in *.
    constructor.
    rewrite <- plus_n_O in *. rewrite plus_comm. simpl.
      constructor. assumption.
Qed.
(* end hide *)

Theorem even_is_double :
  forall n : nat, even n -> exists k : nat, n = 2 * k.
(* begin hide *)
Proof.
  induction 1.
    exists 0. trivial.
    destruct IHeven. exists (S x). simpl in *. rewrite <- plus_n_O in *.
      rewrite plus_comm. simpl. do 2 f_equal. assumption.
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
    szczególnie politycznych, a także ekonomistów. Odpowiedź na
    nie jest jednym z największych osiągnięć matematyki w dziejach:
    równość to jeden z typów induktywnych, które możemy zdefiniować
    w Coqu. *)

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
    Coqa, którą jest konwertowalność. 
*)

Theorem eq_refl_alpha :
  forall A : Type, eq (fun x : A => x) (fun y : A => y).
Proof.
  intro. change (fun x : A => x) with (fun y : A => y).
  apply eq_refl.
Qed.

Theorem eq_refl_beta :
  forall m : nat, eq ((fun n : nat => n + n) m) (m + m).
Proof.
  intro. simpl. apply eq_refl.
Qed.

Definition ultimate_answer : nat := 42.

Theorem eq_refl_delta : eq ultimate_answer 42.
Proof.
  unfold ultimate_answer. apply eq_refl.
Qed.

Theorem eq_refl_iota :
  eq 42 (match 0 with | 0 => 42 | _ => 13 end).
Proof.
  simpl. apply eq_refl.
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
    - Redukcja jota wykonuje pattern matching. W naszym przypadku [0]
      jest termem, który postać jest znana (został on skonstruowany
      konstruktorem [0]) i który pasuje do wzorca [| 0 => 42], a zatem
      redukcja jota zamienia całe wyrażenie od [match] aż do [end]
      na [42]. *)

(** Termy [x] i [y] są konwertowalne, gdy za pomocą konwersji alfa oraz
    redukcji beta, delta i jota można zredukować [x] do [y] lub [y] do [x].

    Uważny czytelnik zada sobie w tym momencie pytanie: skoro równość to
    konwertowalność, to jakim cudem równe są termy [0 + n] oraz [n + 0],
    które przecież nie są konwertowalne?

    TODO: udzielić odpowiedzi na to pytanie. *)

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
    simpl. constructor. inversion H; subst.
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
  induction 1; simpl; intro.
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
    simpl. constructor. inversion H; subst.
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
  destruct n as [| n']; simpl; intros.
    assumption.
    constructor. apply odd_even_plus.
      inversion H. assumption.
      assumption.
  destruct n as [| n']; simpl; intros.
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
  induction n as [| n']; simpl in *; constructor.
  rewrite <- plus_n_O in *. rewrite plus_comm. simpl. constructor.
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

(** TODO: napisać tu coś. *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenS : forall n : nat, odd n -> even (S n)

with odd : nat -> Prop :=
    | oddS : forall n : nat, even n -> odd (S n).

Inductive even_odd : bool -> nat -> Prop :=
    | even0' : even_odd true 0
    | evenS' : forall n : nat, even_odd false n -> even_odd true (S n)
    | oddS' : forall n : nat, even_odd true n -> even_odd false (S n).

Definition even' := even_odd true.
Definition odd' := even_odd false.

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

End MutualIndution_vs_InductiveFamilies.

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

(** [ex] to kolejne wcielenia sumy zależnej. Porównaj dokładnie tę
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

(** ** W-typy *)

(** TODO: napisz coś *)

Inductive W (A : Type) (B : A -> Type) : Type :=
    | sup : forall x : A, (B x -> W A B) -> W A B.

Arguments sup {A B} _ _.

Definition boolW : Type :=
  W bool (fun _ => Empty_set).

Definition trueW : boolW :=
  sup true (fun e : Empty_set => match e with end).

Definition falseW : boolW :=
  sup false (fun e : Empty_set => match e with end).

Definition notW : boolW -> boolW :=
  W_rect bool (fun _ => Empty_set) (fun _ => boolW)
         (fun b _ _ => if b then falseW else trueW).

Definition bool_boolW (b : bool) : boolW :=
  if b then trueW else falseW.

Definition boolW_bool : boolW -> bool :=
  W_rect bool (fun _ => Empty_set) (fun _ => bool) (fun b _ _ => b).

Lemma boolW_bool_notW :
  forall b : boolW,
    boolW_bool (notW b) = negb (boolW_bool b).
(* begin hide *)
Proof.
  induction b; cbn. destruct x; cbn; reflexivity.
Qed.
(* end hide *)

Lemma boolW_bool__bool_boolW :
  forall b : bool,
    boolW_bool (bool_boolW b) = b.
(* begin hide *)
Proof.
  destruct b; reflexivity.
Qed.
(* end hide *)

Lemma bool_boolW__bool_boolW :
  forall b : boolW,
    bool_boolW (boolW_bool b) = b.
(* begin hide *)
Proof.
  unfold bool_boolW, boolW_bool. destruct b, x; cbn.
    unfold trueW. f_equal. admit.
    unfold falseW. f_equal. admit.
Admitted.
(* end hide *)

Definition natW : Type :=
  W bool (fun b : bool => if b then Empty_set else unit).

Definition zeroW : natW :=
  sup true (fun e : Empty_set => match e with end).

Definition succW (n : natW) : natW :=
  sup false (fun u : unit => n).

Definition doubleW : natW -> natW :=
  W_rect _ (fun b : bool => if b then Empty_set else unit) (fun _ => natW)
    (fun a =>
      match a with
          | true => fun _ _ => zeroW
          | false => fun _ g => succW (succW (g tt))
      end).

Definition natW_nat :=
  W_rect _ (fun b : bool => if b then Empty_set else unit) (fun _ => nat)
    (fun a =>
      match a with
          | true => fun _ _ => 0
          | false => fun _ g => S (g tt)
      end).

Fixpoint nat_natW (n : nat) : natW :=
match n with
    | 0 => zeroW
    | S n' => succW (nat_natW n')
end.

Lemma natW_nat_doubleW :
  forall n : natW,
    natW_nat (doubleW n) = 2 * natW_nat n.
(* begin hide *)
Proof.
  induction n. destruct x; cbn.
    reflexivity.
    rewrite H. cbn. rewrite <- !plus_n_O, plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma natW_nat__nat_natW :
  forall n : nat,
    natW_nat (nat_natW n) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma nat_natW__nat_natW :
  forall n : natW,
    nat_natW (natW_nat n) = n.
(* begin hide *)
Proof.
  induction n; destruct x; cbn.
    unfold zeroW. f_equal. admit.
    rewrite H. unfold succW. f_equal. admit.
Admitted.
(* end hide *)

(** * Wyższe czary *)

(** Najwyższy czas nauczyć się czegoś tak zaawansowanego, że nawet w Coqu
    (pełnym przecież dziwnych rzeczy) tego nie ma i nie zapowiada się na
    to, że będzie. Mam tutaj na myśli mechanizm definiwania typów, którego
    nazwa jest wybitnie mało oświecająca: indukcja-indukcja. *)

Unset Elimination Schemes.

(** Powyższa komenda mówi Coqowi, żeby nie generował automatycznie reguł
    indukcji. Przyda nam się ona, by uniknąć konfliktów nazw z regułami,
    które będziemy pisać ręcznie. *)

(** ** Przypomnienie *)

(** Zanim jednak wyjaśnimy, co to za stfur, przypomnijmy sobie różne,
    coraz bardziej innowacyjne sposoby definiowania przez indukcję.
    Przypomnimy sobie też, jak sformułować ich reguły rekursji oraz
    indukcji. *)

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
    jakimś inny typie [P] uda nam się znaleźć po jednym elemencie dla każdego
    z elementów naszego typu [I], to możemy zrobić funkcję [I -> P]. *)

Definition I_case_nondep : I_case_nondep_type :=
  fun (P : Type) (c0' c1' c2' : P) (i : I) =>
  match i with
      | c0 => c0'
      | c1 => c1'
      | c2 => c2'
  end.

(** Regułę zdefiniować możemy za pomocą dopasowania do wzorca. *)

Definition I_case_dep_type : Type :=
  forall (P : I -> Type) (c0' : P c0) (c1' : P c1) (c2' : P c2),
    forall i : I, P i.

(** Zależną regułę definiowania przez przypadki możemy uzyskać z poprzedniej
    uzależniając przeciwdziedzinę [P] od dziedziny. *)

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
    tworzyć type, które mają nieskończenie wiele elementów, z których
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

(** Reguła indukcji (czyli induktor - cóż za piękna nazwa!) powstaje z
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

    Uwaga: nazywam reguły nieco inaczej niż te autogenerowane przez Coqa.
    Dla Coqa reguła indukcji dla [I] to nasze [I_ind] z [P : I -> Type]
    zastąpionym przez [P : I -> Prop], zaś Coqowe [I_rec] odpowiadałoby
    naszemu [I_ind] dla [P : I -> Set].

    Jeżeli smuci cię burdel nazewniczy, to nie przejmuj się - kiedyś będzie
    lepiej. Klasyfikacja reguł jest prosta:
    - reguły mogą być zależne lub nie, w zależności od tego czy [P] zależy
      od [I]
    - reguły mogą być rekurencyjne lub nie
    - reguły mogą być dla sortu [Type], [Prop] albo nawet [Set] *)

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
    zrobić funkcję [I -> P]. Jako, że parametry są zawsze takie samo,
    możemy skwantyfikować je na samym początku. *)

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

(** A regułę indukcję uzyskujemy przez uzależnienie [P] od [I]. *)

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

(** Indukcja wzajemna pozwala definiować na raz wiele typów, które mogą
    odwoływać się do siebie nawzajem. Cytując klasyków: smok to wysuszony
    zmok, zmok to zmoczony smok. *)

Definition Smok_case_nondep_type : Type :=
  forall S : Type, (Zmok -> S) -> Smok -> S.

Definition Zmok_case_nondep_type : Type :=
  forall Z : Type, (Smok -> Z) -> Zmok -> Z.

(** Reguła niezależnej analizy przypadków dla [Smok]a wygląda banalnie:
    jeżeli ze [Zmok]a potrafimy wyprodukować [S], to ze [Smok]a też.
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
    funkcję typu [Smok -> S], musimy mieć nie tylko rzeczy w kształcie
    konstruktorów [Smok]a, ale także w kształcie konstruktorów [Zmok]a,
    gdyż rekurencyjna struktura obu typów jest ze sobą nierozerwalnie
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

(** Ostatnią poznaną przez nas innowacją są typy indeksowane. Tutaj również
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

(** ... a w powyższej tak. Jako, że indeksy zmieniają się pomiędzy
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

(** ** Indukcja-indukcja *)

Module ind_ind.

(** Po powtórce nadszedł czas nowości. Zacznijmy od nazwy, która jest iście
    kretyńska: indukcja-indukcja. Każdy rozsądny człowiek zgodzi się,
    że dużo lepszą nazwą byłoby coś w stylu "indukcja wzajemna indeksowana".

    Ta alternatywna nazwa rzuca sporo światła: indukcja-indukcja to połączenie
    i uogólnienie mechanizmów definiowania typów wzajemnie induktywnych oraz
    indeksowanych typów induktywnych.

    Typy wzajemnie induktywne mogą odnosić się do siebie nawzajem, ale co
    to dokładnie znaczy? Ano to, że konstruktory każdego typu mogą brać
    argumenty wszystkch innych typów definiowanych jednocześnie z nim. To
    jest clou całej sprawy: konstruktory.

    A co to ma do typów indeksowanych? Ano, zastanówmy się, co by się stało,
    gdybyśmy chcieli zdefiniować przez wzajemną indukcję typ [A] oraz rodzinę
    typów [B : A -> Type]. Otóż nie da się: konstruktory [A] mogą odnosić
    się do [B] i vice-versa, ale [A] nie może być indeksem [B].

    Indukcja-indukcja to coś, co... tam taram tam tam... pozwala właśnie na
    to: możemy jednocześnie zdefiniować typ i indeksowaną nim rodzinę typów.
    I wszystko to ukryte pod taką smutną nazwą... lobby teoriotypowe nie
    chciało, żebyś się o tym dowiedział.

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

(** Jako się już wcześniej rzekło, indukcja-indukcja nie jest wspierana
    przez Coqa - powyższa definicja kończy się informacją o błędzie: Coq
    nie widzi [slist] kiedy czyta indeksy [ok] właśnie dlatego, że nie
    dopuszcza on możliwości jednoczesnego definiowania rodziny (w tym
    wypadku relacji) [ok] wraz z jednym z jej indeksów, [slist].

    Będziemy zatem musieli poradzić sobie z przykładem jakoś inaczej -
    po prostu damy go sobie za pomocą aksjomatów. Zanim jednak to zrobimy,
    omówimy go dokładniej, gdyż deklarowanie aksjomatów jest niebezpieczne
    i nie chcemy się pomylić.

    Zamysłem powyższego przykładu było zdefiniowanie typu list posortowanych
    [slist R], gdzie [R] pełni rolę relacji porządku, jednocześnie z relacją
    [ok : A -> slist R -> Prop], gdzie [ok x l] wyraża, że dostawienie [x]
    na początek listy posortowanej [l] daje listę posortowaną.

    Przykład jest oczywiście dość bezsensowny, bo dokładnie to samo można
    osiągnąć bez używania indukcji-indukcji - wystarczy najpierw zdefiniować
    listy, a potem relację bycia listą posortowaną, a na koniec zapakować
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

    Regułe indukcji można uzyskać dodając tyle zależności, ile tylko zdołamy
    unieść.

    Zobaczmy więc, jak zrealizować to wszystko za pomocą aksjomatów. *)

Axioms
  (slist : forall {A : Type}, (A -> A -> Prop) -> Type)
  (ok : forall {A : Type} {R : A -> A -> Prop}, A -> slist R -> Prop).

(** Najpierw musimy zadeklarować [slist], gdyż wymaga tego typ [ok]. Obie
    definicje wyglądają dokładnie tak, jak nagłówki w powyższej definicji
    odrzuconej przez Coqa.

    Widać też, że gdybyśmy chcieli zdefiniować rodziny [A] i [B], które są
    nawzajem swoimi indeksami, to nie moglibyśmy tego zrobić nawet za pomocą
    aksjomatów. Rodzi to pytanie o to, które dokładnie definicje przez
    indukcję-indukcję są legalne. Odpowiedź brzmi: nie wiem, ale może kiedyś
    się dowiem. *)

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
    potem [ok]. Musimy to zrobić w tej kolejności, bo konstruktor [ok_snil]
    odnosi się do [snil], a [ok_scons] do [scons].

    Znowu widzimy, że gdyby konstruktory obu typów odnosiły się do siebie
    nawzajem, to nie moglibyśmy zdefiniować takiego typu aksjomatycznie. *)

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
    {g : (forall (h : A) (t : slist R) (p : ok h t), Q h t p) &
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
    Teoretycznie powinny to być dwie reguły (tak jak w przypadku [Smok]a i
    [Zmok]a) - jedna dla [slist] i jedna dla [ok], ale żeby za dużo nie
    pisać, możemy zapisać je razem.

    Typ [A] i relacja [R] są parametrami obu definicji, więc skwantyfikowane
    są na samym początku. Nasza reguła pozwala nam zdefiniować przez wzajemną
    rekursję dwie funkcje, [f : forall l : slist R, P l] oraz
    [g : forall (h : A) (t : slist R) (p : ok h t), Q h t p]. Tak więc [P]
    to kodziedzina [f], a [Q] - [g].

    Teraz potrzebujemy rozważyć wszystkie możliwe przypadki - tak jak przy
    pattern matchingu. Przypadek [snil] jest dość banalny. Przypadek [scons]
    jest trochę cięższy. Przede wszystkim chcemy, żeby konkluzja była postaci
    [P (scons h t p)], ale jak powinny wyglądać hipotezy indukcyjne?

    Jedyna słuszna odpowiedź brzmi: odpowiadają one typom wszystkich możliwych
    wywołań rekurencyjnych [f] i [g] na strukturalnych podtermach
    [scons h t p]. Jedynymi typami spełniającymi te warunki są [P t] oraz
    [Q h t p], więc dajemy je sobie jako hipotezy indukcyjne.

    Przypadki dla [Q] wyglądają podobnie: [ok_snil] jest banalne, a dla
    [ok_scons] konkluzja musi być jedynej słusznej postaci, a hipotezami
    indukcyjnymi jest wszystko, co pasuje.

    W efekcie otrzymujemy dwie funkcje, [f] i [g]. Tym razem następuje jednak
    mały twist: ponieważ nasza definicja jest aksjomatyczna, zagwarantować
    musimy sobie także reguły obliczania, które dotychczas były zamilaczne,
    bo wynikały z definicji przez dopasowanie do wzorca. Teraz wszystkie te
    "dopasowania" musimy napisać ręcznie w postaci odpowiednio
    skwantyfikowanych równań. Widzimy więc, że [Psnil], [Pscons], [Qok_snil]
    i [Qok_scons] odpowiadają klauzulom w dopasowaniu do wzorca.

    Ufff... udało się. Tak spreparowaną definicją aksjomatyczną możemy się
    jako-tako posługiwać: *)

Definition rec'
  {A : Type} {R : A -> A -> Prop}
  (P : Type) (snil' : P) (scons' : A -> P -> P) :
  {f : slist R -> P &
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

(** Możemy na przykład dość łatwo zdefiniować niezależnych rekursor tylko dla
    [slist], nie odnoszący się w żaden sposób do [ok]. Widzimy jednak, że
    "programowanie" w taki aksjomatyczny sposób jest dość ciężkie - zamiast
    eleganckich dopasowań do wzorca musimy ręcznie wpisywać argumenty do
    reguły indukcyjnej. *)

Require Import List.
Import ListNotations.

Definition toList'
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> list A &
    f snil = [] /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = h :: f t
  }.
Proof.
  exact (rec' (list A) [] cons).
Defined.

Definition toList
  {A : Type} {R : A -> A -> Prop} (l : slist R) : list A :=
match @toList' A R with
    | existT _ f _ => f l
end.

(** Używająnie takieg rekursora jest już dużo prostsze, co ilustruje powyższy
    przykład funkcji, która zapomina o tym, że lista jest posortowana i daje
    nam zwykłą listę.

    Przykładowe posortowane listy wyglądają tak: *)

Definition slist_01 : slist le :=
  scons 0
    (scons 1
      snil
      (ok_snil 1))
    (ok_scons 1 snil (ok_snil 1) 0 (le_S 0 0 (le_n 0))).

(** Niezbyt piękna, prawda? *)

Compute toList slist_01.

(** Utrapieniem jest też to, że nasza funkcja się nie oblicza. Jest tak, bo
    została zdefiniowana za pomocą reguły indukcji, która jest aksjomatem.
    Aksjomaty zaś, jak wiadomo (albo i nie - TODO) się nie obliczają.

    Wyniku powyższego wywołania nie będę nawet wklejał, gdyż jest naprawdę
    ohydny. *)

Lemma toList_slist_01_result :
  toList slist_01 = [0; 1].
Proof.
  unfold toList, slist_01.
  destruct toList' as (f & H1 & H2).
  rewrite 2!H2, H1. reflexivity.
Qed.

(** Najlepsze, co możemy osiągnąć, mając taką definicję, to udowodnienie, że
    jej wynik faktycznie jest taki, jak się spodziewamy. *)

(** **** Ćwiczenie *)

(** Zdefiniuj dla list posortowanych funkcję [slen], która liczy ich długość.
    Udowodnij oczywiste twierdzenie wiążące ze sobą [slen], [toList] oraz
    [length]. *)

(* begin hide *)

Definition slen'
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> nat &
    f snil = 0 /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = S (f t)}.
Proof.
  exact (rec' nat 0 (fun _ n => S n)).
Defined.

Definition slen {A : Type} {R : A -> A -> Prop} (l : slist R) : nat :=
match slen' with
    | existT _ f _ => f l
end.

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
  destruct slen' as (f & Hf1 & Hf2), toList' as (g & Hg1 & Hg2).
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
  1-2: unfold toList; destruct toList' as (f & H1 & H2).
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

(** Żeby przekonać się, że przykład był naprawdę bezsensowny, zdefiniuj
    rodzinę typów [blist : (A -> A -> Prop) -> A -> Type], gdzie elementami
    [blist R x] są listy posortowane, których elementy są [R]-większe od [x].
    Użyj [blist] do zdefiniowania typu [slist'' R], a następnie udowodnij,
    że [slist R] i [slist'' R] są sobie równoważne. *)

End ind_ind.

(** **** *)

(** Na koniec wypadałoby jeszcze wspomnieć, do czego tak naprawdę można w
    praktyce użyć indukcji-indukcji (definiowanie list posortowanych nie
    jest jedną z tych rzeczy, o czym przekonałeś się w ćwiczeniach). Otóż
    najciekawszym przykładem wydaje się być formalizacja teorii typów, czyli,
    parafrazując, implementacja Coqa w Coqu.

    Żeby się za to zabrać, musimy zdefiniować konteksty, typy i termy, a
    także relacje konwertowalności dla typów i termów. Są tutaj możliwe dwa
    podejścia:
    - Curry'ego (ang. Curry style lub mądrzej extrinsic style) - staramy
      się definiować wszystko osobno, a potem zdefiniować relacje "term x
      jest typu A w kontekście Γ", "typ A jest poprawnie sformowany w
      kontekście Γ" etc. Najważniejszą cechą tego sposobu jest to, że
      możemy tworzyć termy, którym nie da się przypisać żadnego typu oraz
      typy, które nie są poprawnie sformowane w żadnym kontekście.
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

(** Nagłówki w tej definicji powinniśmy interpretować tak:
    - [Ctx] to typ reprezentujący konteksty.
    - [Ty] ma reprezentować typy, ale nie jest to typ, lecz rodzina typów
      indeksowana kontekstami - każdy typ jest typem w jakimś kontekście,
      np. [list A] jest typem w kontekście zawierającym [A : Type], a nie
      jest typem w pustym kontekście.
    - [Term] ma reprezentować termy, ale nie jest to typ, lecz rodzina typów
      indeksowana kontekstami i typami - każdy term ma jakiś typ, a typy,
      jak już się rzekło, zawsze są typami w jakimś kontekście. Przykład:
      jeżeli [x] jest zmienną, to [cons x nil] jest typu [list A] w
      kontekście, w którym [x] jest typu [A], ale nie ma żadnego typu (i nie
      jest nawet poprawnym termem) w kontekście pustym ani w żadnym, w którym
      nie występuje [x].
    - [TyConv Γ A B] zachodzi, gdy typy [A] i [B] są konwertowalne, czyli
      obliczają się do tego samego (relacja taka jest potrzebna, gdyż w Coqu
      i ogólnie w teorii typów występować mogą takie typy jak [if true then
      nat else bool], który jest konwertowalny z [nat]). Jako się rzekło,
      typy zawsze występują w kontekście, więc konwertowalne mogą być też
      tylko w kontekście.
    - [TermConv Γ A x y] znaczy, że termy [x] i [y] są konwertowalne,
      np. [if true then 5 else 6] jest konwertowalne z [5]. Ponieważ każdy
      term ciągnie za sobą swój typ, [TermConv] ma jako indeks typ [A], a
      ponieważ typ ciągnie za sobą kontekst, indeksem [TermConv] jest także
      [Γ]. *)

(** Jak widać, indukcji-indukcji jest w powyższym przykładzie na pęczki -
    jest ona wręcz teleskopowa, gdyż [Ctx] jest indeksem [Ty], [Ctx] i [Ty]
    są indeksami [Term], a [Ctx], [Ty] i [Term] są indeksami [TermConv].

    Cóż, to by było na tyle w tym temacie. Ława oburzonych wyraża w tym
    momencie swoje najwyższe oburzenie na brak indukcji-indukcji w Coqu:
    https://www.sadistic.pl/lawa-oburzonych-vt22270.htm

    Jednak uszy do góry - istnieją już języki, które jakoś sobie radzą z
    indukcją-indukcją. Jednym z nich jest wspomniana we wstępie Agda,
    którą można znaleźć tu:
    https://agda.readthedocs.io/en/latest/ *)

(** **** Ćwiczenie *)

(** Typ stert binarnych [BHeap R], gdzie [R : A -> A -> Prop] jest relacją
    porządku, składa się z drzew, które mogą być albo puste, albo być węzłem
    przechowującym wartość [v : A] wraz z dwoma poddrzewami [l r : BHeap R],
    przy czym [v] musi być [R]-większe od wszystkich elementów [l] oraz [r].

    Użyj indukcji-indukcji, żeby zdefiniować jednocześnie typ [BHeap R] oraz
    relację [ok], gdzie [ok v h] zachodzi, gdy [v] jest [R]-większe od
    wszystkich elementów [h].

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie sterty [h : BHeap R]. *)

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
    relacją porządku, składa się z drzew, które mogą być albo puste, albo być
    węzłem przechowującym wartość [v : A] wraz z dwoma poddrzewami
    [l r : BST R], przy czym [v] musi być [R]-większe od wszystkich elemtnów
    [l] oraz [R]-mniejsze od wszystkich elementów [r].

    Użyj indukcji-indukcji, żeby zdefiniować jednocześnie typ [BST R] wraz
    z odpowiednimi relacjami zapewniającymi poprawność konstrukcji węzła.
    Wypróbuj trzy podejścia:
    - jest jedna relacja, [oklr], gdzie [oklr v l r] oznacza, że z [v], [l] i
      [r] można zrobić węzeł
    - są dwie relacje, [okl] i [okr], gdzie [okl v l] oznacza, że [v] jest
      [R]-większe od wszystkich elementów [l], zaś [okr v r], że [v] jest
      [R]-mniejsze od wszystkich elementów [r]
    - jest jedna relacja, [ok], gdzie [ok v t] oznacza, że [v] jest
      [R]-mniejsze od wszystkich elementów [t] *)

(** Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów. *)

(* begin hide *)

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

(** A oto kolejny potfur do naszej kolekcji: indukcja-rekursja. Nazwa, choć
    brzmi tak głupio, jak "indukcja-indukcja", niesie ze sobą jednak dużo
    więcej wyobraźni: indukcja-rekursja pozwala nam jednocześnie definiować
    typy induktywne oraz operujące na nich funkcje rekurencyjne.

    Co to dokładnie znaczy? Dotychczas nasz modus operandi wyglądał tak, że
    najpierw definiowaliśmy jakiś typ induktywny, a potem przez rekursję
    definiowaliśmy operujące na nim funkcje, np:
    - najpierw zdefiniowaliśmy typ [nat], a potem dodawanie, mnożenie etc.
    - najpierw zdefiniowaliśmy typ [list A], a potem [app], [rev] etc. *)

(** Dlaczego mielibyśmy chcieć definiować typ i funkcję jednocześnie? Dla
    tego samego, co zawsze, czyli zależności - indukcja-rekursja pozwala,
    żeby definicja typu odnosiła się do funkcji, która to z kolei jest
    zdefiniowana przez rekursję strukturalną po argumencie o tym typie.

    Zobaczmy dobrze nam już znany bezsensowny przykład, czyli listy
    posortowane, tym razem zaimplementowane za pomocą indukcji-rekursji. *)

(*
Inductive slist {A : Type} (R : A -> A -> bool) : Type :=
    | snil : slist R
    | scons : forall (h : A) (t : slist R), ok h t = true -> slist R

with

Definition ok
  {A : Type} {R : A -> A -> bool} (x : A) (t : slist R) : bool :=
match t with
    | snil => true
    | scons h _ _ => R x h
end.
*)

(** Coq niestety nie wspiera indukcji-rekursji, a próba napisania powyższej
    definicji kończy się błędem składni. Podobnie jak poprzednio, pomożemy
    sobie za pomocą aksjomatów, jednak najpierw prześledźmy definicję.

    Typ slist działa następująco:
    - [R] to jakiś porządek. Zauważ, że tym razem [R : A -> A -> bool], a
      więc porządek jest rozstrzygalny
    - [snil] to lista pusta
    - [scons h t p] to lista z głową [h] i ogonem [t], zaś [p : ok h t = true]
      to dowód na to, że dostawienie [h] przed [t] daje listę posortowaną. *)

(** Tym razem jednak [ok] nie jest relacją, lecz funkcją zwracającą [bool],
    która działa następująco:
    - dla [snil] zwróć [true] - każde [h : A] można dostawić do listy pustej
    - dla [scons h _ _] zwróć wynik porównania [x] z [h] *)

(** Istotą mechanizmu indukcji-rekursji w tym przykładzie jest to, że [scons]
    wymaga dowodu na to, że funkcja [ok] zwraca [true], podczas gdy funkcja
    ta jest zdefiniowana przez rekursję strukturalną po argumencie typu
    [slist R].

    Użycie indukkcji-rekursji do zaimplementowania [slist] ma swoje zalety:
    dla konkretnych list (złożonych ze stałych, a nie ze zmiennych) dowody
    [ok h t = true] będą postaci [eq_refl], bo [ok] po prostu obliczy się
    do [true]. W przypadku indukcji-indukcji dowody na [ok h t] były całkiem
    sporych rozmiarów drzewami. Innymi słowy, udało nam się zastąpić część
    termu obliczeniami. Ten intrygujący motyw jeszcze się w przyszłości
    pojawi, gdy omawiać będziemy dowód przez reflekcję.

    Dosyć gadania! Zobaczmy, jak zakodować powyższą definicję za pomocą
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

(** Najpierw musimy zadeklarować [slist], a następnie [ok], gdyż typ [ok]
    zależy od [slist]. Obie definicje wyglądają dokładnie tak, jak nagłówki
    w powyższej definicji odrzuconej przez Coqa.

    Następnym krokiem jest zadeklarowanie konstruktorów [slist] oraz
    równań definiujących funkcję [ok]. *)

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

(** Innym zyskiem z użycia indukcji-rekursji jest postać reguły indukcyjnej:
    jest ona dużo prostsza, niż w przypadku indukcji-indukcji, gdyż teraz
    definiujemy tylko jeden typ, zaś towarzysząca mu funkcja nie wymaga w
    regule niczego specjalnego - po prostu pojawia się w niej tam, gdzie
    spodziewalibyśm się jej po definicji [slist], ale nie robi niczego
    ponad to. *)

(* begin hide *)
Definition rev
  {A : Type} {R : A -> A -> bool}
  (l : slist R) : slist (fun x y => negb (R x y)).
Proof.
  revert l.
  refine (proj1_sig (ind
    A R
    (fun _ => slist (fun x y => negb (R x y)))
    _ _)).
    exact snil.
    intros h t p.
      refine (proj1_sig (ind
        A (fun x y => negb (R x y))
        (fun _ => slist (fun x y => negb (R x y)))
        _ _)).
        exact (scons h snil (ok_snil h)).
        intros. apply (scons h0 t0). assumption.
Defined.

Fixpoint leb (n m : nat) : bool :=
match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
end.

Goal @rev _ leb (scons 2 snil (ok_snil 2)) = scons 2 snil (ok_snil 2).
Proof.
  unfold rev.
  destruct (ind _) as (f & Hf1 & Hf2). cbn in *.
  rewrite Hf2, Hf1.
  destruct (ind _) as (g & Hg1 & Hg2). cbn in *.
  rewrite Hg1. reflexivity.
Qed.

Require Import JMeq.

Lemma rev_rev :
  forall (A : Type) (R : A -> A -> bool) (l : slist R),
    JMeq (rev (rev l)) l.
Proof.
  intros A R.
  refine (proj1_sig (ind
    A R
    (fun l => JMeq (rev (rev l)) l)
    _ _)).
Abort.
(* end hide *)

(** ** Jeszcze straszniejszy potfur *)