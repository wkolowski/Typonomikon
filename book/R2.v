(** * R2: Indukcja i rekursja *)

(** W poprzednim rozdziale dowiedzieliśmy się już co nieco o typach, a
    także spotkaliśmy kilka z nich oraz kilka sposobów tworzenia nowych
    typów ze starych (takich jak np. koniunkcja; pamiętaj, że zdania są
    typami). W tym rozdziale dowiemy się o nich nieco więcej: spotkamy
    się z ich sortami oraz uniwersami, w których żyją; dowiemy się, jak
    definiować nowe typy przy pomocy indukcji oraz jak użyć rekursji do
    tworzenia funkcji, które konstruują i dekonstruują ich termy. *)

(** * Sorty *)

(** Jeżeli przeczytałeś uważnie sekcję "Typy i termy" z poprzedniego
    rozdziału, zauważyłeś zapewne stwierdzenie, że typy są termami.
    W połączeniu ze stwierdzeniem, że każdy term ma swój typ, zrodzić
    musi się pytanie: jakiego typu są typy? Zacznijmy od tego, że
    żeby uniknąć używania mało poetyckiego określenia "typy typów",
    typy typów nazywamy sortami. *)

(** [Prop], jak już wiesz, jest sortem zdań logicznych. Jeżeli
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

    [Set] jest sortem, w którym żyją specyfikacje. Jeżeli [x : A] oraz
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
    specyfikacją — niektóre typy są przecież zdaniami. *)

(** * Hierarchia uniwersów *)

(** Uwaga: ta sekcja jest czysto teoretyczna. Jeżeli boisz
    się uprawiania teorii dla samej teorii, możesz ją pominąć.

    Jeżeli czytasz uważnie, to pewnie wciąż czujesz niedosyt — wszakże
    sorty, jako typy, także są termami. Jakie są więc typy/sorty sortów?
    Przekonajmy się. *)

Check Prop.
(* ===> Prop : Type *)

Check Set.
(* ===> Set : Type *)

(** [Prop] oraz [Set] są typu/sortu [Type], który bywa też nazywany
    uniwersum. To stwierdzenie wciąż jednak pewnie nie zaspakaja twojej
    ciekawości. Pójdźmy więc po nitce do kłębka. *)

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
    View > Display universe levels. *)

Check Type.
(* ===> Type (* Top.7 *) : Type (* (Top.7)+1 *) *)

(** Co oznacza ten dziwny napis? Otóż w Coqu mamy do czynienia nie z
    jednym, ale z wieloma (a nawet nieskończenie wieloma) uniwersami.
    Uniwersa te są numerowane liczbami naturalnymi: najniższe uniwersum
    ma numer 0, a każde kolejne o jeden większy. Wobec tego hierarchia
    uniwersów wygląda tak (użyta notacja nie jest tą, której używa Coq;
    została wymyślona ad hoc):
    - [Set] jest typu/sortu [Type(0)]
    - [Type(0)] jest typu/sortu [Type(1)]
    - w ogólności, [Type(i)] jest typu/sortu [Type(i + 1)] *)

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
    w Coqu atuomatycznie uzyskać program w Scheme, OCamlu lub Haskellu,
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
    [negb (negb true)] i [negb (negb false)]. zauważ, że
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
    która jest rekurencyjna, ale nie jest strukturalnie rekurencyjna. *)

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

(** ** Typy induktywne — pełna moc *)

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
    (w naszym przypadku w definicji [list] argumentem nazywa się [A],
    więc tak też musimy go nazwać w komendzie arguments). Musimy wypisać
    wszystkie argumenty danego konstruktora — ich ilość możemy sprawdzić
    np. komendą [Check].

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
    typów, takich jak listy. *)

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

(** ** Rekordy *)

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

(** ** Klasy *)

(** Mechanizmem ułatwiającym życie jeszcze bardziej niż rekordy są klasy.
    Niech nie zmyli cię ta nazwa — nie mają one nic wspólnego z klasami
    znanymi z języków imperatywnych. Bliżej im raczej do interfejsów,
    od których są zresztą dużo silniejsze.

    W językach imperatywnych interfejs możemy zaimplementować zazwyczaj
    definiując nowy typ. W Coqu możemy uczynić typ instancją klasy w
    dowolnym miejscu — nawet jeżeli to nie my go zdefiniowaliśmy. Co
    więcej, instancjami klas mogą być nie tylko typy, ale dowolne termy.
    Klasy są w Coqu pełnoprawnym tworem — mogą mieć argumenty, zawierać
    inne klasy, być przekazywane jako argumenty do funkcji etc. Używa się
    ich zazwyczaj dwojako:
    - zamiast rekordów (zwiększa to nieco czytelność)
    - jako interfejsy *)

Class EqDec (A : Type) : Type :=
{
    eq_dec : A -> A -> bool;
    eq_dec_spec : forall x y : A, eq_dec x y = true <-> x = y
}.

(** Nie będziemy po raz trzeci powtarzać (kulawej) definicji liczb
    wymiernych — użycie do tego klas zamiast rekordów sprowadza się
    do zamienienia słowa kluczowego [Record] na [Class] w poprzedniej
    definicji.

    Przyjrzyjmmy się za to wykorzystaniu klasy w roli interfejsu.
    Argument [A : Type] po nazwie klasy mówi nam, że nasz interfejs
    będą mogły implementować typy. Dalej zapis [: Type] mówi nam, że
    nasza klasa jest typem — klasy, jako ulepszone rekordy, są typami
    induktywnymi z jednym konstruktorem.

    Nasza klasa ma dwa pola, które będzie musiał podać użytkownik chcący
    uczynić swój typ jej instancją: funkcję [eq_dec] oraz jej specyfikację,
    która mówi nam, że [eq_dec] zwraca [true] wtedy i tylko wtedy, gdy jej
    argumenty są równe.

    Wobec tego typy będące instancjami [EqDec] można interpretować jako
    typy, dla których równość elementów można sprawdzić za pomocą jakiegoś
    algorytmu. Nie wszystkie typy posiadają tę własność — problematyczne
    są szczególnie te, których elementy są w jakiś sposób "nieskończone". *)

Instance EqDec_bool : EqDec bool :=
{
    eq_dec := fun b b' : bool =>
      match b, b' with
        | true, true => true
        | false, false => true
        | _, _ => false
      end
}.
Proof.
  destruct x, y; split; trivial; inversion 1.
Defined.

(** Instancje klas definiujemy przy pomocy słowa kluczowego [Instance].
    Jeżeli używamy klasy jako interfejsu, który implementować mogą typy,
    to zazwyczaj będziemy potrzebować tylko jednej instancji, więc jej
    nazwa będzie niemal identyczna jak jej typ (dzięki temu łatwo będzie
    ją zapamiętać).

    Po symbolu [:=] w nawiasach klamrowych definiujemy pola, które
    nie są dowodami. Całość, jako komenda, musi kończyć się kropką. Gdy
    klasa nie zawiera żadnych pól będących dowodami, definicja jest
    zakończona. W przeciwnym przypadku Coq przechodzi w tryb dowodzenia,
    w którym każdemu polu będącemu dowodem odpowiada jeden podcel. Po
    rozwiązaniu wszystkich podcelów instancja jest zdefiniowana.

    W naszym przypadku klasa ma dwa pola — funkcję i dowód na to, że
    funkcja spełnia specyfikację — więc w nawiasach klamrowych musimy
    podać jedynie funkcję. Zauważmy, że nie musimy koniecznie definiować
    jej właśnie w tym miejscu — możemy zrobić to wcześniej, np. za pomocą
    komendy [Definition] albo [Fixpoint], a tutaj odnieść się do niej
    używając jej nazwy. W przypadku bardziej skomplikowanych definicji
    jest to nawet lepsze wyjście, gdyż zyskujemy dzięki niemu kontrolę
    nad tym, w którym miejscu rozwinąć definicję, dzięki czemu kontekst
    i cel stają się czytelniejsze.

    Ponieważ nasza klasa ma pole, które jest dowodem, Coq przechodzi w tryb
    dowodzenia. Dowód, mimo iż wymaga rozpatrzenia ośmiu przypadków, mieści
    się w jednej linijce — widać tutaj moc automatyzacji. Prześledźmy, co
    się w nim dzieje.

    Najpierw rozbijamy wartości boolowskie [x] i [y]. Nie musimy wcześniej
    wprowadzać ich do kontekstu taktyką [intros], gdyż [destruct] sam potrafi
    to zrobić. W wyniku tego dostajemy cztere podcele. W każdym z nich
    taktyką [split] rozbijamy równoważność na dwie implikacje. Sześć z nich
    ma postać [P -> P], więc radzi sobie z nimi taktyka [trivial]. Dwie
    pozostałe mają przesłanki postaci [false = true] albo [true = false],
    które są sprzeczne na mocy omówionych wcześniej właściwości konstruktorów.
    Taktyką [inversion 1] wskazujemy, że pierwsza przesłanka implikacji
    zawiera taką właśnie sprzeczną równość termów zrobionych różnymi
    konstruktorami, a Coq załatwia za nas resztę.

    Jeżeli masz problem z odczytaniem tego dowodu, koniecznie przeczytaj
    ponownie fragment rozdziału pierwszego dotyczący kombinatorów taktyk.
    Jeżeli nie potrafisz wyobrazić sobie podcelów generowanych przez
    kolejne taktyki, zastąp chwilowo średniki kropkami, a jeżeli to nie
    pomaga, udowodnij całe twierdzenie bez automatyzacji.

    Dzięki takim ćwiczeniom prędzej czy później oswoisz się z tym sposobem
    dowodzenia, choć nie jest to sztuka prosta — czytanie cudzych dowodów
    jest równie trudne jak czytanie cudzych programów.

    Prawie nigdy zresztą nowopowstałe dowody nie są od razu zautomatyzowane
    aż w takim stopniu — najpierw są przeprowadzone w części lub w całości
    ręcznie. Automatyzacja jest wynikiem dostrzeżenia w dowodzie pewnych
    powtarzających się wzorców. Proces ten przypomina trochę
    refaktoryzację kodu — gdy dostrzeżemy powtarzające się fragmenty kodu,
    przenosimy je do osobnych procedur. Analogicznie, gdy dostrzegamy
    powtarzające się fragmenty dowodu, łączymy je kombinatorami taktyk
    lub piszemy własne, zupełnie nowe taktyki (temat pisania własnych
    taktyk poruszę prędzej czy później).

    Od teraz będę zakładał, że nie masz problemów ze zrozumieniem takich
    dowodów i kolejne przykładowe dowody będę pisał w bardziej zwratej
    formie.

    Zauważ, że definicję instancji kończymy komendą [Defined], a nie [Qed],
    jak to było w przypadku dowodów twierdzeń. Wynika to z faktu, że Coq
    inaczej traktuje specyfikacje i programy, a inaczej zdania i dowody.
    W przypadku dowodu liczy się sam fakt jego istnienia, a nie jego treść,
    więc komenda [Qed] każe Coqowi zapamiętać jedynie, że twierdzenie
    udowodniono, a zapomnieć, jak dokładnie wyglądał proofterm. W przypadku
    programów takie zachowanie jest niedopuszczalne, więc [Defined] każe
    Coqowi zapamiętać term ze wszystkimi szczegółami. Jeżeli nie wiesz,
    której z tych dwóch komend użyć, użyj [Defined]. *)

(** **** Ćwiczenie ([EqDec]) *)

(** Zdefiniuj instancje klasy [EqDec] dla typów [unit] oraz [nat]. *)

(* begin hide *)
Instance EqDec_unit : EqDec unit :=
{
    eq_dec := fun _ _ => true
}.
Proof.
  destruct x, y; split; trivial.
Defined.

Instance EqDec_nat : EqDec nat :=
{
    eq_dec := fix f (n m : nat) :=
      match n, m with
        | 0, 0 => true
        | S n', S m' => f n' m'
        | _, _ => false
      end
}.
Proof.
  induction x.
    destruct y; split; trivial; inversion 1.
    induction y.
      split; inversion 1.
      split; intro.
        f_equal. apply IHx. assumption.
        inversion H; subst. destruct (IHx y) as [IHx1 IHx2].
          apply IHx2. trivial.
Defined.
(* end hide *)

(** **** Ćwiczenie (równość funkcji) *)

(** Czy możliwe jest zdefiniowanie instancji klasy [EqDec] dla typu:
    - [bool -> bool]
    - [bool -> nat]
    - [nat -> bool]
    - [nat -> nat]
    - [Prop] *)

(** Jeżeli tak, udowodnij w Coqu. Jeżeli nie, zaargumentuj słownie. *)

(* begin hide *)
(** Odpowiedzi:
    - Tak
    - Tak
    - Nie
    - Nie
    - Nie *)
(* end hide *)

Instance EqDec_option (A : Type) (_ : EqDec A) : EqDec (option A) :=
{
    eq_dec := fun opt1 opt2 : option A =>
      match opt1, opt2 with
        | Some a, Some a' => eq_dec a a'
        | None, None => true
        | _, _ => false
      end
}.
Proof.
  destruct x, y; split; trivial; try (inversion 1; fail); intro.
    apply (eq_dec_spec a a0) in H. subst. trivial.
    apply (eq_dec_spec a a0). inversion H. trivial.
Defined.

(** Instancje klas mogą przyjmować argumenty, w tym również instancje innych
    klas albo inne instancje tej samej klasy. Dzięki temu możemy wyrazić
    ideę interfejsów warunkowych.

    W naszym przypadku typ [option A] może być instancją klasy [EqDec]
    jedynie pod warunkiem, że jego argument również jest instancją tej
    klasy. Jest to konieczne, gdyż porównywanie termów typu [option A]
    sprowadza się do porównywania termów typu [A].

    Zauważ, że kod [eq_dec a a'] nie odwołuje się do definiowanej właśnie
    funkcji [eq_dec] dla typu [option A] — odnosi się do funkcji [eq_dec],
    której dostarcza nam instancja [_ : EqDec A]. Jak widać, nie musimy
    nawet nadawać jej nazwy — Coqa interesuje tylko jej obecność.

    Na podstawie typów termów [a] i [a'], które są Coqowi znane, potrafi
    on wywnioskować, że [eq_dec a a'] nie jest wywołaniem rekurencyjnym,
    lecz odnosi się do instancji innej niż obecnie definiowana. Coq może
    ją znaleźć i odnosić się do niej, mimo że my nie możemy (gdybyśmy
    chcieli odnosić się do tej instancji, musielibyśmy zmienić nazwę z
    [_] na coś innego). *)

(** *** Przydatne komendy *)

(** Ponieważ w następnym zadaniu pojawia się stwierdzenie "znajdź",
    czas, aby opisać kilka przydatnych komend. *)

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

(** **** Ćwiczenie (równość list) *)

(** Zdefiniuj instancję klasy [EqDec] dla typu [list A]. *)

(* begin hide *)
Fixpoint eq_dec_list {A : Type} {eq_dec_A : EqDec A} (l l' : list A)
    : bool :=
match l, l' with
    | nil, nil => true
    | cons h t, cons h' t' => andb (eq_dec h h') (eq_dec_list t t')
    | _, _ => false
end.

Instance EqDec_list (A : Type) (eq_dec_A : EqDec A) : EqDec (list A) :=
{
    eq_dec := eq_dec_list
}.
Proof.
  induction x as [| h t].
    destruct y; split; trivial; inversion 1.
    split.
      induction y as [| h' t']; cbn.
        inversion 1.
        intro. destruct eq_dec_A. apply andb_true_elim in H. destruct H.
          destruct (eq_dec_spec0 h h'), (IHt t').
            rewrite (H1 H), (H3 H0). reflexivity.
      intros ->. induction y as [| h' t']; cbn.
        reflexivity.
        rewrite IHt'. case_eq (eq_dec h' h'); intro.
          reflexivity.
          destruct eq_dec_A; cbn in *. destruct (eq_dec_spec0 h' h').
            rewrite <- H, H1; reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie (równość funkcji 2) *)

(** Niech [A] i [B] będą dowolnymi typami. Zastanów się, kiedy możliwe
    jest zdefiniowanie instancji klasy [EqDec] dla [A -> B]. *)

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

(** ** Typy puste *)

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

(** Widać gołym okiem, iż próba zredukowania (czyli obliczenia) obieku
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

(** ** Parametryczność *)

(** Niech [A B : Set]. Zadajmy sobie następujące pytanie: ile jest funkcji
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
    [forall A : Set, A -> A]? W udzieleniu odpowiedzi pomoże nam
    parametryczność — jedna z właściwości Coqowego polimorfizmu.

    Stwierdzenie, że polimorfizm w Coqu jest parametryczny, oznacza, że
    funkcja biorąca typ jako jeden z argumentów działa w taki sam sposób
    niezależnie od tego, jaki typ przekażemy jej jako argument.

    Konsekwencją tego jest, że funkcje polimorficzne nie wiedzą (i nie
    mogą wiedzieć), na wartościach jakiego typu operują. Wobec tego
    elementem typu [forall A : Set, A -> A] nie może być funkcja, która
    np. dla typu [nat] stale zwraca [42], a dla innych typów po prostu
    zwraca przekazany jej argument.

    Stąd konkludujemy, że typ [forall A : Set, A -> A] ma tylko jeden
    element, a mianowicie polimorficzną funkcję identycznościową. *)

Definition id' : forall A : Set, A -> A :=
  fun (A : Set) (x : A) => x.

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie elementy następujących typów lub udowodnij, że
    istnienie choć jednego elementu prowadzi do sprzeczności:
    - [forall A : Set, A -> A -> A]
    - [forall A : Set, A -> A -> A -> A]
    - [forall A B : Set, A -> B]
    - [forall A B : Set, A -> B -> A]
    - [forall A B : Set, A -> B -> B]
    - [forall A B : Set, A -> B -> A * B]
    - [forall A B : Set, A -> B -> sum A B]
    - [forall A B C : Set, A -> B -> C]
    - [forall A : Set, option A -> A]
    - [forall A : Set, list A -> A] *)

(* begin hide *)
Theorem no_such_fun :
  (forall A B : Set, A -> B) -> False.
Proof.
  intros. exact (X nat False 42).
Qed.
(* end hide *)

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

(** Żeby zrozumieć ten komunikat o błędzie, musimy najpierw przypomnieć sobie
    składnię konstruktorów. Konstruktory typu induktywnego [T] będą mieć (w
    dość sporym uproszczeniu) postać [arg1 -> ... -> argN -> T] — są to funkcje
    biorące pewną (być może zerową) ilość argumentów, a ich przeciwdziedziną
    jest definiowany typ [T].

    Jeżeli definiowany typ [T] nie występuje nigdzie w typach argumentów
    [arg1 ... argN], sytuacja jest klarowna i wszystko jest w porządku.
    W przeciwnym wypadku, w zależności od postaci typów argumentów, mogą
    pojawić się problemy.

    Jeżeli typ któregoś z argumentów jest równy [T], nie ma problemu — jest
    to po prostu argument rekurencyjny. Jeżeli jest on postaci [A -> T] dla
    dowolnego typu [A], również nie ma problemu — dzięki argumentom o takich
    typach możemy reprezentować np. drzewa o nieskończonym współczynniku
    rozgałęzienia. Mówimy, że w [A -> T] typ [T] występuje w pozycji (ściśle)
    pozytywnej.

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

(** **** Ćwiczenie *)

(* Inductive T : Type := *)

(** Rozstrzygnij, czy typ posiadający jeden z następujących konstruktorów
    spełnia kryterium ścisłej pozytywności. Następnie sprawdź w Coqu, czy
    udzieliłeś poprawnej odpowiedzi.
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
    - [| C11 : forall A B C : Type, A -> (forall x : T, B) -> (C -> T) -> T] *)

(* begin hide *)
(* C1-C7 są legalne, C8-C11 nie. *)
(* end hide *)

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

(** Taki zabiego daje nam większą swobodę: w każdym konstruktorze
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

(** ** Sumy zależne i podtypy *)

(** W Coqu, w przeciwieństwie do wielu języków imperatywnych, nie ma
    mechanizmu subtypowania, a każde dwa typy są ze sobą rozłączne.
    Nie jest to problemem, gdyż subtypowanie możemy zasymulować za
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

(** ** Rozstrzygalność *)

Theorem excluded_middle :
  forall P : Prop, P \/ ~ P.
Proof.
  intro. left.
Restart.
  intro. right. intro.
Abort.

(** Próba udowodnienia tego twierdzenia pokazuje nam zasadniczą różnicę
    między logiką konstruktywną, która jest domyślną logiką Coqa, oraz
    logiką klasyczną, najpowszechniej znanym i używanym rodzajem logiki.

    Każde zdanie jest, w pewnym "filozoficznym" sensie, prawdziwe lub
    fałszywe i to właśnie powyższe zdanie oznacza w logice klasycznej.
    Logika konstruktywna jednak, jak już wiemy, nie jest logiką prawdy,
    lecz logiką udowadnialności i ma swoją interpretację obliczeniową.
    Powyższe zdanie w logice konstruktywnej oznacza: program komputerowy
    [exluded_middle] rozstrzyga, czy dowolne zdanie jest prawdziwe, czy
    fałszywe.

    Skonstruowanie programu o takim typie jest w ogólności niemożliwe,
    gdyż dysponujemy zbyt małą ilością informacji: nie wiemy czym jest
    zdanie [P], a nie posiadamy żadnego ogólnego sposobu dowodzenia lub
    obalania zdań o nieznanej nam postaci. Nie możemy np. użyć indukcji,
    gdyż nie wiemy, czy zdanie [P] zostało zdefiniowane induktywnie, czy
    też nie. W Coqu jedynym sposobem uzyskania termu o typie [forall
    P : Prop, P \/ ~ P] jest przyjęcie go jako aksjomat. *)

Theorem True_dec : True \/ ~ True.
Proof.
  left. trivial.
Qed.

(** Powyższe dywagacje nie przeszkadzają nam jednak w udowadnianiu,
    że reguła wyłączonego środka zachodzi dla pewnych konkretnych
    zdań. Zdanie takie będziemy nazywać zdaniami rozstrzygalnymi
    (ang. decidable). O pozostałych zdaniach będziemy mówić, że są 
    nierozstrzygalne (ang. undecidable). Ponieważ w Coqu wszystkie
    funkcje są rekurencyjne, a dowody to programy, to możemy powyższą
    definicję rozumieć tak: zdanie jest rozstrzygalne, jeżeli istnieje
    funkcja rekurencyjna o przeciwdzidzinie [bool], która sprawdza, czy
    jest ono prawdziwe, czy fałszywe.

    Przykładami zdań, predykatów czy problemów rozstrzygalnych są:
    - sprawdzanie, czy lista jest niepusta
    - sprawdzanie, czy liczba naturalna jest parzysta
    - sprawdzanie, czy dwie liczby naturalne są równe *)

(** Przykładem problemów nierozstrzygalnych są:
    - dla funkcji [f g : nat -> nat] sprawdzenie, czy
      [forall n : nat, f n = g n] — jest to w ogólności niemożliwe,
      gdyż wymaga wykonania nieskończonej ilości porównań (co nie
      znaczy, że nie da się rozwiązać tego problemu dla niektórych
      funkcji)
    - sprawdzenie, czy słowo o nieskończonej długości jest palindromem *)

(** **** Ćwiczenie *)

Theorem eq_nat_dec :
  forall n m : nat, n = m \/ ~ n = m.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'].
    left. trivial.
    right. inversion 1.
    right. inversion 1.
    destruct (IHn' m').
      left. subst. trivial.
      right. intro. inversion H0. subst. contradiction H. trivial.
Qed.
(* end hide *)

(** *** Techniczne apekty rozstrzygalności *)

(** Podsumowując powyższe rozważania, moglibyśmy stwierdzić: zdanie [P] jest
    rozstrzygalne, jeżeli istnieje term typu [P \/ ~ P]. Stwierdzenie takie
    nie zamyka jednak sprawy, gdyż bywa czasem mocno bezużyteczne.

    Żeby to zobrazować, spróbujmy użyć twierdzenia [eq_nat_dec] do napisania
    funkcji, która sprawdza, czy liczna naturalna [n] występuje na liście
    liczb naturalnych [l]: *)

Fail Fixpoint inb_nat (n : nat) (l : list nat) : bool :=
match l with
    | nil => false
    | cons h t =>
        match eq_nat_dec n h with
            | or_introl _ => true
            | _ => inb_nat n t
        end
end.

(** Coq nie akceptuje powyższego kodu, racząc nas informacją o błędzie: *)

(* Error:
   Incorrect elimination of "eq_nat_dec n h0" in the inductive type "or":
   the return type has sort "Set" while it should be "Prop".
   Elimination of an inductive object of sort Prop
   is not allowed on a predicate in sort Set
   because proofs can be eliminated only to build proofs. *)

(** Nasza porażka wynika z faktu, że do zdefiniowania funkcji, która
    jest programem (jej dziedzina i przeciwdziedzina są sortu [Set])
    próbowaliśmy użyć termu [eq_nat_dec n h], który jest dowodem
    (konkluzją [eq_nat_dec] jest równość, która jest sortu [Prop]).

    Mimo korespondencji Curry'ego-Howarda, która odpowiada za olbrzymie
    podobieństwo specyfikacji i zdań, programów i dowodów, sortu [Set]
    i sortu [Prop], są one rozróżniane i niesie to za sobą konsekwencje:
    podczas gdy programów możemy używać wszędzie, dowodów możemy używać
    jedynie do konstruowania innych dowodów.

    Praktycznie oznacza to, że mimo iż równość liczb naturalnych jest
    rozstrzygalna, pisząc program nie mamy możliwości jej rozstrzygania
    za pomocą [eq_nat_dec]. To właśnie miałem na myśli pisząc, że termy
    typu [P \/ ~ P] są mocno bezużyteczne.

    Uszy do góry: nie wszystko stracone! Jest to tylko drobna przeszkoda,
    którą bardzo łatwo ominąć: *)

Inductive sumbool (A B : Prop) : Set :=
    | left : A -> sumbool A B
    | right : B -> sumbool A B.

(** Typ [sumbool] jest niemal dokładną kopią [or], jednak nie żyje on
    w [Prop], lecz w [Set]. Ta drobna sztuczka, że termy typu
    [sumbool A B] formalnie są programami, mimo że ich naturalna
    interpretacja jest taka sama jak [or], a więc jako dowodu
    dysjunkcji. *)

(** **** Ćwiczenie *)

(** Udowodnij twierdzenie [eq_nat_dec'] o rozstrzygalności [=] na
    liczbach naturalnych. Użyj typu [sumbool]. Następnie napisz
    funkcję [inb_nat], która sprawdza, czy liczba naturalna [n]
    jest obecna na liście [l]. *)

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

(** ** Typy hybrydowe *)

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

(** ** Pięć rodzajów reguł *)

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

(** *** Reguły formacji *)

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

(** *** Reguły wprowadzania *)

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

(** *** Reguły eliminacji *)

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
    H : P [[]], H' : forall (h : A) (t : list A), P t -> P (t ++ [h])
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

(** *** Reguły obliczania *)

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

(** *** Reguły unikalności *)

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

(** * Rekursja *)

(** Powinieneś już potrafić całkiem sprawnie posługiwać się prostą rekursją,
    a skoro tak, to czas poznać teoretyczne podstawy jej funkcjonowania.

    Ogólnie funkcja rekurencyjna to taka, która w swojej definicji odnosi
    się do samej siebie. Rodzaje rekurencji można podzielić w zależności
    od tego, w jaki sposób to robi:
    - Rekursja strukturalna to taka, w której funkcja wywołuje siebie
      na argumentach o coraz mniejszym "rozmiarze".
    - Rekursja dobrze ufundowana to taka, w której funkcja wywołuje siebie
      jedynie na argumentach "mniejszych", gdzie o tym, które termy są
      mniejsze, a które większe, decyduje pewna relacja dobrze ufundowana.
      Intuicyjnie relacja dobrze ufundowana to taka, że nie możemy
      w nieskończoność robić wywołań rekurencyjnych na coraz mniejszych
      argumentach, gdyż w końcu trafimy na najmniejszy.
    - Funkcje f i g są wzajemnie rekurencyjne, gdy funkcja f wywołuje g,
      a g wywołuje f. To, że f nie wywołuje samej siebie bezpośrednio nie
      oznacza wcale, że nie jest rekurencyjna. Schemat ten można uogólnić
      na dowolną ilość funkcji.
    - Rekursja ogólna to taka, w którym funkcja może odwoływać się do
      samej siebie w dowolny sposób. *)

(** ** Rekursja ogólna *)

(** W Coqu rekursja ogólna nie jest dozwolona. Powód jest prozaiczny:
    jest ona sprzeczna. W celu zobrazowania spróbujmy zdefiniować za
    pomocą taktyk następującą funkcję rekurencyjną: *)

Fixpoint loop (u : unit) : False.
Proof.
  apply loop. assumption.
Abort. (* Coq odrzuca komendę [Qed.] *)

(** Przyjrzyjmy się uważnie definicji funkcji [loop]. Mimo, że udało
    nam się ujrzeć znajomy napis "No more subgoals", próba użycia
    komendy [Qed] kończy się błędem. Gdyby tak się nie stało, możliwe
    byłoby skonstruowanie dowodu [False]: *)

(* Definition the_universe_explodes : False := loop tt. *)

(** Aby chronić nas przed tą katastrofą, Coq nakłada na rekurencję
    ograniczenie: argument główny wywołania rekurencyjnego musi być
    strukturalnym podtermem argumentu głównego obecnego wywołania.
    Innymi słowy, dozwolona jest jedynie rekursja strukturalna. *)

(** ** Rekursja strukturalna (todo) *)

(** Przyjrzyjmy się ponownie definicji dodawania: *)

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
    jest argumentem głównym. Definiując funkcje rekurencyjne zazwyczaj
    nie musimy go pisać, gdyż Coq jest w stanie sam wywnioskować, który
    argument jest główny.

    Czym jest argument główny? Aby to zrozumieć, zbadajmy najpierw
    relację bycia podtermem (dla uproszczenia, skupimy się na termach
    typów induktywnych). Relację tę opisują dwie proste zasady:
    - po pierwsze, jeżeli dany term został skonstruowany pewnym konstruktorem,
      to jego podtermami są rekurencyjne argumenty konstruktora. Przykład:
      [0] jest podtermem [S 0], zaś [nil] podtermem [cons 42 nil].
    - po drugie, jeżeli [t1] jest podtermem [t2], a [t2] podtermem [t3],
      to [t1] jest podtermem [t3] — własność ta nazywa się tranzytywnością.
      Przykład: [S 0] jest podtermem [S (S 0)], a zatem [0] jest podtermem
      [S (S 0)]. Podobnie [nil] jest podtermem [cons 666 (cons 42 nil)] *)

(** **** Ćwiczenie *)

(** Zdefiniuj relacje bycia podtermem dla liczb naturalnych i list. *)

(* begin hide *)
Inductive subterm_nat : nat -> nat -> Prop :=
    | subterm_nat_S : forall n : nat, subterm_nat n (S n)
    | subterm_nat_trans : forall x y z : nat,
        subterm_nat x y -> subterm_nat y z -> subterm_nat x z.

Inductive subterm_list {A : Type} : list A -> list A -> Prop :=
    | subterm_list_cons : forall (h : A) (t : list A),
        subterm_list t (h :: t)
    | subterm_list_trans : forall x y z : list A,
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

Goal subterm_list nil (cons 42 nil).
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

Goal subterm_nat 0 (S 0).
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

(** Argument główny to ten, który jest dopasowywany jako pierwszy. Argumentami
    głównymi w wywołaniach rekurencyjnych mogą być jedynie podtermy argumentu
    głównego z obecnego wywołania.

    Argumentem głównym funkcji [plus] jest jej pierwszy argument (o czym
    informuje nas adnotacja [{struct n}]), gdyż to on jest dopasowywany
    jako pierwszy (i jedyny). W przypadku gdy [n] jest równe [S p], [plus]
    jest wywoływany rekurencyjnie z argumentami [p] i [m], co jest dozwolone,
    gdyż jego argument główny, [p], jest podtermem [S p]. *)