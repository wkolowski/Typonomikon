(** * D2b: Rodzaje rekursji [TODO] *)

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

(** * Rekursja strukturalna (TODO) *)

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
| subterm_nat_trans' :
    forall x y z : nat,
      subterm_nat x y -> subterm_nat y z -> subterm_nat x z.

Inductive subterm_list {A : Type} : list A -> list A -> Prop :=
| subterm_list_cons :
    forall (h : A) (t : list A),
      subterm_list t (h :: t)
| subterm_list_trans' :
    forall x y z : list A,
      subterm_list x y -> subterm_list y z -> subterm_list x z.

Inductive trans_clos {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| trans_clos_step : forall x y : A, R x y -> trans_clos R x y
| trans_clos_trans :
    forall x y z : A,
      R x y -> trans_clos R y z -> trans_clos R x z.

Inductive subterm_nat_base : nat -> nat -> Prop :=
| subterm_nat_base_c : forall n : nat, subterm_nat_base n (S n).

Definition subterm_nat' : nat -> nat -> Prop :=
  trans_clos subterm_nat_base.

Inductive subterm_list_base {A : Type} : list A -> list A -> Prop :=
| subterm_list_base_c :
    forall (h : A) (t : list A),
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
    apply Nat.lt_trans with y; assumption.
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
    inversion H; subst. apply Nat.lt_trans with (S x).
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
    eapply Nat.lt_trans; eassumption.
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
    inversion H; subst; cbn in *. apply Nat.lt_trans with (length (h :: x)).
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

(** Funkcja ta próbuje policzyć n-tą
    #<a class='link' href='https://en.wikipedia.org/wiki/Fibonacci_number'>
    liczbę Fibonacciego</a>#, ale słabo jej to wychodzi, gdyż dostajemy
    następujący błąd: *)

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

From Typonomikon Require Import D5.

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

(** Oto definicja funkcji plus, lecz zapisana nieco inaczej, niż gdy
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
      cbn. apply Nat.lt_trans with 1.
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
      rewrite (ack_eq (S m)). apply IHle. apply Nat.le_trans with (S m0).
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
    intros. rewrite rev_rev. reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite merge_eq. case_eq (snoc h1 (rev t1)); intros.
        apply (f_equal length) in H. rewrite length_snoc in H. inv H.
        rewrite <- H, snoc_rev, rev_rev. reflexivity.
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