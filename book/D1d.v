(** * D1d: Rekursja prymitywna i reguły indukcji [TODO] *)

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

(** * Myślenie rekurencyjne - bottom-up vs top-down (TODO) *)

(** * Jak działa taktyka [induction]? Standardowe reguły indukcji (TODO) *)