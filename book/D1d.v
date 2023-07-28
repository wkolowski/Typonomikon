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

(** * Jaka piękna katastrofa *)

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

(** * Fantastyczny termination checker i jak go wyłączyć (TODO) *)

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

(** * Dekompozycja reguły indukcji na regułę rekursji i regułę unikalności (TODO) *)

Module nat_ind.

(* begin hide *)
(* TODO: dokończyć dowód indukcja = rekursja + unikalność *)
(* end hide *)

Record recursive
  {A : Type} (f : nat -> A)
  (z : A) (s : A -> A) : Prop :=
{
  f_0 : f 0 = z;
  f_S : forall n : nat, f (S n) = s (f n);
}.

Fixpoint nat_rec'
  {A : Type} (z : A) (s : A -> A) (n : nat) : A :=
match n with
| 0 => z
| S n' => s (nat_rec' z s n')
end.

Lemma recursive_nat_rec' :
  forall
    {A : Type} (z : A) (s : A -> A),
      recursive (nat_rec' z s) z s.
Proof.
  split; cbn; reflexivity.
Qed.

Definition recursor : Type :=
  forall
    (A : Type) (z : A) (s : A -> A),
      {f : nat -> A | recursive f z s}.

Definition uniqueness : Prop :=
  forall
    (A : Type) (f g : nat -> A)
    (z : A) (s : A -> A),
      recursive f z s -> recursive g z s ->
        forall n : nat, f n = g n.

Definition nat_ind' : Type :=
  forall
    (P : nat -> Type)
    (z : P 0) (s : forall n : nat, P n -> P (S n)),
      {f : forall n : nat, P n |
        (f 0 = z) /\
        (forall n : nat, f (S n) = s n (f n))
      }.

Lemma induction_recursor :
  nat_ind' -> recursor.
Proof.
  unfold nat_ind', recursor.
  intros ind A z s.
  destruct (ind (fun _ => A) z (fun _ => s)) as (f & f_0 & f_S).
  exists f.
  split; assumption.
Qed.

Lemma induction_uniqueness :
  nat_ind' -> uniqueness.
Proof.
  unfold nat_ind', uniqueness.
  intros ind A f g z s [f_0 f_S] [g_0 g_S].
  apply (ind (fun n => f n = g n)).
  - now rewrite f_0, g_0.
  - intros n Heq.
    now rewrite f_S, g_S, Heq.
Qed.

Lemma recursor_uniqueness_induction :
  recursor -> uniqueness -> nat_ind'.
Proof.
  unfold recursor, uniqueness, nat_ind'.
  intros rec uniqueness P z s.
  destruct
  (
    rec
      {n : nat & P n}
      (existT _ 0 z)
      (fun '(existT _ n p) => existT _ (S n) (s n p))
  )
  as (f & f_0 & f_S).
  assert (forall n : nat, projT1 (f n) = n).
  {
    unshelve eapply (uniqueness nat (fun n => projT1 (f n)) (fun n => n)).
    - exact 0.
    - exact S.
    - split.
      + now rewrite f_0; cbn.
      + intros n.
        rewrite f_S.
        now destruct (f n); cbn.
    - now split.
  }
  unshelve esplit.
  - intros n.
    erewrite (uniqueness nat (fun n => n) (fun n => projT1 (f n)) 0 S).
    + now destruct (f n); cbn.
    + now split.
    + split.
      * now rewrite f_0; cbn.
      * intros.
        rewrite f_S.
        now destruct (f n0); cbn.
  - split.
Restart.
  unfold recursor, uniqueness, nat_ind'.
  intros rec uniqueness P z s.
  pose (A :=
    {n : nat &
    {x : P n |
      match n as n return (P n -> Prop) with
      | 0 => fun x : P 0 => x = z
      | S n' => fun x : P (S n') => exists x' : P n', x = s n' x'
      end x
    }}
  ).
  unshelve edestruct (rec A) as (f & f_0 & f_S).
  - now exists 0, z.
  - intros (n & x & H).
    now exists (S n), (s n x), x.
  - assert (forall n : nat, projT1 (f n) = n).
    {
      unshelve eapply (uniqueness nat (fun n => projT1 (f n)) (fun n => n)).
      - exact 0.
      - exact S.
      - split.
        + now rewrite f_0; cbn.
        + intros n.
          rewrite f_S.
          now destruct (f n) as (? & ? & ?); cbn.
      - now split.
    }
    unshelve esplit.
    + intros n.
      rewrite <- H.
      exact (proj1_sig (projT2 (f n))).
    + split; cbn in *.
      *
Admitted.

End nat_ind.

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
    - [let x := Prop in 16] - wiązanie [let]
    - ... i wiele, wiele innych!

    Tak wiele różnych sposobów robienia termów to niesamowite bogactwo,
    więc żeby zgodnie z przysłowiem od tego przybytku nie rozbolała nas
    głowa, musimy pomyśleć o nich w nieco bardziej jednorodny sposób.
    Rozwiązanie jest na szczęście bajecznie proste: zauważ, że wszystkie
    powyższe konstrukty językowe można po prostu zawinąć w funkcję, która
    bierze pewną liczbę argumentów (być może zero) i zwraca coś typu
    [nat].

    To jednak nie w pełni mityguje nasz przyszły-niedoszły ból głowy. O ile
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
Require Import List.
Import ListNotations.

Module wut.

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
    (A : Type)
    (P : list A -> Prop)
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
  forall (X : Type) (z : X) (s : X -> X),
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
    (P : N -> Type)
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