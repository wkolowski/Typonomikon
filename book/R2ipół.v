(** * R2ipół : Rekursja i indukcja *)

(** W poprzednim rozdziale dość dogłębnie zapoznaliśmy się z mechanizmem
    definiowania induktywnych typów i rodzin typów. Nauczyliśmy się też
    definiować funkcje operujące na ich elementach za pomocą dopasowania
    do wzorca oraz rekursji.

    Indukcja i rekursja są ze sobą bardzo ściśle powiązane. Obie opierają
    się na autoreferencji, czyli odnoszeniu się do samego siebie:
    - liczba naturalna to zero lub następnik liczby naturalnej
    - długość listy złożonej z głowy i ogona to jeden plus długość ogona *)

(** Można użyć nawet mocniejszego stwierdzenia: indukcja i rekursja są
    dokładnie tym samym zjawiskiem. Skoro tak, dlaczego używamy na jego
    opisanie dwóch różnych słów? Cóż, jest to zaszłość historyczna, jak
    wiele innych, które napotkaliśmy. Rozróżniamy zdania i typy/specyfikacje,
    relacje i rodziny typów, dowody i termy/programy etc., choć te pierwsze
    są specjalnymi przypadkami tych drugich. Podobnie indukcja pojawiła się
    po raz pierwszy jako technika dowodzenia faktów o liczbach naturalnych,
    zaś rekursja jako technika pisania programów.

    Dla jasności, terminów tych będziemy używać w następujący sposób:
    - indukcja będzie oznaczać metodę definiowania typów oraz
      metodę dowodzenia
    - rekursja będzie oznaczać metodę definiowania funkcji *)

(** W tym rozdziale zbadamy dokładniej rekursję: poznamy różne jej rodzaje,
    zobaczymy w jaki sposób za jej pomocą można zrobić własne niestandardowe
    reguły indukcyjne, poznamy rekursję (i indukcję) dobrze ufundowaną oraz
    zobaczymy, w jaki sposób połączyć indukcję i rekursję, by móc dowodzić
    poprawności pisanych przez nas funkcji wciśnięciem jednego przycisku
    (no, prawie). *)

(** * Rodzaje rekursji *)

(** Funkcja może w swej definicji odwoływać się do samej siebie na różne
    sposoby. Najważniejszą klasyfikacją jest klasyfikacja ze względu na
    dozwolone argumenty w wywołaniu rekurencyjnym:
    - Rekursja strukturalna to taka, w której funkcja wywołuje siebie
      na argumentach będących podtermami argumentów z obecnego wywołania.
    - Rekursja dobrze ufundowana to taka, w której funkcja wywołuje siebie
      jedynie na argumentach "mniejszych", gdzie o tym, które argumenty są
      mniejsze, a które większe, decyduje pewna relacja dobrze ufundowana.
      Intuicyjnie relacja dobrze ufundowana jest jak drabina: schodząc po
      drabinie w dół kiedyś musimy schodzenie zakończyć. Nie możemy schodzić
      w nieskończoność. *)

(** Mniej ważną klasyfikacją jest klasyfikacja ze względu na... cóż, nie
    wiem jak to ładnie nazwać:
    - Rekursja bezpośrednia to taka, w której funkcja f wywołuje siebie
      samą bezpośrednio.
    - Rekursja pośrednia to taka, w której funkcja f wywołuje jakąś inną
      funkcję g, która wywołuje f. To, że f nie wywołuje samej
      siebie bezpośrednio nie oznacza wcale, że nie jest rekurencyjna.
    - W szczególności, rekursja wzajemna to taka, w której funkcja f
      wywołuje funkcję g, a g wywołuje f.
    - Rzecz jasna rekursję pośrednią oraz wzajemną można uogólnić na dowolną
      ilość funkcji. *)

(** Oczywiście powyższe dwie klasyfikacje to tylko wierzchołek góry lodowej,
    której nie ma sensu zdobywać, gdyż naszym celem jest posługiwanie się
    rekursją w praktyce, a nie dzielenie włosa na czworo. Wobec tego
    wszystkie inne rodzaje rekursji (albo nawet wszystkie możliwe rodzaje
    w ogóle) będziemy nazywać rekursją ogólną.

    Z rekursją wzajemną zapoznaliśmy się już przy okazji badania indukcji
    wzajemnej w poprzednim rozdziale. W innych funkcyjnych językach
    programowania używa się jej zazwyczaj ze względów estetycznych, by móc
    elegancko i czytelnie pisać kod, ale jak widzieliśmy w Coqu jest ona
    bardzo upierdliwa, więc raczej nie będziemy jej używać. Skupmy się
    zatem na badaniu rekursji strukturalnej, dobrze ufundowanej i ogólnej. *)

(** **** Ćwiczenie *)

(** Przypomnij sobie podrozdział o indukcji wzajemnej. Następnie wytłumacz,
    jak przetłumaczyć definicję funkcji za pomocą rekursji wzajemnej na
    definicję, która nie używa rekursji wzajemnej. *)

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

    Fakt, że konstruujemy funkcję za pomocą taktyk, nie ma tu żadnego
    znaczenia, lecz służy jedynie lepszemu zobrazowaniu, dlaczego rekursja
    ogólna jest grzechem. Dokładnie to samo stałoby się, gdybyśmy próbowali
    zdefiniować [loop] ręcznie: *)

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
    jest [u], podczas gdy powinien być nim jakiś podterm [u].

    Zanim jednak dowiemy się, czym jest argument główny, czym są podtermy
    i jak dokładnie Coq weryfikuje poprawność naszych definicji funkcji
    rekurencyjnych, wróćmy na chwilę do indukcji. Jak się zaraz okaże,
    nielegalność rekursji ogólnej wymusza również pewne ograniczenia w
    definicjach induktywnych. *)

(** **** Ćwiczenie *)

(** Ograniczenia nakładane przez Coqa sprawiają, że wszystkie napisane
    przez nas funkcje rekurencyjne muszą się kiedyś zatrzymać i zwrócić
    ostateczny wynik swojego działania. Tak więc nie możemy w Coqu pisać
    funkcji nieterminujących, czyli takich, które się nie zatrzymują.

    Rozważ bardzo interesujące pytanie filozoficzne: czy funkcje, które
    nigdy się nie zatrzymują (lub nie zatrzymują się tylko dla niektórych
    argumentów) mogą być w ogóle do czegokolwiek przydatne?

    Nie daj się wpuścić w maliny. *)

(** * Ścisła pozytywność *)

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

(** * Rekursja strukturalna *)

(** Wiemy już, że rekursja ogólna prowadzi do sprzeczności, a jedyną legalną
    formą rekursji jest rekursja strukturalna. Funkcje rekurencyjne, które
    dotychczas pisaliśmy, były strukturalnie rekurencyjne, więc potrafisz
    już całkiem sprawnie posługiwać się tym rodzajem rekursji. Pozostaje
    nam zatem zbadać jedynie techniczne detale dotyczące sposobu realizacji
    rekursji strukturalnej w Coqu. W tym celu przyjrzyjmy się ponownie
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
    jest przez rekursję po n".

    Czym jest argument główny? Spróbuję wyjasnić to w sposób operacyjny:
    - jako argument główny możemy wskazać dowolny argument, którego typ
      jest induktywny
    - Coq wymusza na nas, aby argumentem głównym wywołania rekurencyjnego
      był podterm argumentu głównego z obecnego wywołania *)

(** Dlaczego taki zabieg chroni nas przed sprzecznością? Przypomnij sobie,
    że termy typów induktywnych muszą być skończone. Parafrazując: są to
    drzewa o skończonym rozmiarze. Ich podtermy są od nich mniejsze, więc
    w kolejnych wywołaniach rekurencyjnych argument główny będzie malał,
    aż w końcu jego rozmiar skurczy się do zera. Wtedy rekursja zatrzyma
    się, bo nie będzie już żadnych podtermów, na których można by zrobić
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

(** Udowodnij, że relacje [subterm_nat] oraz [subterm_list] są antyzwrotne
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

    Dla każdego typu induktywnego możemy zdefiniować relację bycia podtermem
    podobną do tych dla liczb naturalnych i list. Zauważmy jednak, że nie
    możemy za jednym zamachem zdefiniować relacji bycia podtermem dla
    wszystkich typów induktywnych, gdyż nie możemy w Coqu powiedzieć czegoś
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

(** Definicja zdaje się być poprawna: [0] to przypadek bazowy, a gdy [n]
    jest postaci [S n'], wywołujemy funkcję rekurencyjnie na argumencie
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

    Ufff...  udało nam się przebrnąć przez techniczne detale działania
    rekursji strukturalnej. Mogłoby się wydawać, że jest ona mechanizmem
    bardzo upośledzonym, ale z doświadczenia wiesz już, że w praktyce
    omówione wyżej problemy występują raczej rzadko.

    Mogłoby się też wydawać, że skoro wywołania rekurencyjne możemy robić
    tylko na bezpośrednich podtermach dopasowanych we wzorcu, to nie da się
    zdefiniować prawie żadnej ciekawej funkcji. Jak zobaczymy w następnym
    podrozdziale, wcale tak nie jest - dzięki pewnej sztuczce (która jest
    jednocześnie fundamentalną własnością wszystkich możliwych wszechświatów)
    za pomocą rekursji strukturalnej można wyrazić rekursję dobrze ufundowaną,
    która na pierwszy rzut oka jest dużo potężniejsza i daje nam wiele
    możliwości definiowania różnych ciekawych funkcji. *)

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

(** * Rekursja dobrze ufundowana *)

(** Typy induktywne są jak domino - każdy term to jedna kostka, indukcja
    i rekursja odpowiadają zaś temu co tygryski lubią najbardziej, czyli
    reakcji łańcuchowej przewracającej wszystkie kostki.

    Typ [unit] to jedna biedna kostka, zaś [bool] to już dwie biedne
    kostki - [true] i [false]. W obu przypadkach nie dzieje się nic
    ciekawego - żeby wszystkie kostki się przewróciły, musimy pchnąć
    palcem każdą z osobna.

    Typ [nat] jest już ciekawszy - są dwa rodzaje kostek, [0] i [S],
    a jeżeli pchniemy kostkę [0] i między kolejnymi kostkami jest
    odpowiedni odstęp, to równy szlaczek kolejnych kostek przewracać
    się będzie do końca świata.

    Podobnie dla typu [list A] mamy dwa rodzaje kostek - [nil] i [cons],
    ale kostki rodzaju [cons] mają różne kolory - są nimi elementy typu
    [A]. Podobnie jak dla [nat], jeżeli pchniemy kostkę [nil] i odstępy
    między kolejnymi kostkami są odpowiednie, to kostki będą przewracać
    się w nieskończoność. Tym razem jednak zamiast jednego szaroburego
    szlaczka będzie multum kolorowych szlaczków o wspólnych początkach
    (no chyba, że [A = unit] - wtedy dostaniemy taki sam bury szlaczek
    jak dla [nat]).

    Powyższe malownicze opisy przewracających się kostek domino bardziej
    przywodzą mi na myśl indukcję, niż rekursję, chociaż wiemy już, że
    jest to w sumie to samo. Przyjmują one perspektywę "od przodu" -
    jeżeli przewrócimy początkową kostkę i niczego nie spartaczyliśmy,
    kolejne kostki będą przewracać się już same.

    Możemy jednak przyjąć inny sposób patrzenia - perspektywę "od tyłu".
    W tej perspektywie kostka początkowa przewraca się, jeżeli zostanie
    pchnięta palcem, zaś każda dalsza kostka przewraca się, jeżeli
    przewracają się wszystkie kostki bezpośrednio ją poprzedzające.

    Jeszcze jeden drobny detal: żeby w ogóle móc pchnąć kostki początkowe
    (w liczbie mnogiej, bo rzecz jasna może być więcej niż jedna), musimy
    najpierw ustalić, które kostki są tymi początkowymi! Na szczęście nie
    jest to trudne - są to oczywiście te, których nie poprzedzają inne
    kostki.

    I tutaj następuje pewien trik logiczno-językowo-wyobraźniowy: możemy
    o kostkach początkowych myśleć, że przewracają się, gdy przewrócą się
    wszystkie kostki je poprzedzające, których oczywiście nie ma, a nasz
    palec wyobrażać sobie po prostu jako fizyczną realizację tej pustej
    prawdy.

    W ten oto wesoły sposób udało nam się uzyskać definicję elementu
    dostępnego oraz relacji dobrze ufundowanej. *)

Inductive Acc {A : Type} (R : A -> A -> Type) (x : A) : Prop :=
    | Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

(** Kostki domina reprezentuje typ [A], zaś relacja [R] to sposób ułożenia
    kostek, a [x] to pewna konkretna kostka domina. Konstruktor [Acc_intro]
    mówi, że kostka [x] przewraca się, gdy przewracają się wszystkie kostki
    ją poprzedzające.

    To samo nieco mniej bajkowym językiem: element [x] typu [A] jest dostępny
    w relacji [R], jeżeli każdy poprzedzający go element [y] typu [A] również
    jest dostępny. *)

Definition well_founded {A : Type} (R : A -> A -> Type) : Prop :=
  forall x : A, Acc R x.

(** Układ kostek reprezentowany przez [R] przewraca się w całości, jeżeli
    każda kostka domina przewraca się z osobna.

    Mniej poetycko: relacja jest dobrze ufundowana, jeżeli każdy element
    typu [A] jest dostępny.

    Uwaga: typem naszej "relacji" nie jest [A -> A -> Prop], lecz
    [A -> A -> Type], a zatem [R] jest tak naprawdę indeksowaną rodziną
    typów. Różnica między relacją i rodziną typów jest taka, że relacja,
    gdy dostanie argumenty, zwraca zdanie, czyli coś typu [Prop], a rodzina
    typów, gdy dostanie argumenty, zwraca typ, czyli coś typu [Type]. Tak
    więc pojęcie rodziny typów jest ogólniejsze niż pojęcie relacji. Ta
    ogólność przyda się nam za kilka chwil aby nie musieć pisać wszystkiego
    dwa razy. *)

(** **** Ćwiczenie (dostępność i ufundowanie) *)

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
  induction x as [| n']; constructor; inversion 1; subst.
    assumption.
    inversion IHn'. apply H0. assumption.
Qed.
(* end hide *)

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

Definition wut {A : Type} (f : nat -> A) : A * (nat -> A) :=
  (f 0, fun n : nat => f (S n)).

Definition unwut {A : Type} (x : A * (nat -> A)) (n : nat) : A :=
match n with
    | 0 => fst x
    | S n' => snd x n'
end.

Require Import FunctionalExtensionality.

Lemma wut_unwut :
  forall {A : Type} (f : nat -> A),
    unwut (wut f) = f.
Proof.
  intros. extensionality n.
  destruct n as [| n']; cbn; reflexivity.
Qed.

Lemma unwut_wut :
  forall {A : Type} (x : A * (nat -> A)),
    wut (unwut x) = x.
Proof.
  intros. destruct x as [a f]. reflexivity.
Qed.

Lemma wut_ind :
  forall P : nat * (nat -> nat) -> Prop,
    (forall f : nat -> nat, P (0, f)) ->
    (forall (n : nat) (f : nat -> nat), P (n, f) -> P (S n, f)) ->
      forall x : nat * (nat -> nat), P x.
Proof.
  destruct x as [n f].
  induction n as [| n'].
    apply H.
    apply H0. assumption.
Qed.

Definition Pwut
  {A : Type} (P : A * (nat -> A) -> Prop)
  (f : nat -> A) : Prop :=
    P (wut f).

Definition Punwut
  {A : Type} (P : (nat -> A) -> Prop)
  (x : A * (nat -> A)) : Prop := P (unwut x).

Lemma fun_ind :
  forall (A : Type) (P : (nat -> A) -> Prop),
    (forall x : A * (nat -> A), Punwut P x) ->
      forall f : nat -> A, P f.
Proof.
  intros. rewrite <- wut_unwut. apply H.
Qed.

Require Import Omega.

(* TODO: uogólnić na dowolny typ [A] i relację dobrze ufundowaną [R]. *)
Theorem wf_lt' :
  well_founded lt'.
Proof.
  unfold well_founded.
  apply fun_ind. destruct x as [n f]. (* revert f.*)
  unfold Punwut, unwut.
  constructor. unfold lt'. cbn. intro g. revert g.
  induction n as [| n']; intros.
    specialize (H 0). cbn in H. inversion H.
    constructor. intros h H'. apply IHn'.
      destruct n; cbn.
        specialize (H 0). specialize (H' 0). cbn in H. omega.
        specialize (H (S n)). specialize (H' (S n)). cbn in H. omega.
Qed.

Lemma wf_lt'' :
  well_founded lt'.
Proof.
  unfold well_founded.
  intro f.
  pose (n := f 0); assert (n = f 0) by reflexivity; clearbody n.
  revert f H.
(*  induction (lt_wf n).*)
  induction n as [| n']; intros.
    admit.
Admitted.

(** Sprawdź, czy dobrze ufundowana jest poniższa relacja porządku: *)

(* end hide *)

(** Wiemy już, co to znaczy, że kostka domina jest dostępna (każda kostka
    ją poprzedzająca jest dostępna, co formalnie wyraża predykat [Acc])
    oraz że poprawny układ kostek to taki, w którym każda kostka jest
    dostępna (co formalnie wyraża predykat [well_founded]). Możemy teraz
    przejść do tego, do czego dążyliśmy od samego początku: udowodnić, że
    jeżeli poprawnie ustawimy kostki, to wszystkie się przewrócą. *)

Theorem well_founded_rect :
  forall
    (A : Type) (R : A -> A -> Type)
    (wf : well_founded R) (P : A -> Type),
      (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
        forall x : A, P x.
Proof.
  intros A R wf P IH x.
  Check Acc_rect.
  apply Acc_rect with R.
    intros y H1 H2. apply IH. assumption.
    apply wf.
Defined.

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

Require Import Arith.

Definition div : nat -> nat -> nat.
Proof.
  intros n k. revert n.
  apply (well_founded_rect nat lt wf_lt (fun _ => nat)).
  intros n IH.
  case_eq (leb (S n) (S k)); intro.
    exact 0.
    refine (S (IH (n - S k) _)).
      clear IH. revert k H. induction n as [| n']; cbn; intros.
        inversion H.
        destruct k as [| k'].
          rewrite Nat.sub_0_r. apply le_n.
          unfold lt. apply le_trans with n'.
            apply IHn'. cbn. assumption.
            apply le_S, le_n.

(* apply Nat.sub_lt.
      apply leb_complete_conv, lt_S_n in H. exact H.
      apply le_n_S, le_0_n. Show Proof.
*)
 (*
      unfold lt. clear IH. revert k n0.
      induction n as [| n']; cbn; intros.
        contradiction n0. apply le_n_S, le_0_n.
        apply le_n_S. apply IHn'.*)
Defined.

Print div.

Compute div 2 1.

(** * Indukcja funkcyjna *)