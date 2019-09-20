(** * D2: Rekursja i indukcja *)

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

(** * Rekursja strukturalna *)

(** Wiemy już, że rekursja ogólna prowadzi do sprzeczności, a jedyną legalną
    formą rekursji jest rekursja strukturalna. Funkcje rekurencyjne, które
    dotychczas pisaliśmy, były strukturalnie rekurencyjne, więc potrafisz
    już całkiem sprawnie posługiwać się tym rodzajem rekursji. Pozostaje
    nam zatem jedynie zbadać techniczne detale dotyczące sposobu realizacji
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
    zdefiniować prawie żadnej ciekawej funkcji. Jak zobaczymy w kolejnych
    podrozdziałach, wcale tak nie jest. Dzięki pewnej sztuczce za pomocą
    rekursji strukturalnej można wyrazić rekursję dobrze ufundowaną, która
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

(** * Rekursja po paliwie *)

(** Rekursja dobrze ufundowana to sirius byznys, więc zanim się nią zajmiemy
    wypadałoby nauczyć się robić robotę na odwal, byle działało. Jakkolwiek
    nie brzmi to zbyt profesjonalnie, dobrze jest mieć tego typu narzędzie
    w zanadrzu, choćby w celu szybkiego prototypowania. Czasem zdarza się
    też, że tego typu luźne podejście do problemu jest jedynym możliwym, bo
    nikt nie wie, jak to zrobić porządnie.

    Narzędziem, o którym mowa, jest coś, co ja nazywam "rekursją po paliwie".
    Pozwala ona zasymulować definicję dowolnej funkcji o typie
    [A1 -> ... -> An -> B] (w tym nawet częściowej czy nieterminującej, co
    już samo w sobie jest ciekawe) za pomocą funkcji o typie
    [nat -> A1 -> ... -> An -> option B].

    Trik jest dość banalny: argument typu [nat] jest argumentem głównym,
    po którym robimy rekursję. Jest on naszym "paliwem", które spalamy
    przy każdym wywołaniu rekurencyjnym. Jeżeli paliwo się nam skończy,
    zwracamy [None]. Jeżeli jeszcze starcza paliwa, możemy zdefiniować
    funkcję tak jak zamierzaliśmy, ale mamy też obowiązki biurokratyczne
    związane ze sprawdzaniem, czy wyniki wywołań rekurencyjnych to [None]
    czy [Some].

    Coby za dużo nie godoć, przykład. *)

Require Import List.
Import ListNotations.

Require Import Nat.

(** Będą nam potrzebne notacje dla list oraz funkcja [even], która sprawdza,
    czy liczba naturalna jest parzysta. Będziemy chcieli zdefiniować funkcję
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
    argumentu, czy może jest jakiś, dla którego się ona zapętla?

    O ile funkcja jest prosta, o tyle odpowiedź jest bardzo skomplikowana i
    dotychczas nikt nie potrafił jej udzielić. Sprawdzono ręcznie (czyli za
    pomocą komputerów) bardzo dużo liczb i funkcja ta zawsze kończyła pracę,
    ale nikt nie umie udowodnić, że dzieje się tak dla wszystkich liczb. *)

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

(** Definicja funkcji [collatz] za pomocą rekursji po paliwie wygląda dość
    groźnie, ale tak naprawdę jest całkiem banalna.

    Ponieważ oryginalna funkcja była typu [nat -> list nat], to ta nowa musi
    być typu [nat -> nat -> option (list nat)]. Tym razem zamiast dopasowywać
    [n] musimy dopasować paliwo, czyli [fuel]. Dla [0] zwracamy [None], a gdy
    zostało jeszcze trochę paliwa, przechodzimy do właściwej części definicji.
    W przypadkach bazowych zwracamy [[n]], ale  musimy zawinąć je w [Some]. W
    pozostałych przypadkach sprawdzamy, czy [n] jest parzyste, a następnie
    doklejamy odpowiedni ogon, ale musimy dopasować wywołania rekurencyjne
    żeby sprawdzić, czy zwracają one [None] czy [Some]. *)

Compute collatz 10 5.
(* ===> = Some [[5; 16; 8; 4; 2; 1]]
        : option (list nat) *)

Compute collatz 2 5.
(* ===> = None
        : option (list nat) *)

(** Zaimplementowana za pomocą rekursji po paliwie funkcja oblicza się bez
    problemu, oczywiście o ile wystarczy jej paliwa. W powyższych przykładach
    [10] jednostek paliwa wystarcza, by obliczyć wynik dla [5], ale [2]
    jednostki paliwa to za mało. Jak więc widać, ilość potrzebnego paliwa
    zależy od konkretnej wartości na wejściu.

    Interpretacja tego, czym tak naprawdę jest paliwo, nie jest zbyt
    trudna. Jest to maksymalna głębokość rekursji, na jaką może pozwolić
    sobie funkcja. Czym jest głębokość rekursji? Możemy wyobrazić sobie
    drzewo, którego korzeniem jest obecne wywołanie, a poddrzewami są
    drzewa dla wywołań rekurencyjnych. Głębokość rekursji jest po prostu
    głębokością (czyli wysokością) takiego drzewa.

    W przypadku funkcji [collatz] głębokość rekursji jest równa długości
    zwróconej listy (gdy funkcja zwraca [Some]) lub większa niż ilość
    paliwa (gdy funkcja zwraca [None]).

    Powyższe rozważania prowadzą nas do techniki, która pozwala z funkcji
    zrobionej rekursją po paliwie zrobić normalną, pełnoprawną funkcję.
    Wystarczy znaleźć "funkcję tankującą"
    [fill_tank : A1 -> ... -> An -> nat], która oblicza, ile paliwa
    potrzeba dla danych argumentów wejściowych. Funkcja ta powinna mieć
    tę własność, że gdy nalejemy tyle paliwa, ile ona każe (lub więcej),
    zawsze w wyniku dostaniemy [Some].

    Trudnością, z którą nikt dotychczas w przypadku funkcji [collatz] nie
    potrafił się uporać, jest właśnie znalezienie funkcji tankującej. Jak
    więc widać, rekursja po paliwie nie zawsze jest fuszerką czy środkiem
    prototypowania, lecz czasem bywa faktycznie przydatna do reprezentowania
    funkcji, których inaczej zaimplementować się nie da. *)

(** **** Ćwiczenie *)

(** Zdefiniuj za pomocą rekursji po paliwie funkcję [divFuel], która jest
    implementacją dzielenia (takiego zwykłego, a nie sprytnego jak ostatnio,
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

(** Sporą zaletą rekursji po paliwie jest to, że definicje zrobionych za
    jej pomocą funkcji są jasne i czytelne (przynajmniej w porównaniu do
    rekursji dobrze ufundowanej, o czym już niedługo się przekonamy). To
    z kolei pozwala nam w dość łatwy sposób dowodzić interesujących nas
    właściwości tych funkcji.

    Udowodnij kilka oczywistych właściwości dzielenia:
    - [divFuel ? n 1 = Some n], tzn. [n/1 = n]. Ile potrzeba paliwa?
    - [divFuel ? n n = Some 1], tzn. [n/n = 1]. Ile potrzeba paliwa?
    - przy dzieleniu przez [0] nigdy nie starcza paliwa. *)

(* begin hide *)

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

(** Udowodnij, że funkcji [collatz] dla wejść o postaci [pow 2 n] (czyli
    potęg dwójki) wystarczy [S n] jednostek paliwa.

    Uwaga (trochę złośliwa): jeśli napotkasz trudności w trakcie dowodzenia
    (a moje uwagi przecież nie biorą się znikąd), to pamiętaj, że mają one
    charakter arytmetyczny, tzn. są związane z użyciem w definicji funkcji
    takich jak [pow] czy [div2], nie są zaś spowodowane jakimiś problemami
    z samą techniką, jaką jest rekursja po paliwie. *)

(* begin hide *)

Lemma pow2_n_SS :
  forall n : nat, exists m : nat, pow 2 (S n) = S (S m).
Proof.
  induction n as [| n']; cbn.
    exists 0. reflexivity.
    destruct IHn' as [m IH]. cbn in IH. rewrite IH. cbn.
      exists (m + (S (S (m + 0)))). reflexivity.
Qed.

(* TODO *) Lemma collatz_pow2 :
  forall n : nat, collatz (S n) (pow 2 n) <> None.
Proof.
  induction n as [| n'].
    inversion 1.
    destruct (pow2_n_SS n') as [m eq]. rewrite eq.
Abort.

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

    Powyższe malownicze opisy przewracających się kostek domina bardziej
    przywodzą na myśl indukcję, niż rekursję, chociaż wiemy już, że jest
    to w sumie to samo. Przyjmują one perspektywę "od przodu" - jeżeli
    przewrócimy początkową kostkę i niczego nie spartaczyliśmy, kolejne
    kostki będą przewracać się już same.

    Co to znaczy, że niczego nie spartaczyliśmy, pytasz? Tutaj przydaje
    się spojrzenie na nasze domino "od tyłu". Żeby kostka domina się
    przewróciła, muszą przewrócić się na nią wszystkie bezpośrednio
    poprzedzające ją kostki, a żeby one się przewróciły, to przewrócić
    muszą się wszystkie poprzedzające je kostki i tak dalej. W związku
    z tym możemy powiedzieć, że kostka jest dostępna, jeżeli dostępne
    są wszystkie kostki ją poprzedzające.

    Jeszcze jeden drobny detal: kiedy dostępne są kostki, które nie mają
    żadnych poprzedzających kostek? Odpowiedź: zawsze, a dowodem na to
    jest nasz palec, który je przewraca.

    W ten oto wesoły sposób udało nam się uzyskać definicję elementu
    dostępnego oraz relacji dobrze ufundowanej. *)

Inductive Acc {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
    | Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

(** Kostki domina reprezentuje typ [A], zaś relacja [R] to sposób ułożenia
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
    [A -> A -> Type], a zatem [R] jest tak naprawdę indeksowaną rodziną
    typów, a nie relacją. Różnica między relacją i rodziną typów jest
    taka, że relacja, gdy dostanie argumenty, zwraca zdanie, czyli coś
    typu [Prop], a rodzina typów, gdy dostanie argumenty, zwraca typ,
    czyli coś typu [Type]. Tak więc pojęcie rodziny typów jest ogólniejsze
    niż pojęcie relacji. Ta ogólność przyda się nam za kilka chwil aby nie
    musieć pisać wszystkiego dwa razy. *)

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
  induction x as [| n'].
    constructor. inversion 1.
    constructor. intros a Ha. constructor. intros b Hb.
      apply IHn'. apply Nat.lt_le_trans with a.
        assumption.
        apply le_S_n. assumption.
Defined.

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
  revert n f H.
  apply (@well_founded_induction nat lt lt_wf
    (fun n => forall f, n = f 0 -> Acc lt' f)).
  intros n IH f Heq. constructor. intros g Hlt.
  unfold lt' in Hlt.
  apply IH with (g 0).
    specialize (Hlt 0). omega.
    reflexivity.
Qed.

(* end hide *)

(** Sprawdź, czy dobrze ufundowana jest następująca relacja porządku:
    wszystkie liczby parzyste są mniejsze niż wszystkie liczby nieparzyste,
    zaś dwie liczby o tej samej parzystości porównujemy według zwykłego
    porządku [<]. *)

(** Nasza bajka powoli zbliża się do końca. Czas udowodnić ostateczne
    twierdzenie, do którego dążyliśmy: jeżeli układ kostek [R] jest
    niespartaczony (czyli gdy każda kostka jest dostępna), to każda
    kostka się przewraca. *)

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
    możemy myśleć, że [P x] znaczy "kostka x się przewraca". Mamy jeszcze
    hipotezę, która głosi, że kostka [x] przewraca się, gdy przewraca się
    każda kostka, która poprzedza ją w układzie [R].

    Dowód jest banalny. Zaczynamy od wprowadzenia zmiennych i hipotez do
    kontekstu. Następnie odwijamy definicję [well_founded]. Teraz hipoteza
    [wf] głosi, że każde [x : A] jest dostępne. Skoro tak, to specjalizujemy
    ją dla naszego konkretnego [x], które mamy w kontekście.

    Wiemy już zatem, że [x] jest dostępne. Jest to kluczowy fakt, gdyż
    oznacza to, że wszystkie kostki domina poprzedzające [x] również są
    dostępne. Co więcej, [Acc] jest zdefiniowane induktywnie, więc możemy
    pokazać, że [x] się przewraca, właśnie przez indukcję po dowodzie
    dostępności [x].

    Przypadek jest jeden (co nie znaczy, że nie ma przypadków bazowych -
    są nimi kostki domina, których nic nie poprzedza): musimy pokazać, że
    [x] się przewraca przy założeniu, że wszystkie poprzedzające je kostki
    również się przewracają. To, że [x] się przewraca, wynika z hipotezy
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
    które jest jego specjalizacją dla relacji binarnych (czyli bytów o
    typie [A -> A -> Prop]), możemy nazwać twierdzeniem o indukcji dobrze
    ufundowanej.

    Upewnij się, że dobrze rozumiesz oba twierdzenia, a także pojęcia
    dostępności i dobrego ufundowania, gdyż są one bardzo ważne przy
    rozwiązywaniu poważniejszych problemów.

    Co to są "poważniejsze problemy"? Mam oczywiście na myśli dowodzenie
    twierdzeń i definiowanie funkcji, którego nie da się zrobić za pomocą
    prostej indukcji albo banalnego dopasowania do wzorca. W tego typu
    sytuacjach nieodzowne będzie skorzystanie z indukcji i rekursji
    dobrze ufundowanej, o czym przekonamy się już natychmiast zaraz. *)

Definition div : nat -> nat -> nat.
Proof.
  apply (@well_founded_rect nat lt wf_lt (fun _ => nat -> nat)).
  intros n IH m.
  destruct (le_lt_dec (S m) n).
    2: exact 0.
    refine (1 + IH (n - S m) _ m). abstract omega.
Defined.

(* begin hide *)

(** TODO: wprowadzić kombinator [abstract] za pierwszym razem, gdy użyta
    zostanie taktyka [omega]. *)

(* end hide *)

(** Poważniejszym problemem jest bowiem definicja dzielenia, z którą borykamy
    się od samiuśkiego początku niniejszego rozdziału. Powyższy kawałek kodu
    jest (nieudaną, jak się okaże) próbą uporania się z tym problemem.

    Definiować będziemy w trybie dowodzenia, gdyż przy posługiwaniu się
    rekursją dobrze ufundowaną zazwyczaj tak jest dużo łatwiej. Zaczynamy
    od zaaplikowania reguły rekursji dobrze ufundowanej dla typu [nat] i
    porządku [<] (no i rzecz jasna [wf_lt], czyli dowodu na to, że [lt]
    jest dobrze ufundowany - bez tego ani rusz). Po typach widać, że
    rekursja będzie się odbywać po pierwszym argumencie. Wprowadzamy też
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
    sobie rąk arytmetyką, zostawiamy ten cel taktyce [omega], ale
    zawijamy jej użycie w kombinator [abstract], który zapobiega
    "wylaniu się" rozumowania taktyki [omega] do definicji. *)

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
(* ===> dużo różnych głupot *)

(** Mówiąc wprost, taktyka [abstract omega] zamiast wstawiać do definicji
    całe rozumowanie, tak jak zrobiłaby to taktyka [omega], dowodzi sobie
    na boku odpowiedni lemat arytmetyczny, nazywa go [div_subproof] i
    dowodzi celu za jego pomocą. *)

Compute div 5 2.
(* ===> = 1 : nat *)

(** Jak widać, definicja przechodzi bez problemu, a nasza funkcja elegancko
    się oblicza (pamiętaj, że [div 5 2] to tak naprawdę [5/3], więc wynikiem
    faktycznie powinno być [1]).

    Jednak nie samymi definicjami żyje człowiek - czas trochę podowodzić.
    Spodziewamy się wszakże, że nasze dzielenie spełnia wszystkie
    właściwości, których się po nim spodziewamy, prawda? *)

Lemma div_0_r :
  forall n : nat, div n 0 = n.
Proof.
  apply (well_founded_ind _ _ wf_lt).
  intros. unfold div. cbn. (* O Jezu, a cóż to za wojacy? *)
Abort.

(** Niestety jednak, jak to w życiu, nie ma kolorowo.

    Powyższy lemat głosi, że [n/1 = n]. Ponieważ [div] jest zdefiniowane
    za pomocą rekursji dobrze ufundowanej, to dowodzić będziemy oczywiście
    za pomocą indukcji dobrze ufundowanej. Tak, będziemy dowodzić, hmmm...
    cóż... tylko jak?

    Sytuacja wygląda beznadziejnie. Nie żeby lemat był nieprawdziwy - co to,
    to nie. Po prostu próba odwinięcia definicji i policzenia czegokolwiek
    daje inny wynik, niż byśmy chcieli - część definicji ukryta dotychczas
    w [div_subproof] wylewa się i zaśmieca nam ekran.

    Problem nie pochodzi jednak od taktyki [omega] (ani od [abstract omega]).
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
    pomocą taktyki [unfold] lub obliczać za pomocą [cbn]. *)

Lemma div_eq :
  forall n m : nat,
    div n m = if n <? S m then 0 else S (div (n - S m) m).
Proof.
  apply (well_founded_ind _ _ wf_lt (fun _ => forall m : nat, _)).
  intros. unfold div. cbn. (* O Jezu, a cóż to za hołota? *)
Admitted.

(** Powyższe równanie dokładnie opisuje, jak powinna zachowywać się funkcja
    [div], ale za definicję służyć nie może, gdyż Coq nie byłby w stanie
    rozpoznać, że [n - S m] jest podtermem [n]. Zauważ, że używamy tu [<?]
    (czyli [ltb]) zamiast [le_lt_dec]. Możemy sobie na to pozwolić, gdyż
    użycie [le_lt_dec] w faktycznej definicji wynikało jedynie z tego, że
    potrzebowaliśmy dowodu odpowiedniego faktu arytmetycznego, żeby użyć
    go jako argumentu wywołania rekurencyjnego.

    Niestety próba udowodnienia tego równania rekurencyjnego musi skończyć
    się taką samą porażką, jak próba udowodnienia [div_0_r]. Przyczyna jest
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
    omega.
    rewrite IH; omega.
Qed.

(** Jak widać, dzięki równaniu rekurencyjnemu dowody przebiegają dość gładko.
    W powyższym zaczynamy od indukcji dobrze ufundowanej po [n] (przy użyciu
    relacji [<] i dowodu [wf_lt]), wprowadzamy zmienne do kontekstu, po czym
    przepisujemy równanie rekurencyjne. Po przeprowadzeniu analizy przypadków
    kończymy za pomocą rozumowań arytmetycznych, używając być może hipotezy
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

(** * Indukcja funkcyjna *)

(** Skoro nie dla psa kiełbasa, to musimy znaleźć jakiś sposób na
    udowodnienie równania rekurencyjnego dla [div]. Zamiast jednak głowić
    się nad równaniami rekurencyjnymi albo nad funkcją [div], zastanówmy
    się w pełnej ogólności: jak dowodzić właściwości funkcji rekurencyjnych?

    No przez indukcję, czy to nie oczywiste? Jasne, ale jak dokładnie owa
    indukcja ma wyglądać? Odpowiedź jest prostsza niż można się spodziewać.
    Otóż gdy kupujesz but, ma on pasować do twojej stopy, zaś gdy kupujesz
    gacie, mają one pasować do twojej dupy. Podobnie jest z indukcją: jej
    kształt ma pasować do kształtu rekursji, za pomocą której zdefiniowana
    została funkcja.

    Czym jest "kształt" rekursji (i indukcji)? Jest to raczej poetyckie
    pojęcie, które odnosi się do tego, jak zdefiniowano funkcję - ile
    jest przypadków, podprzypadków, podpodprzypadków etc., w jaki sposób
    są w sobie zagnieżdżone, gdzie są wywołania rekurencyjne, ile ich
    jest i na jakich argumentach etc.

    Dowiedziawszy się, czym jest kształt rekursji i indukcji, powinniśmy
    zacząć szukać sposobu na dopasowanie kształtu indukcji w naszych
    dowodach do kształtu rekursji funkcji. Dotychczas indukcję zawsze
    robiliśmy po argumencie głównym, zaś z potencjalnymi niedopasowaniami
    kształtów radziliśmy sobie robiąc ad hoc analizy przypadków, które
    uznaliśmy za stosowne.

    I tutaj przyda nam się nieco konceptualnej spostrzegawczości. Zauważyć
    nam bowiem trzeba, że robiąc indukcję po argumencie głównym, kształt
    indukcji odpowiada kształtowi typu argumentu głównego. Skoro zaś mamy
    dopasować go do kształtu rekursji funkcji, to nasuwa nam się oczywiste
    pytanie: czy da się zdefiniować typ, który ma taki sam kształt, jak
    definicja danej funkcji?

    Odpowiedź brzmi: nie, ale da się zdefiniować rodzinę typów
    (a konkretniej pisząc, rodzinę zdań, czyli relację) o takiej właściwości.
    Owa relacja zwie się wykresem funkcji. Jaki ma to związek z bazgrołami
    znanymi ci ze szkoły (zakładam, że wiesz, że wykresem funkcji liniowej
    jest prosta, wykresem funkcji kwadratowej jest parabola, a wykresy sinusa
    i cosinusa to takie wesołe szlaczki)?

    To, co w szkole nazywa się wykresem funkcji, jest jedynie graficznym
    przedstawieniem prawdziwego wykresu, czyli relacji. Samo słowo "wykres",
    wywodzące się w oczywisty sposób od kreślenia, sugeruje, że myślenie o
    wykresie jak o obrazku było pierwsze, a koncepcja wykresu jako relacji
    jest późniejsza.

    W ramach ciekawostki być może warto napisać, że w dawnych czasach
    matematycy silnie utożsamiali funkcję z jej wykresem (w sensie
    obrazka) i przez to byty, których wykresu nie dało się narysować,
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
      wykresem jakiejś funkcji.
    - Jeżeli typy [A] i [B] da się jakoś sensownie narysować, to możemy
      narysować obrazek przedstawiający wykres funkcji.*)

Definition is_graph
  {A B : Type} (f : A -> B) (R : A -> B -> Prop) : Prop :=
    forall (a : A) (b : B), R a b <-> f a = b.

(** Żeby było nam raźniej, tak wygląda formalna definicja stwierdzenia,
    że relacja [R] jest wykresem funkcji [f]. Uwaga: jeżeli funkcja
    bierze więcej niż jeden argument (tzn. ma typ [A1 -> ... -> An -> B]),
    to wtedy do powyższej definicji musimy wrzucić jej zmodyfikowaną
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

(** Skoro już wiemy czym są wykresy funkcji, czas nauczyć się definiować
    induktywne wykresy o kształtach odpowiednich dla naszych niecnych
    celów. *)

Check div_eq.
(* ===> div_eq
        : forall n m : nat,
            div n m = if n <? S m then 0 else S (div (n - S m) m) *)

(** Zwróćmy tylko uwagę na fakt, że mówiąc o kształcie rekursji (lub po
    prostu o kształcie definicji) [div] nie mamy na myśli faktycznej
    definicji, która używa rekursji dobrze ufundowanej i jak już wiemy,
    jest dość problematyczna, lecz "docelowej" definicji, którą wyraża
    między innymi równanie rekurencyjne. *)

Inductive divG : nat -> nat -> nat -> Prop :=
    | divG_lt : forall {n m : nat}, n < S m -> divG n m 0
    | divG_ge :
        forall n m r : nat, n >= S m ->
          divG (n - S m) m r -> divG n m (S r).

(** [div] jest funkcją typu [nat -> nat -> nat], więc jej wykres to relacja
    typu [nat -> nat -> nat -> Prop]. Dwa pierwsze argumenty relacji
    reprezentują wejście, zaś ostatni argument reprezentuje wyjście, tzn.
    chcemy, żeby [divG n m r] było równoważne [div n m = r].

    Z równania rekurencyjnego widać, że mamy dwa przypadki, czyli konstruktory
    też będą dwa. Jeden odpowiada przypadkowi, gdy [n < S m], tzn. dzielna jest
    mniejsza niż dzielnik (pamiętaj, że [div n m] oznacza [n/(m + 1)], żeby
    uniknąć problemów z dzieleniem przez zero). Konkluzją jest wtedy
    [divG n m 0], tzn. argumentami są [n] i [m], zaś wynikiem jest [0].

    Drugi przypadek to przyadek rekurencyjny. Jeżeli [n >= S m], tzn. dzielna
    jest większa lub równa od dzielnika, to konkluzją jest [divG n m (S r)],
    tzn. argumentami są [n] i [m], zaś wynikiem dzielenia jest [S r]. Czym
    jest [r]? Jest ono skwantyfikowane w tym konstruktorze i pojawia się w
    przesłance [divG (n - S m) m r], która mówi, że wynikiem dzielenia
    [n - S m] przez [m] jest [r]. Przesłanka ta jest wykresowym odpowiednikiem
    wywołania rekurencyjnego. *)

(** **** Ćwiczenie *)

(** Mimo, że wszystkie wykresy danej funkcji są równoważne, to zdefiniować
    można je na wiele różnych sposobów. W zależności od sposobu definicja
    może być użyteczna lub nie, np. przy definicjach induktywnych dostajemy
    za darmo regułę indukcji.

    Podaj inną definicję wykresu funkcji [div], która nie używa typów
    induktywnych (ani nie odwołuje się do samej funkcji [div] - to byłoby
    za łatwe). Użyj kwantyfikatora egzystencjalnego, mnożenia i relacji
    równości (i niczego więcej).

    Na razie nie musisz dowodzić, że wykres faktycznie jest wykresem [div] -
    póki co jest to za trudne (co oczywiście nie znaczy, że wolno ci się
    mylić). Wróćimy do tego dowodu później. *)

(* begin hide *)
Definition divG' (n m r : nat) : Prop :=
  exists q : nat, n = r * S m + q.
(* end hide *)

(** Mamy wykres. Fajnie, ale co możemy z nim zrobić? Jeszcze ważniejsze
    pytanie brzmi zaś: co powinniśmy z nim zrobić? Pierwsza czynność po
    zdefiniowaniu wykresu, którą powinniśmy wykonać, to sprawdzenie, czy
    ów wykres jest relacją funkcyjną, czyli taką, której ostatni argument
    (czyli wynik) jest zdeterminowany przez pozostałe (czyli przez argumenty
    funkcji). Jeżeli tak - dobrze. Jeżeli nie - definicja jest błędna. *)

Lemma divG_functional :
  forall n m r1 r2 : nat,
    divG n m r1 -> divG n m r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; inversion 1; subst.
    reflexivity.
    1-2: omega.
    f_equal. apply IHdivG. assumption.
Qed.

(** Dowód nie jest zbyt trudny. Robimy indukcję po hipotezie [divG n m r1],
    ale musimy pamiętać, żeby wcześniej zgeneralizować [r2], gdyż w przeciwnym
    przypadku nasza hipoteza indukcyjna będzie za mało ogólna. *)

Lemma divG_correct :
  forall n m : nat,
    divG n m (div n m).
Proof.
  apply (well_founded_ind _ _ wf_lt (fun _ => forall m : nat, _)).
  intros n IH m.
  rewrite div_eq. destruct (Nat.ltb_spec0 n (S m)).
    constructor. assumption.
    constructor.
      omega.
      apply IH. omega.
Qed.

Lemma divG_complete :
  forall n m r : nat,
    divG n m r -> div n m = r.
Proof.
  intros. apply divG_functional with n m.
    apply divG_correct.
    assumption.
Qed.

Lemma div_ind :
  forall
    (P : nat -> nat -> nat -> Prop)
    (Hlt : forall n m : nat, n < S m -> P n m 0)
    (Hge : forall n m : nat, n >= S m ->
             P (n - S m) m (div (n - S m) m) -> P n m (S (div (n - S m) m))),
      forall n m : nat, P n m (div n m).
Proof.
  intros P Hlt Hge n m.
  refine (divG_ind P Hlt _ n m _ _).
    intros. apply divG_complete in H0. subst. apply Hge; assumption.
    apply divG_correct.
Qed.

Lemma div_le :
  forall n m : nat,
    div n m <= n.
Proof.
  refine (div_ind (fun n m r => r <= n) _ _); intros.
    apply le_0_n.
    omega.
Qed.

(** * Metoda wykresowo-dziedzinowa *)

(** https://members.loria.fr/DLarchey/files/papers/TYPES_2018_paper_19.pdf

    A robi się to tak:
    - Zdefiniuj wykres funkcji.
    - Zdefiniuj predykat dziedziny używając wykresu.
    - Udowodnij użyteczne rzeczy, np. funkcyjność wykresu.
    - Zdefiniuj funkcję przez rekursję po predykacie dziedziny wraz z jej
      specyfikacją.
    - Wyjmij funkcję i specyfikację za pomocą projekcji. *)

Inductive divD (n m : nat) : Type :=
    | divD_lt : n < S m -> divD n m
    | divD_ge :
        n >= S m -> divD (n - S m) m -> divD n m.

Fixpoint div'_aux {n m : nat} (H : divD n m) : nat :=
match H with
    | divD_lt _ _ _ => 0
    | divD_ge _ _ _ H' => S (div'_aux H')
end.

Lemma divD_all :
  forall n m : nat, divD n m.
Proof.
  apply (well_founded_rect nat lt wf_lt (fun _ => forall m : nat, _)).
  intros n IH m.
  destruct (le_lt_dec (S m) n).
    apply divD_ge.
      assumption.
      apply IH. apply Nat.sub_lt.
        assumption.
        apply le_n_S, le_0_n.
    apply divD_lt. assumption.
Defined.

Definition div' (n m : nat) : nat :=
  div'_aux (divD_all n m).

Lemma divG_div'_aux :
  forall (n m : nat) (d : divD n m),
    divG n m (div'_aux d).
Proof.
  induction d; cbn; constructor; assumption.
Qed.

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
      f_equal. apply divG_functional with (n - S m) m; apply divG_div'_aux.
      assumption.
Qed.

Lemma div'_good :
  forall n m r : nat,
    div' n m = r <-> divG n m r.
Proof.
  split; intro.
    subst. apply divG_div'_aux.
    apply divG_functional with n m.
      apply divG_div'_aux.
      assumption.
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
  refine (divG_ind _ _ _ n m (div' n m) _).
    assumption.
    intros. rewrite <- div'_good in H0. subst. apply Hge; assumption.
    rewrite <- div'_good. reflexivity.
Qed.

Inductive graph : nat -> nat -> Prop :=
    | graph_gt100 :
        forall n : nat, 100 < n -> graph n (n - 10)
    | graph_le100 :
        forall n r1 r2 : nat, n <= 100 ->
          graph (n + 11) r1 -> graph r1 r2 -> graph n r2.

Inductive dom : nat -> Type :=
    | dom_gt100 :
        forall n : nat, 100 < n -> dom n
    | dom_le100 :
        forall n r : nat, n <= 100 ->
          graph (n + 11) r -> dom (n + 11) -> dom r -> dom n.

Lemma graph_functional :
  forall n r1 r2 : nat,
    graph n r1 -> graph n r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; intros.
    inversion H0; subst.
      reflexivity.
      omega.
    inversion H2; subst.
      omega.
      assert (r1 = r3) by apply (IHgraph1 _ H4); subst.
        apply (IHgraph2 _ H5).
Qed.

Fixpoint fD' (n : nat) (d : dom n) : {r : nat | graph n r}.
Proof.
  destruct d.
    exists (n - 10). constructor. assumption.
    destruct (fD' _ d1) as [r1 g1].
      destruct (fD' _ d2) as [r2 g2]. exists r2. eapply graph_le100.
        assumption.
        exact g1.
        assert (r1 = r) by (eapply graph_functional; eauto).
          rewrite H. assumption.
Defined.

Definition fD (n : nat) (d : dom n) : nat :=
match fD' n d with
    | exist _ r _ => r
end.

Lemma fD_correct :
  forall (n : nat) (d : dom n), graph n (fD n d).
Proof.
  intros. unfold fD. destruct (fD' n d). assumption.
Qed.

Lemma fD_complete :
  forall (n r : nat) (d : dom n),
    graph n r -> fD n d = r.
Proof.
  intros. unfold fD. destruct (fD' n d).
  eapply graph_functional; eauto.
Qed.

Lemma fD_spec :
  forall (n r : nat) (d : dom n),
    fD n d = r <-> graph n r.
Proof.
  split; intro.
    rewrite <- H. apply fD_correct.
    apply fD_complete. assumption.
Qed.

Lemma dom_total :
  forall n : nat, dom n.
Proof.
  do 101 try (destruct n).
Admitted.

Definition f (n : nat) : nat := fD n (dom_total n).

Lemma f_correct :
  forall n : nat, graph n (f n).
Proof.
  intros. apply fD_correct.
Qed.

Lemma f_complete :
  forall n r : nat,
    graph n r -> f n = r.
Proof.
  intros. apply fD_complete. assumption.
Qed.

Lemma f_spec :
  forall n r : nat,
    f n = r <-> graph n r.
Proof.
  intros. apply fD_spec.
Qed.

Lemma f_eq :
  forall n : nat,
    f n =
    if leb n 100 then f (f (n + 11)) else n - 10.
Proof.
  intros. unfold f. rewrite fD_spec.
  destruct (Nat.leb_spec0 n 100) as [H | H].
    eapply graph_le100.
      assumption.
      1-2: apply fD_correct.
    constructor. omega.
Qed.

Lemma fD_91 :
  forall (n : nat) (d : dom n),
    n <= 100 -> fD n d = 91.
Proof.
  intros. rewrite fD_spec. revert H.
  induction d; intro.
    omega.
    clear l. inversion d1; subst.
      inversion d2; subst.
        clear IHd2. inversion g; subst.
          eapply graph_le100; eauto. assert (n = 100) by omega.
            subst. cbn. constructor. omega.
          omega.
        eapply graph_le100; eauto.
      specialize (IHd1 H0). assert (r = 91).
        eapply graph_functional; eauto.
        subst. eapply graph_le100; eauto. apply IHd2. omega.
Qed.

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
  intros. unfold f, fD. destruct (fD' n _) as (r & H).
  induction H.
    apply H_gt100. assumption.
    rewrite <- f_spec in *. subst. apply H_le100; assumption.
Defined.

Lemma f_91 :
  forall (n : nat),
    n <= 100 -> f n = 91.
Proof.
  apply (f_ind (fun n r => n <= 100 -> r = 91)).
    intros. omega.
    intros. destruct (Nat.leb_spec0 (n + 11) 100).
      apply H1. rewrite H0.
        omega.
        assumption.
      destruct (Nat.leb_spec0 (f (n + 11)) 100).
        apply H1. assumption.
        rewrite f_eq in n1. destruct (Nat.leb_spec0 (n + 11) 100).
          omega.
          assert (n = 100) by omega. subst. cbn. rewrite 2!f_eq.
            cbn. reflexivity.
Qed.

(** * Wszystko razem, tak do kupy *)

(** Tu jakieś podsumowanie całego zwierzyńca. *)

(** * Uszy do góry *)

(** Tu opis komendy [Function] i pluginu [Equations]. *)