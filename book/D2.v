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
    wszystkie liczby parzyste są mniejsze niż wszystkie liczby nieparzyste,
    zaś dwie liczby o tej samej parzystości porównujemy według zwykłego
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

Require Import Omega.

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
  destruct b as [m | m |], c as [k | k |]; cbn; try omega; auto.
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

Require Import Omega.

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
(* ===> dużo różnych głupot, szkoda pisać *)

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

(** Niech [B : Type] i niech [R : B -> B -> Prop] będzie relacją dobrze
    ufundowaną. Zdefiniuj po współrzędnych relację porządku na funkcjach
    o typie [A -> B] i rozstrzygnij, czy relacja ta jest dobrze ufundowana.

    Uwaga: w zależności od okoliczności to zadanie może być trudne lub
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
        forall n m r : nat,
          n >= S m -> divG (n - S m) m r -> divG n m (S r).

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
    1-2: omega.
    f_equal. apply IHdivG. assumption.
Qed.

(** Pierwsza czynność po zdefiniowaniu wykresu, którą powinniśmy wykonać,
    to sprawdzenie, czy ów wykres jest relacją deterministyczną. Relacja
    deterministyczna to taka, której ostatni argument jest zdeterminowany
    przez poprzednie.

    Jeżeli wykres jest deterministyczny to dobrze, a jeżeli nie, to definicja
    na pewno jest błędna, bo wykres ma opisywać funkcję, a żadna funkcja nie
    może dla tych samych argumentów dawać dwóch różnych wyników. Relacjom
    deterministycznym (i nie tylko) przyjrzymy się dokładniej w rozdziale o
    relacjach.

    Dowód nie jest zbyt trudny. Robimy indukcję po dowodzie hipotezy
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
      omega.
      apply IH. omega.
Qed.

(** Kolejna rzecz do udowodnienia to twierdzenie o poprawności, które mówi,
    że [divG] faktycznie jest wykresem [div]. Zauważ, że moglibyśmy równie
    dobrze sformułować je za pomocą [is_graph], ale tak jak wyżej będzie
    praktyczniej.

    Dowód zaczynamy od indukcji dobrze ufundowanej, po czym wprowadzamy
    zmienne do kontekstu i... aj waj, cóż to takiego? Używamy równania
    rekurencyjnego do rozpisania [div], po czym kończymy przez rozważenie
    przypadków.

    Ten dowód pokazuje, że nie udało nam się osiągnąć celu, który sobie
    postawiliśmy, czyli udowodnienia [div_eq] za pomocą specjalnej reguły
    indukcji. Niestety, bez równania rekurencyjnego nie da się udowodnić
    twierdzenia o poprawności. Nie powinniśmy jednak za bardzo się tym
    przejmować - uszy do góry. Póki co dokończmy poszukiwań ostatecznej
    reguły indukcji, a tym nieszczęsnym równaniem rekurencyjnym zajmiemy
    się później. *)

Lemma divG_complete :
  forall n m r : nat,
    divG n m r -> r = div n m.
Proof.
  intros. apply divG_det with n m.
    assumption.
    apply divG_correct.
Qed.

(** Kolejną, ostatnią już rzeczą, którą powinniśmy zrobić z wykresem, jest
    udowodnienie twierdzenia o pełności, które głosi, że jeżeli argumentom
    [n] i [m] odpowiada na wykresie wynik [r], to [r] jest równe [div n m].
    Dowód jest banalny i wynika wprost z twierdzeń o determinizmie i
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
    pozbyć się niepotrzebnej przesłanki [divG n m r] (po podstawieniu za
    [r] ma ona postać [divG n m (div n m)]), gdyż nie jest potrzebna -
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
    nam ona dowodzić zdań, które zależą od [n m : nat] i wyniku dzielenia,
    czyli [div n m].

    Są dwa przypadki, jak w docelowej definicji [div]. Gdy [n < S m], czyli
    dzielna jest mniejsza od dzielnika, wystarczy udowodnić [P n m 0], bo
    wtedy [div n m] wynosi [0]. W drugim przypadku, czyli gdy [n >= S m],
    wystarczy udowodnić [P n m (S (div (n - S m) m))] (bo taki jest wynik
    [div n m] dla [n >= S m]) przy założeniu, że [P] zachodzi dla [n - S m],
    [m] oraz [div (n - S m) m], bo takie są argumenty oraz wynik wywołania
    rekurencyjnego.

    Dowód jest prosty. Wprowadzamy zmienne do kontekstu, a następnie za pomocą
    zwykłego [apply] używamy reguły indukcji [divG_ind] - jako rzekło się
    powyżej, reguła [div_ind] nie jest niczym innym, niż lekką przeróbką
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
    omega.
Qed.

(** **** Ćwiczenie *)

(** Udowodnij twierdzenie [div_le] za pomocą indukcji dobrze ufundowanej
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
    specialize (IH (n - S m) ltac:(omega) m). omega.
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
    destruct H0 as [q IH]. exists q. cbn. omega.
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
    destruct (IH (n - S m) ltac:(omega) m) as [q IHq].
      exists q. cbn. omega.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Napisz funkcję [split] o sygnaturze
    [split (n : nat) {A : Type} (l : list A) : option (list A * list A)],
    która rozdziela listę [l] na blok o długości [n] i resztę listy, lub
    zwraca [None] gdy lista jest za krótka.

    Następnie udowodnij dla tej funkcji regułę indukcji wykresowej i użyj
    jej do udowodnienia kilku lematów.

    Wszystkie te rzeczy przydadzą się nam w jednym z kolejnych zadań. *)

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

(** Póki co nie jest źle - udało nam się wszakże wymyślić jedyną słuszną
    metodę dowodzenia właściwości funkcji rekurencyjnych. Jednak nasza
    implementacja kuleje przez to nieszczęsne równanie rekurencyjne. Jak
    możemy udowodnić je bez używania indukcji wykresowej?

    Żeby znaleźć odpowiedź na to pytanie, znowu przyda się nam trochę
    konceptualnej jasności. Na czym tak naprawdę polega problem? Jak
    pamiętamy, problem wynika z tego, że definiując [div] przez rekursję
    dobrze ufundowaną musieliśmy jednocześnie dowodzić, że wywołania
    rekurencyjne odbywają się na argumencie mniejszym od argumentu obecnego
    wywołania.

    Tak więc problemem jest połączenie w jednej definicji dwóch dość luźno
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
    żeby rozdzielić obliczeniowy i logiczny aspekt danej funkcji, a potem
    poskładać je do kupy?

    Pomyślmy najpierw nad aspektem obliczeniowym. Czy da się zdefiniować
    funkcję bezpośrednio za pomocą jej definicji docelowej, czyli równania
    rekurencyjnego? Żeby to zrobić, musielibyśmy mieć możliwość robienia
    rekursji o dokładnie takim kształcie, jaki ma mieć ta funkcja...

    Eureka! Przecież mamy coś, co pozwala nam na rekursję o dokładnie takim
    kształcie, a mianowicie induktywny wykres! Ale przecież wykres wiąże
    ze sobą argumenty i wynik, a my chcemy dopiero zdefiniować coś, co ów
    wynik obliczy... czyli nie eureka?

    Nie do końca. Możemy zmodyfikować definicję wykresu, wyrzucając z
    niej wszystkie wzmianki o wyniku, uzyskując w ten sposób predykat
    będący induktywną charakteryzacją dziedziny naszej funkcji. Dzięki
    niemu możemy zdefiniować zmodyfikowaną wersję funkcji, w której
    dodatkowym argumentem jest dowód na to, że argumenty należą do
    dziedziny.

    Logiczny aspekt funkcji, czyli dowód terminacji, sprowadza się w
    takiej sytuacji do pokazania, że wszystkie argumenty należą do
    dziedziny (czyli spełniają predykat dziedziny). Żeby zdefiniować
    oryginalną funkcję, wystarczy jedynie poskładać oba aspekty do
    kupy, czyli wstawić dowód terminacji do zmodyfikowanej funkcji.

    Żeby nie utonąć w ogólnościach, zobaczmy, jak nasz wspaniały
    wynalazek radzi sobie z dzieleniem. *)

Inductive divD : nat -> nat -> Type :=
    | divD_lt : forall n m : nat, n < S m -> divD n m
    | divD_ge :
        forall n m : nat,
          n >= S m -> divD (n - S m) m -> divD n m.

(** Tak wygląda predykat dziedziny dla dzielenia. Zauważmy, że tak naprawdę
    to nie jest to predykat, bo bierze dwa argumenty i co więcej nie zwraca
    [Prop], lecz [Type]. Nie będziemy się tym jednak przejmować - dla nas
    [divD] będzie "predykatem dziedziny". Zauważmy też, że nie jest to
    predykat dziedziny dla [div], lecz dla [div'], czyli zupełnie nowej
    funkcji, którą zamierzamy zdefiniować.

    Ok, przejdźmy do konkretów. [div'] ma mieć typ [nat -> nat -> nat],
    a zatem [divD] ma dwa indeksy odpowiadające dwóm argumentom [div'].
    Pierwszy konstruktor głosi, że jeżeli [n < S m], to oba te argumenty
    należą do dziedziny (bo będziemy chcieli w tym przypadku zwrócić [0]).
    Drugi konstruktor głosi, że jeżeli [n >= S m], to para argumentów [n]
    i [m] należy do dziedziny pod warunkiem, że para argumentów [n - S m]
    i [m] należy do dziedziny. Jest tak, gdyż w tym przypadku będziemy
    chcieli zrobić wywołanie rekurencyjne właśnie na [n - S m] oraz [m]. *)

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
    stojąca za metodą induktywnej dziedziny - możemy sprawić, żeby każda (no,
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
      apply IH. abstract omega.
    apply divD_lt. assumption.
Defined.

(** Dowód terminacji jest bliźniaczo podobny do naszej pierwszej definicji
    [div]. Zaczynamy przez rekursję dobrze ufundowaną z porządkiem [lt] (i
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

(** Jak widać, wynik oblicza się bez problemu. Po raz kolejny przypominam,
    że [div' n m] oblicza [n/(m + 1)], nie zaś [n/m]. Przypominam też, że
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

(** Żeby udowodnić regułę indukcji wykresowej, będziemy potrzebowali tego
    samego co poprzednio, czyli twierdzeń o poprawności i pełności funkcji
    [div'] względem wykresu [divG]. Dowody są jednak dużo prostsze niż
    ostatnim razem.

    Najpierw dowodzimy, że funkcja pomocnicza [div'_aux] oblicza taki wynik,
    jakiego spodziewa się wykres [divG]. Dowód jest banalny, bo indukcja po
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
    równanie rekurencyjne, bez którego nie mogliśmy obyć się ostatnim
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
      abstract omega.
    rewrite leb_correct_conv.
      reflexivity.
      abstract omega.
Qed.

(** Pierwszy, trudniejszy sposób, to zgeneralizowanie [divD_all n m]
    do dowolnego [d] oraz indukcja po [d] (to tak, jakbyśmy najpierw
    udowodnili tę regułę dla [div'_aux], a potem wyspecjalizowali do
    [div']).

    Drugi, łatwiejszy sposób, realizuje nasz początkowy pomysł, od którego
    wszystko się zaczęło: dowodzimy równania rekurencyjnego za pomocą reguły
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
    jest inwolucją dla dowolnego [n], tzn. [rot n (rot n l) = l]. Uwaga:
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

(** * Komenda [Function] *)

(** Odkryliśmy uniwersalną metodę definiowania funkcji i dowodzenia ich
    właściwości. Czego chcieć więcej?

    Po pierwsze, metoda definiowania nie jest uniwersalna (jeszcze), o czym
    przekonamy się w kolejnych podrozdziałach. Po drugie, mimo że metoda
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
  intros. unfold id. cbn in teq. apply leb_complete_conv in teq. omega.
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
    udowodnić, że wywołanie rekurencyjne [div''] odbywa się na argumencie
    mniejszym niż [n]. Po zakończeniu dowodu funkcja zostaje zaakceptowana
    przez Coqa.

    To jednak nie koniec. Komenda [Function] nie tylko pozwala bezboleśnie
    zdefiniować [div''], ale też generuje dla nas całą masę różnych rzeczy:
    - [div''_tcc] to lemat, który mówi, że wszystkie wywołania rekurencyjne
      są na argumencie mniejszym od obecnego
    - [div''_terminate] to dowód tego, że funkcja terminuje (czyli że się
      nie zapętla). Jeżeli przyjrzysz się jego typowi, to zobaczysz, że
      jest podobny zupełnie do niczego. Wynika to z faktu, że komenda
      [Function] tak naprawdę nie używa metody induktywnej dziedziny, ale
      pewnej innej metody definiowania funkcji ogólnie rekurencyjnych.
      Nie powinno nas to jednak martwić - ważne, że działa.
    - [div''_ind] to reguła indukcji wykresowej dla [div'']. Jest też jej
      wariant [div''_rect], czyli "rekursja wykresowa", służąca raczej do
      definiowania niż dowodzenia.
    - [R_div''] to induktywnie zdefiniowany wykres funkcji [div'']. Zauważ
      jednak, że nie jest on relacją, a rodziną typów - nie wiem po co i
      nie ma co wnikać w takie detale.
    - [R_div''_correct] to twierdzenie o poprawności wykresu.
    - [R_div''_complete] to twierdzenie o pełności wykresu.
    - [div''_equation] to równanie rekurencyjne *)

(** Jak więc widać, nastąpił cud automatyzacji i wszystko robi się samo.
    To jednak nie koniec udogodnień. Zobaczmy, jak możemy udowodnić jakiś
    fakt o [div'']. *)

Lemma div''_le :
  forall n m : nat, div'' n m <= n.
Proof.
  intros. functional induction (div'' n m).
    apply le_0_n.
    apply leb_complete_conv in e. omega.
Defined.

(** Dowodzenie właściwości funkcji zdefiniowanych za pomocą [Function]
    jest bajecznie proste. Jeżeli wszystkie argumenty funkcji znajdują
    się w kontekście, to możemy użyć taktyki [functional induction
    (nazwa_funkcji argument_1 ... argument_n)], która odpala indukcję
    wykresową dla tej funkcji. Z powodu nazwy tej taktyki indukcja
    wykresowa bywa też nazywana indukcją funkcyjną.

    Wujek Dobra Rada: nigdy nie odwijaj definicji funkcji zdefiniowanych
    za pomocą [Function] ani nie próbuj ręcznie aplikować reguły indukcji
    wykresowej, bo skończy się to jedynie bólem i zgrzytaniem zębów.

    Na koniec wypadałoby jedynie dodać, że wcale nie złapaliśmy pana boga
    za nogi i komenda [Function] nie rozwiązuje wszystkich problemów
    pierwszego świata. W szczególności niektóre funkcje mogą być tak
    upierdliwe, że komenda [Function] odmówi współpracy z nimi. Radzeniu
    sobie z takimi ciężkimi przypadkami poświęcimy kolejne podrozdziały. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [rot] (i wszystkie funkcje pomocnicze) jeszcze raz,
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

Require Import Omega.

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
      cbn. omega.
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

(** https://members.loria.fr/DLarchey/files/papers/TYPES_2018_paper_19.pdf

    A robi się to tak:
    - Zdefiniuj wykres funkcji.
    - Zdefiniuj predykat dziedziny używając wykresu.
    - Udowodnij użyteczne rzeczy, np. funkcyjność wykresu.
    - Zdefiniuj funkcję przez rekursję po predykacie dziedziny wraz z jej
      specyfikacją.
    - Wyjmij funkcję i specyfikację za pomocą projekcji. *)

Inductive f91G : nat -> nat -> Prop :=
    | f91G_gt100 :
        forall n : nat, 100 < n -> f91G n (n - 10)
    | f91G_le100 :
        forall n r1 r2 : nat, n <= 100 ->
          f91G (n + 11) r1 -> f91G r1 r2 -> f91G n r2.

Inductive f91D : nat -> Type :=
    | f91D_gt100 :
        forall n : nat, 100 < n -> f91D n
    | f91D_le100 :
        forall n r : nat, n <= 100 ->
          f91G (n + 11) r -> f91D (n + 11) -> f91D r -> f91D n.

Lemma f91G_det :
  forall n r1 r2 : nat,
    f91G n r1 -> f91G n r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; intros r Hr.
    inversion Hr; subst.
      reflexivity.
      omega.
    inversion Hr; subst.
      omega.
      assert (r1 = r0) by apply (IHf91G1 _ H3); subst.
        apply (IHf91G2 _ H4).
Qed.

Fixpoint f91_aux {n : nat} (d : f91D n) : nat :=
match d with
    | f91D_gt100 _ _ => n - 10
    | f91D_le100 _ _ _ _ _ d2 => f91_aux d2
end.

Lemma f91_aux_correct :
  forall (n : nat) (d : f91D n), f91G n (f91_aux d).
Proof.
  induction d; cbn.
    constructor. assumption.
    econstructor 2.
      assumption.
      exact IHd1.
      assert (r = f91_aux d1).
        apply f91G_det with (n + 11); assumption.
        subst. assumption.
Qed.

Lemma f91_aux_complete :
  forall (n r : nat) (d : f91D n),
    f91G n r -> f91_aux d = r.
Proof.
  intros. apply f91G_det with n.
    apply f91_aux_correct.
    assumption.
Qed.

Lemma f91_aux_91 :
  forall (n : nat) (d : f91D n),
    n <= 100 -> f91_aux d = 91.
Proof.
  intros. apply f91_aux_complete. revert H.
  induction d; intro.
    omega.
    clear l. inversion d1; subst.
      inversion d2; subst.
        clear IHd2. inversion f; subst.
          eapply f91G_le100; eauto. assert (n = 100) by omega.
            subst. cbn. constructor. omega.
          omega.
        eapply f91G_le100; eauto.
      specialize (IHd1 H0). assert (r = 91).
        eapply f91G_det; eauto.
        subst. eapply f91G_le100; eauto. apply IHd2. omega.
Qed.

Lemma f91_aux_ge_100 :
  forall (n : nat) (d : f91D n),
    100 < n -> f91_aux d = n - 10.
Proof.
  destruct d; cbn; omega.
Qed.

Lemma f91D_all :
  forall n : nat, f91D n.
Proof.
  apply (well_founded_ind _ (fun n m => 101 - n < 101 - m)).
    apply wf_inverse_image. apply wf_lt.
    intros n IH. destruct (le_lt_dec n 100).
      pose (d := (IH (n + 11) ltac:(omega))); clearbody d.
        constructor 2 with (f91_aux d).
          assumption.
          apply f91_aux_correct.
          assumption.
          apply IH. inversion d; subst.
            rewrite f91_aux_ge_100.
              omega.
              assumption.
            rewrite f91_aux_91; omega.
      constructor. assumption.
Qed.

Definition f91 (n : nat) : nat := f91_aux (f91D_all n).

Lemma f91_correct :
  forall n : nat, f91G n (f91 n).
Proof.
  intros. apply f91_aux_correct.
Qed.

Lemma f91_complete :
  forall n r : nat,
    f91G n r -> f91 n = r.
Proof.
  intros. apply f91_aux_complete. assumption.
Qed.

Lemma f91_ind :
  forall
    (P : nat -> nat -> Prop)
    (H_gt100 : forall n : nat, 100 < n -> P n (n - 10))
    (H_le100 :
      forall n : nat, n <= 100 ->
        P (n + 11) (f91 (n + 11)) -> P (f91 (n + 11)) (f91 (f91 (n + 11))) ->
          P n (f91 (f91 (n + 11)))),
    forall n : nat, P n (f91 n).
Proof.
  intros. apply f91G_ind.
    assumption.
    intros. apply f91_complete in H0. apply f91_complete in H2.
      subst. apply H_le100; assumption.
    apply f91_correct.
Defined.

Lemma f91_91 :
  forall (n : nat),
    n <= 100 -> f91 n = 91.
Proof.
  intros. apply f91_aux_91. assumption.
Qed.

Lemma f91_eq :
  forall n : nat,
    f91 n = if 100 <? n then n - 10 else f91 (f91 (n + 11)).
Proof.
  intros. apply f91G_det with n.
    apply f91_correct.
    unfold ltb. destruct (Nat.leb_spec0 101 n).
      constructor. assumption.
      econstructor.
        omega.
        apply f91_correct.
        apply f91_correct.
Qed.

(** * Metoda induktywno-rekurencyjnej dziedziny *)

(** * Rekursja wyższego rzędu *)

(** Pozostaje kwestia rekursji wyższego rzędu. Co to? Ano dotychczas nasze
    wywołania rekurencyjne były specyficzne, a konkretniej pisząc, wszystkie
    dotychczasowe wywołania rekurencyjne były zaaplikowane do argumentów.

    Mogłoby się wydawać, że jest to jedyny możliwy sposób robienia wywołań
    rekurencyjnych, jednak nie jest tak. Wywołania rekurencyjne mogą mieć
    również inną, wyższorzędową postać, a mianowicie - możemy przekazać
    funkcję, którą właśnie definiujemy, jako argument do innej funkcji.

    Dlaczego jest to wywołanie rekurencyjne, skoro nie wywołujemy naszej
    funkcji? Ano dlatego, że tamta funkcja, która dostaje naszą jako
    argument, dostaje niejako możliwość robienia wywołań rekurencyjnych.
    W zależności od tego, co robi ta funkcja, wszystko może być ok (np.
    gdy ignoruje ona naszą funkcję i w ogóle jej nie używa) lub śmiertelnie
    niebezpieczne (gdy próbuje zrobić wywołanie rekurencyjne na większym
    argumencie).

    Sztoby za dużo nie godoć, bajszpil: *)

Inductive Tree (A : Type) : Type :=
    | Node : A -> list (Tree A) -> Tree A.

Arguments Node {A} _ _.

(** [Tree] to typ drzew niepustych, które mogą mieć dowolną (ale skończoną)
    ilość poddrzew. Spróbujmy zdefiniować funkcję, która zwraca lustrzane
    odbicie drzewa. *)

Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
match t with
    | Node x ts => Node x (rev (map mirror ts))
end.

(** Nie jest to zbyt trudne. Rekurencyjnie odbijamy wszystkie poddrzewa, a
    następnie odwracamy kolejność poddrzew za pomocą [rev]. Chociaż poszło
    gładko, to mamy tu do czynienia z czymś, czego wcześniej nie widzieliśmy.
    Nie zrobiliśmy żadnego wywołania rekurencyjnego, a mimo to funkcja działa
    ok. Dlaczego?

    Właśnie dlatego, że wywołania rekurencyjne są robione przez funkcję [map].
    A zatem mamy do czynienia z rekursją wyższego rzędu. *)



Definition mab {A B : Type} (f : A -> B) :=
  fix mab (l : list A) : list B :=
  match l with
      | [] => []
      | h :: t => f h :: mab t
  end.


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


(** * Plugin [Equations] *)

(** **** Zadanie 8 *)

(** Zainstaluj plugin Equations:
    https://github.com/mattam82/Coq-Equations

    Przeczytaj tutorial:
    https://raw.githubusercontent.com/mattam82/Coq-Equations/master/doc/equations_intro.v

    Następnie znajdź jakiś swój dowód przez indukcję, który był skomplikowany
    i napisz prostszy dowód za pomocą komendy [Equations] i taktyki [funelim].
*)

(** * Podsumowanie *)

(** Póki co nie jest źle, wszakże udało nam się odkryć indukcję wykresową,
    czyli metodę dowodzenia właściwości funkcji za pomocą specjalnie do
    niej dostosowanej reguły indukcji, wywodzącej się od reguły indukcji
    jej wykresu. *)