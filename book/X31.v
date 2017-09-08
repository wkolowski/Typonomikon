(** * X31: Złożoność obliczeniowa i rekursja ogonowa *)

(** (Uwaga: numeracja jest chwilowa, bo nie wiem jak zrobić kolejność. To jest
    tylko draft. Chyba będę pisał rozdziały chaotycznie.) *)

(** Prerekwizyty:
    - rekursja strukturalna
    - dowodzenie przez indukcję
    - listy
    - teoria relacji *)

Require Import X3.

(** Zapoznaliśmy się już z rekursją strukturalną, dzięki której możemy definiować
    proste funkcje, oraz z techniką dowodzenia przez indukcję, dzięki której
    możemy stwierdzić ponad wszelką wątpliwość, że nasze funkcje robią to, czego
    od nich wymagamy. Skoro tak, to czas zapoznać się z kolejnym istotnym
    elementem układanki, jakim jest złożoność obliczeniowa.

    W tym rozdziale nauczysz się analizować proste algorytmy pod względem czasu
    ich działania. Poznasz też technikę, która pozwala napisać niektóre funkcje
    rekurencyjne w dużo wydajniejszy sposób. *)

(** * Czas działania programu *)

(** Cel naszych rozważań w tym rozdziale jest prosty: chcemy zbadać, jak długo
    będą wykonywać się nasze programy.

    Jest to z pozoru proste zadanie: wystarczy włączyć zegar, odpalić program
    i wyłączyć zegar, gdy program się wykona. Takie podejście ma jednak spore
    wady, gdyż zmierzony w ten sposób czas:
    - Zależy od sprzętu. Im lepszy sprzęt, tym krótszy czas.
    - Jest w pewnym sensie losowy. Za każdym wykonaniem programu czas jego
      działania będzie nieco inny. Wobec tego musielibyśmy puszczać nasz
      program wielokrotnie, co spowolniłoby mierzenie czasu jego wykonania.
      Musielibyśmy też, zamiast "zwykłego" czasu działania, posługiwać się
      średnim czasem działania, co rodzi obawy natury statystycznej.
    - Jest trudny do zmierzenia. Co, jeżeli wykonanie programu jest dłuższe,
      niż przewidywany czas istnienia wszechświata? *)

(** Wobec powyższego mierzenie czasu za pomocą zegarka należy odrzucić. Innym
    z pozoru dobrym pomysłem jest zastępienie pojęcia "czasu" pojęciem "ilości
    taktów procesora". Jednak i ono ma swoje wady:
    - Zależy od sprzętu. Niektóre procesory mogą np. wykonywać wiele operacji
      na raz (wektoryzacja), inne zaś mają po kilka rdzeni i być może zechcą
      wykonać nasz kod współbieżnie na kilku z nich.
    - Zależy od implementacji języka, którym się posługujemy. W Coqu jest
      możliwość ekstrakcji kodu do kilku innych języków (Haskell, Ocaml,
      Scheme), a kod wyekstraktowany do Haskella najpewniej miałby inny
      czas działania, niż kod wyekstraktowany do Ocamla.
    - Również jest trudny do zmierzenia. *)

(** Jak widać, mierzenie czasu za pomocą taktów procesora też nie jest zbyt
    dobrym pomysłem. Prawdę mówiąc, wszelkie podejścia oparte na mierzeniu
    czegokolwiek będą się wiązały z takimi nieprzyjemnościami, jak błędy
    pomiaru, problemy z mierzeniem, czy potencjalna konieczność posługiwania
    się uśrednieniami. *)

(** * Złożoność obliczeniowa *)

(** Zdecydujemy się zatem na podejście bardziej abstrakcyjne: będziemy
    liczyć, ile operacji wykonuje nasz program w zależności od rozmiaru
    danych wejściowych. Niech cię nie zmyli słowo "rozmiar": nie ma ono
    nic wspólnego z mierzeniem.

    Żeby za dużo nie gdakać, rzućmy okiem na przykład. *)

Print head.
(* ===> head = 
        fix head (A : Type) (l : list A) {struct l} : option A :=
        match l with
            | [[]] => None
            | h :: _ => Some h
        end
        : forall A : Type, list A -> option A *)

(** Tak powinna wyglądać definicja funkcji [head], której napisanie było w
    poprzednim rozdziale jednym z twoich zadań.

    Pierwszym krokiem naszej analizy jest ustalenie, czym są dane wejściowe.
    Dane wejściowe to po prostu argumenty funkcji [head], czyli [A : Type]
    oraz [l : list A].

    Drugim krokiem jest ustalanie, które argumenty mają wpływ na czas działania
    funkcji i jaki jest ich rozmiar. Z pewnością wpływu na wynik nie może mieć
    typ [A], gdyż dla każdego typu robi ona to samo — zmienia się tylko typ
    danych, na których operuje. Wobec tego jedynym argumentem, którego rozmiar
    może mieć znaczenie, jest [l : list A].

    Kolejnym krokiem jest ustalenie, jaki jest rozmiar listy [l], ale zanim
    będzie to w ogóle możliwe, musimy zadać sobie bardziej fundamentalne
    pytanie: czym właściwie jest rozmiar? Przez rozmiar rozumieć będziemy
    zawsze pewną liczbę naturalną, która intuicyjnie mówi nam, jak duży i
    skomplikowany jest dany obiekt.

    W przypadku typów induktywnych powinno to być dość jasne. Jako że funkcje
    na obiektach takich typów definiujemy przez rekursję, która stopniowo
    "pożera" swój argument, spodziewamy się, że obliczenie funkcji na "większym"
    obiekcie będzie wymagało wykonania większej ilości wywołań rekurencyjnych,
    co oznacza dłuższy "czas" wykonania ("czas" jest w cudzysłowie, gdyż tak
    naprawdę nie badamy już dosłownie czasu działania programu, a jedynie ilość
    wykonywanych przez niego operacji).

    Czymże może być rozmiar listy? Cóż, potencjalnych miar rozmiaru list jest
    zapewne nieskończenie wiele, ale najsensowniejszym pomysłem, który powinien
    od razu przyjść ci na myśl, jest jej długość (ta sama, którą obliczamy
    za pomocą funkcji [length]).

    W ostatnim kroku pozostaje nam policzyć na palcach, ile operacji wykonuje
    nasza funkcja. Pierwszą operacją jest pattern matching. Druga to zwrócenie
    wyniku. Hmmm, czyżby nasza funkcja wykonywała tylko dwie operacje?

    Przypomnij sobie, że wzorce są dopasowywane w kolejności od góry do dołu.
    Wobec tego jeżeli lista nie jest pusta, to wykonujemy dwa dopasowania, a
    nie jedno. Wobec dla pustej listy wykonujemy dwie operacje, a dla niepustej
    trzy.

    Ale czy aby na pewno? A może zwrócenie wyniku nie jest operacją? A może
    jego koszt jest inny niż koszt wykonania dopasowania? Być może nie podoba
    ci się forma naszego wyniku: "jeżeli pusta to 2, jeżeli nie to 3".

    Powyższe wątpliwości wynikają w znacznej mierze z tego, że wynik naszej
    analizy jest zbyt szczegółowy. Nasze podejście wymaga jeszcze jednego,
    ostatniego już ulepszenia: zamiast analizy dokładnej posłużymy się analizą
    asymptotyczną. *)

(** * Złożoność asymptotyczna *)

(** Za określeniem "złożoność asymptotyczna" kryje się prosta idea: nie
    interesuje nas dokładna ilość operacji, jakie program wykonuje, a tylko
    w jaki sposób zwiększa się ona w zależności od rozmiaru danych. Jeżeli
    przełożymy naszą odpowiedź na język złożoności asymptotycznej, zabrzmi
    ona: funkcja [head] działa w czasie stałym (co nieformalnie będziemy
    oznaczać przez O(1)).

    Co znaczy określenie "czas stały"? Przede wszystkim nie odnosi się ono
    do czasu, lecz do ilości operacji. Przywyknij do tej konwencji — gdy
    chodzi o złożoność, "czas" znaczy "ilość operacji". Odpowiadając na
    pytanie: jeżeli funkcja "działa w czasie stałym" to znaczy, że wykonuje
    ona taką samą ilość operacji niezależnie od rozmiaru danych.

    Uzyskana odpowiedź nie powinna nas dziwić — ustaliliśmy wszakże, że
    funkcja [head] oblicza wynik za pomocą góra dwóch dopasowań do wzorca.
    Nawet jeżeli przekażemy do niej listę o długości milion, to nie dotyka
    ona jej ogona o długości 999999.

    Co dokładnie oznacza stwierdzenie "taką samą ilość operacji"? Mówiąc
    wprost: ile konkretnie? O tym informuje nas nasze nieformalne oznaczenie
    O(1), które niedługo stanie się dla nas jasne. Przedtem jednak należy
    zauważyć, że istnieją trzy podstawowe sposoby analizowania złożoności
    asymptotycznej:
    - optymistyczny, polegający na obliczeniu najkrótszego możliwego czasu
      działania programu
    - średni, który polega na oszacowaniu przeciętnego czasu działania
      algorytmu, czyli czasu działania dla "typowych" danych wejściowych
    - pesymistyczny, polegający na obliczeniu najgorszego możliwego czasu
      działania algorytmu. *)

(** Analizy optymistyczna i pesymistyczna są w miarę łatwe, a średnia — dość
    trudna. Jest tak dlatego, że przy dwóch pierwszych sposobach interesuje
    nas dokładnie jeden przypadek (najbardziej lub najmniej korzystny), a przy
    trzecim — przypdek "średni", a do uporania się z nim musimy przeanalizować
    wszystkie przypadki.

    Analizy średnia i pesymistyczna są w miarę przydatne, a optymistyczna —
    raczej nie. Optymizm należy odrzucić choćby ze względu na prawa Murphy'ego,
    które głoszą, że "jeżeli coś może się nie udać, to na pewno się nie uda".

    Wobec powyższych rozważań skupimy się na analizie pesymistycznej, gdyż ona
    jako jedyna z trzech możliwości jest zarówno użyteczna, jak i w miarę
    łatwa. *)

(** * Duże O *)

(** ** Definicja i intuicja *)

(** Nadszedł wreszcie czas, aby formalnie zdefiniować "notację" duże O.
    Wziąłem słowo "notacja" w cudzysłów, gdyż w ten właśnie sposób byt
    ten jest nazywany w literaturze; w Coqu jednak słowo "notacja" ma
    zupełnie inne znaczenie, nijak niezwiązane z dużym O. Zauważmy też,
    że zbieżność nazwy [O] z identyczną nazwą konstruktora [O : nat] jest
    jedynie smutnym przypadkiem. *)

Definition O (f g : nat -> nat) : Prop :=
  exists c n : nat,
    forall n' : nat, n <= n' -> f n' <= c * g n'.

(** Zdanie [O f g] można odczytać jako "f rośnie nie szybciej niż g" lub
    "f jest asymptotycznie mniejsze od g", gdyż [O] jest pewną formą porządku.
    Jest to jednak porządek specyficzny:
    - Po pierwsze, funkcje [f] i [g] porównujemy porównując wyniki zwracane
      przez nie dla danego argumentu.
    - Po drugie, nie porównujemy ich na wszystkich argumentach, lecz jedynie
      na wszystkich argumentach większych od pewnego [n : nat]. Oznacza to,
      że [f] może być "większe" od [g] na skończonej ilości argumentów od [0]
      do [n], a mimo tego i tak być od [g] asymptotycznie mniejsze. 
    - Po trzecie, nie porównujemy [f n'] bezpośrednio do [g n'], lecz do
      [c * g n']. Można to intuicyjnie rozumieć tak, że nie interesują nas
      konkretne postaci funkcji [f] i [g] lecz jedynie ich komponenty 
      najbardziej znaczące, czyli najbardziej wpływające na wynik. Przykład:
      jeżeli f(n) = 4n^2, a g(n) = 42n^42, to nie interesują nas stałe 4 i 42.
      Najbardziej znaczącym komponentem [f] jest n^2, zaś g — n^42. *)

(** Poszukaj w Internecie wizualizacji tej idei — ja niestety mam bardzo
    ograniczone możliwości osadzania multimediów w niniejszej książce
    (TODO: postaram się coś na to poradzić). *)

(** ** Złożoność formalna i nieformalna *)

(** Ostatecznie nasze nieformalne stwierdzenie, że złożoność funkcji [head]
    to O(1) możemy rozumieć tak: "ilość operacji wykonywanych przez funkcję
    [head] jest stała i nie zależy w żaden sposób od długości listy, która
    jest jej argumentem". Nie musimy przy tym zastanawiać się, ile dokładnie
    operacji wykonuje [head]: może 2, może 3, a może nawet 4, ale na pewno
    mniej niż, powiedzmy, 1000, więc taką wartość możemy przyjąć za [c].


    To nieformalne stwierdzenie moglibyśmy przy użyciu naszej formalnej
    definicji zapisać jako [O f (fun _ => 1)], gdzie [f] oznaczałoby ilość
    operacji wykonywanych przez funkcję [head].

    Moglibyśmy, ale nie możemy, gdyż zdania dotyczące złożoności obliczeniowej
    funkcji [head], i ogólnie wszystkich funkcji możliwych do zaimplementowania
    w Coqu, nie są zdaniami Coqa (czyli termami typu [Prop]), lecz zdaniami o
    Coqu, a więc zdaniami wyrażonymi w metajęzyku (którym jest tutaj mix języka
    polskiego oraz nieformalnej notacji matematycznej).

    Jest to bardzo istotne spostrzeżenie, więc powtórzmy je, tym razem nieco
    dobitniej: jest niemożliwe, aby w Coqu udowodnić, że jakaś funkcja napisana
    w Coqu ma jakąś złożoność obliczeniową.

    Z tego względu nasza definicja [O] oraz ćwiczenia jej dotyczące mają
    jedynie charakter pomocniczy. Ich celem jest pomóc ci zrozumieć, czym
    jest złożoność asymptotyczna. Wszelkie dowodzenie złożoności obliczeniowej
    będziemy przeprowadzać w sposób tradycyjny, czyli "na kartce". *)

(** **** Ćwiczenie *)

(** Udowodnij, że [O] jest relacją zwrotną i przechodnią. Pokaż też, że nie
    jest ani symetryczna, ani słabo antysymetryczna. *)

Lemma O_refl :
  forall f : nat -> nat, O f f.
(* begin hid e*)
Proof.
  intros. red. exists 1, 0. intros. simpl. rewrite <- plus_n_O. trivial.
Qed.
(* end hide *)

Lemma O_trans :
  forall f g h : nat -> nat,
    O f g -> O g h -> O f h.
(* begin hide *)
Proof.
  unfold O; intros. destruct H as [c1 [n1 H1]], H0 as [c2 [n2 H2]].
  exists (c1 * c2), (max n1 n2). intros.
  destruct (Max.max_spec n1 n2).
    destruct H0. apply Le.le_trans with (c1 * g n').
      apply H1. omega.
      rewrite <- Mult.mult_assoc. apply Mult.mult_le_compat_l, H2. omega.
    destruct H0. apply Le.le_trans with (c1 * g n').
      apply H1. omega.
      rewrite <- Mult.mult_assoc. apply Mult.mult_le_compat_l, H2. omega.
Qed.
(* end hide *)

Lemma O_asym :
  exists f g : nat -> nat, O f g /\ ~ O g f.
(* begin hide *)
Proof.
  unfold O. exists (fun _ => 0), (fun n => n). split.
    exists 0, 0. intros. simpl. trivial.
    intro. destruct H as [c [n H]]. assert (n <= S n) by omega.
      specialize (H (S n) H0). omega.
Qed.
(* end hide *)

Lemma O_not_weak_antisym :
  exists f g : nat -> nat, O f g /\ O g f /\ f <> g.
(* begin hide *)
Proof.
  unfold O. exists (fun _ => 42), (fun _ => 43). repeat split.
    exists 1, 0. intros. omega.
    exists 2, 0. intros. omega.
    intro. cut (42 = 43).
      inversion 1.
      change 42 with ((fun _ => 42) 0) at 1. change 43 with ((fun _ => 43) 0).
        rewrite H. trivial.
Qed.
(* end hide *)

(** * Duże Theta *)

(** ** Definicja i idea *)

Definition Theta (f g : nat -> nat) : Prop := O f g /\ O g f.

(** Definicja [Theta f g] głosi, że [O f g] i [O g f]. Przypomnijmy, że
    [O f g] możemy rozumieć jako "[f] rośnie asymptotycznie nie szybciej
    niż [g]", zaś [O g f] analogicznie jako "[g] rośnie asymptotycznie
    nie szybciej niż [f]". Wobec tego interpretacja [Theta f g] nasuwa się
    sama: "[f] i [g] rosną asymptotycznie w tym samym tempie".

    [Theta] jest relacją równoważności, która oddaje nieformalną ideę
    najbardziej znaczącego komponentu funkcji, którą posłużyliśmy się
    opisując intuicje dotyczące [O]. Parafrazując:
    - [O f g] znaczy tyle, co "najbardziej znaczący komponent [f] jest
      mniejszy lub równy najbardziej znaczącemu komponentowi [g]"
    - [Theta f g] znaczy "najbardziej znaczące komponenty [f] i [g] są
      sobie równe". *)

(** **** Ćwiczenie *)

(** Pokaż też, że [Theta] jest relacją równoważności. *)

(* begin hide *)
Theorem Theta_spec :
  forall f g : nat -> nat,
    Theta f g <->
    exists c1 c2 n : nat,
      forall n' : nat, n <= n' -> c1 * g n' <= f n' <= c2 * g n'.
Proof.
  split; intros.
    destruct H as [[c1 [n1 H1]] [c2 [n2 H2]]].
      exists 1, c1, (max n1 n2). intros. split.
        Focus 2. apply H1. eapply Le.le_trans with (max n1 n2).
          apply Max.le_max_l.
          assumption.
        assert (n2 <= n').
          apply Le.le_trans with (max n1 n2).
            apply Le.le_trans with (max n1 n2).
              apply Max.le_max_r.
              trivial.
            assumption.
          specialize (H2 _ H0). destruct c2; simpl in *.
            omega.
            assert (g n' <= f n').
Abort.
(* end hide *)

Theorem Theta_refl :
  forall f : nat -> nat, Theta f f.
(* begin hide *)
Proof.
  intros. red. split; apply O_refl.
Qed.
(* end hide *)

Theorem Theta_trans :
  forall f g h : nat -> nat,
    Theta f g -> Theta g h -> Theta f h.
(* begin hide *)
Proof.
  unfold Theta; intros. destruct H, H0. split; eapply O_trans; eauto.
Qed.
(* end hide *)

Theorem Theta_sym :
  forall f g : nat -> nat,
    Theta f g -> Theta g f.
(* begin hide *)
Proof.
  unfold Theta. intros. destruct H. split; assumption.
Qed.
(* end hide *)