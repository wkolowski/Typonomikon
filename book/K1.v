(** * K1: Złożoność obliczeniowa *)

(** Prerekwizyty:
    - rekursja strukturalna
    - dowodzenie przez indukcję
    - listy
    - teoria relacji *)

Require Import D5.
Require Import Lia.
Require Import Nat.

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
    nasza funkcja. Pierwszą jest dopasowanie do wzorca. Druga to zwrócenie
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
    Coqu, a więc zdaniami wyrażonymi w metajęzyku (którym jest tutaj język
    polski).

    Jest to bardzo istotne spostrzeżenie, więc powtórzmy je, tym razem nieco
    dobitniej: jest niemożliwe, aby w Coqu udowodnić, że jakaś funkcja napisana
    w Coqu ma jakąś złożoność obliczeniową.

    Z tego względu nasza definicja [O] oraz ćwiczenia jej dotyczące mają
    jedynie charakter pomocniczy. Ich celem jest pomóc ci zrozumieć, czym
    jest złożoność asymptotyczna. Wszelkie dowodzenie złożoności obliczeniowej
    będziemy przeprowadzać w sposób tradycyjny, czyli "na kartce" (no, może
    poza pewną sztuczką, ale o tym później). *)

(** **** Ćwiczenie *)

(** Udowodnij, że [O] jest relacją zwrotną i przechodnią. Pokaż też, że nie
    jest ani symetryczna, ani słabo antysymetryczna. *)

Lemma O_refl :
  forall f : nat -> nat, O f f.
(* begin hide *)
Proof.
  intros. red. exists 1, 0. intros. cbn. rewrite <- plus_n_O. trivial.
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
      apply H1. lia.
      rewrite <- Mult.mult_assoc. apply Mult.mult_le_compat_l, H2. lia.
    destruct H0. apply Le.le_trans with (c1 * g n').
      apply H1. lia.
      rewrite <- Mult.mult_assoc. apply Mult.mult_le_compat_l, H2. lia.
Qed.
(* end hide *)

Lemma O_asym :
  exists f g : nat -> nat, O f g /\ ~ O g f.
(* begin hide *)
Proof.
  unfold O. exists (fun _ => 0), (fun n => n). split.
    exists 0, 0. intros. cbn. trivial.
    intro. destruct H as [c [n H]]. assert (n <= S n) by lia.
      specialize (H (S n) H0). lia.
Qed.
(* end hide *)

Lemma O_not_weak_antisym :
  exists f g : nat -> nat, O f g /\ O g f /\ f <> g.
(* begin hide *)
Proof.
  unfold O. exists (fun _ => 42), (fun _ => 43). repeat split.
    exists 1, 0. intros. lia.
    exists 2, 0. intros. lia.
    intro. cut (42 = 43).
      inversion 1.
      change 42 with ((fun _ => 42) 0) at 1. change 43 with ((fun _ => 43) 0).
        rewrite H. trivial.
Qed.
(* end hide *)

(** ** Duże Omega *)

Definition Omega (f g : nat -> nat) : Prop := O g f.

(** [Omega] to [O] z odwróconymi argumentami. Skoro [O f g] oznacza, że [f]
    rośnie nie szybciej niż [g], to [Omega g f] musi znaczyć, ż [g] rośnie
    nie wolniej niż [f]. [O] oznacza więc ograniczenie górne, a [Omega]
    ograniczenie dolne. *)

Lemma Omega_refl :
  forall f : nat -> nat, Omega f f.
(* begin hide *)
Proof.
  intros. red. apply O_refl.
Qed.
(* end hide *)

Lemma Omega_trans :
  forall f g h : nat -> nat,
    Omega f g -> Omega g h -> Omega f h.
(* begin hide *)
Proof.
  unfold Omega; intros. eapply O_trans; eauto.
Qed.
(* end hide *)

Lemma Omega_not_weak_antisym :
  exists f g : nat -> nat, O f g /\ O g f /\ f <> g.
(* begin hide *)
Proof.
  unfold Omega. apply O_not_weak_antisym.
Qed.
(* end hide *)

(** * Duże Theta *)

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
          specialize (H2 _ H0). destruct c2; cbn in *.
            lia.
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

(** * Złożoność typowych funkcji na listach *)

(** ** Analiza nieformalna *)

(** Skoro rozumiesz już, na czym polegają [O] oraz [Theta], przeanalizujemy
    złożoność typowej funkcji operującej na listach. Zapoznamy się też z
    dwoma sposobami na sprawdzenie poprawności naszej analizy: mimo, że w
    Coqu nie można udowodnić, że dana funkcja ma jakąś złożoność obliczeniową,
    możemy użyć Coqa do upewnienia się, że nie popełniliśmy w naszej analizie
    nieformalnej pewnych rodzajów błędów.

    Naszą ofiarą będzie funkcja [length]. *)

Print length.
(* ===> length = 
        fix length (A : Type) (l : list A) {struct l} : nat :=
        match l with
            | [[]] => 0
            | _ :: t => S (length A t)
        end
        : forall A : Type, list A -> nat *)

(** Oznaczmy złożoność tej funkcji w zależności o rozmiaru (długości) listy
    [l] przez T(n) (pamiętaj, że jest to oznaczenie nieformalne, które nie ma
    nic wspólnego z Coqiem). Jako, że nasza funkcja wykonuje dopasowanie [l],
    rozważmy dwa przypadki:
    - [l] ma postać [[]]. Wtedy rozmiar [l] jest równy 0, a jedyne co robi
      nasza funkcja, to zwrócenie wyniku, które policzymy jako jedna operacja.
      Wobec tego T(0) = 1.
    - [l] ma postać [h :: t]. Wtedy rozmiar [l] jest równy n + 1, gdzie n
      jest rozmiarem [t]. Nasza funkcja robi dwie rzeczy: rekurencyjnie wywołuje
      się z argumentem [t], co kosztuje nas T(n) operacji , oraz dostawia do
      wyniku tego wywołania [S], co kosztuje nas 1 operację. Wobec tego
      T(n + 1) = T(n) + 1. *)

(** Otrzymaliśmy więc odpowiedź w postaci równania rekurencyjnego T(0) = 1;
    T(n + 1) = T(n) + 1. Widać na oko, że T(n) = n + 1, a zatem złożoność
    funkcji [length] to O(n). *)

(** ** Formalne sprawdzenie *)

(** **** Ćwiczenie *)

(** Żeby przekonać się, że powyższy akapit nie kłamie, zaimplementuj [T]
    w Coqu i udowodnij, że rzeczywiście rośnie ono nie szybciej niż
    [fun n => n]. *)

(* begin hide *)
Fixpoint T (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => S (T n')
end.
(* end hide *)

Theorem T_spec_0 : T 0 = 1.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Theorem T_spec_S : forall n : nat, T (S n) = 1 + T n.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Theorem T_sum : forall n : nat, T n = n + 1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    trivial.
    rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem O_T_n : O T (fun n => n).
(* begin hide *)
Proof.
  red. exists 2, 1. intros. rewrite T_sum. lia.
Qed.
(* end hide *)

(** Prześledźmy jeszcze raz całą analizę, krok po kroku:
    - oznaczamy złożoność analizowanej funkcji przez T
    - patrząc na definicję analizowanej funkcji definiujemy T za pomocą równań
      T(0) = 1 i T(n + 1) = T(n) + 1
    - rozwiązujemy równanie rekurencyjne i dostajemy T(n) = n + 1
    - konkludujemy, że złożoność analizowanej funkcji to O(n) *)

(** W celu sprawdzenia analizy robimy następujące rzeczy:
    - implementujemy T w Coqu
    - dowodzimy, że rozwiązaliśmy równanie rekurencyjne poprawnie
    - pokazujemy, że [O T (fun n => n)] zachodzi *)

(** Dzięki powyższej procedurze udało nam się wyeliminować podejrzenie co do
    tego, że źle rozwiązaliśmy równanie rekurencyjne lub że źle podaliśmy
    złożoność za pomocą dużego O. Należy jednak po raz kolejny zaznaczyć, że
    nasza analiza nie jest formalnym dowodem tego, że funkcja [length] ma
    złożoność O(n). Jest tak dlatego, że pierwsza część naszej analizy jest
    nieformalna i nie może zostać w Coqu sformalizowana. *)


(** Jest jeszcze jeden sposób, żeby sprawdzić naszą nieformalną analizę.
    Mianowicie możemy sprawdzić nasze mniemanie, że T(n + 1) = T(n) + 1,
    dowodząc formalnie w Coqu, że pewna wariacja funkcji [length] wykonuje
    co najwyżej [n] wywołań rekurencyjnych, gdzie [n] jest rozmiarem jej
    argumentu. *)

Fixpoint length' {A : Type} (fuel : nat) (l : list A) : option nat :=
match fuel, l with
    | 0, _ => None
    | _, [] => Some 0
    | S fuel', _ :: t =>
        match length' fuel' t with
            | None => None
            | Some n => Some (S n)
        end
end.

(** Pomysł jest prosty: zdefiniujemy wariację funkcji [length] za pomocą
    techniki, którą nazywam "rekursją po paliwie". W porównaniu do [length],
    której argumentem głównym jest [l : list A], [length'] ma jeden dodatkowy
    argument [fuel : nat], który będziemy zwać paliwem, a który jest jej
    argumentem głównym

    Nasza rekursja wygląda tak, że każde wywołanie rekurencyjne zmniejsza
    zapasy paliwa o [1], ale z pozostałymi argumentami możemy robić dowolne
    cuda. Żeby uwzględnić możliwość wyczerpania się paliwa, nasza funkcja
    zwraca wartość typu [option nat] zamiast samego [nat]. Wyczerpaniu się
    paliwa odpowiada wynik [None], zaś [Some] oznacza, że funkcja zakończyła
    się wykonywać przed wyczerpaniem się paliwa.

    Paliwo jest więc tak naprawdę maksymalną ilością wywołań rekurencyjnych,
    które funkcja może wykonać. Jeżeli uda nam się udowodnić, że dla pewnej
    ilości paliwa funkcja zawsze zwraca [Some], będzie to znaczyło, że
    znaleźliśmy górne ograniczenie ilości wywołań rekurencyjnych niezbędnych
    do poprawnego wykonania się funkcji. *)

(** **** Ćwiczenie *)

(** Uwaga, trudne. *)

(* begin hide *)
Functional Scheme length'_ind := Induction for length' Sort Prop.
(* end hide *)

Theorem length'_rec_depth :
  forall (A : Type) (l : list A),
    length' (S (length l)) l = Some (length l).
(* begin hide *)
Proof.
  intros. remember (S (length l)) as n.
  functional induction @length' A n l; try inversion Heqn; subst; cbn.
    trivial.
    rewrite e1 in IHo. specialize (IHo eq_refl). inversion IHo; subst.
      trivial.
    specialize (IHo eq_refl). rewrite IHo in e1. inversion e1.
Qed.
(* end hide *)

(** Twierdzenie to wygląda dość kryptycznie głównie ze względu na fakt, że
    [length l] jest zarówno analizowaną przez nas funkcją, jaki i funkcją
    obliczającą rozmiar listy [l].

    Żeby lepiej zrozumieć, co się stało, spróbujmy zinterpretować powyższe
    twierdzenie. Mówi ono, że dla dowolnego [A : Type] i [l : list A],
    jeżeli wywołamy [length'] na [l] dając jej [S (length l)] paliwa, to
    zwróci ona [Some (length l)].

    Innymi słowy, [S (length l)] paliwa to dostatecznie dużo, aby funkcja
    wykonała się poprawnie. Dodatkowo [Some (length l)] jest pewną formą
    specyfikacji dla funkcji [length'], która mówi, że jeżeli [length']
    ma dostatecznie dużo paliwa, to wywołanie jej na [l] daje taki sam
    wynik jak [length l], czyli nie pomyliliśmy się przy jej definiowaniu
    (chcieliśmy, żeby była to "wariacja" [length], która daje takie same
    wyniki, ale jest zdefiniowana przez rekursję po paliwie).

    Na tym kończy się nasz worek sztuczek formalnych, które pomagają nam
    upewnić się w poprawności naszej analizy nieformalnej. *)

(** * Złożoność problemu *)
    
(** Dotychczas zajmowaliśmy się złożonością obliczeniową funkcji. Złożoność ta
    oznacza faktycznie złożoność sposobu rozwiązania pewnego problemu — w naszym
    przypadku były to problemy zwrócenia głowy listy (funkcja [head]) oraz
    obliczenia jej długości (funkcja [length]).

    Złożoność ta nie mówi jednak nic o innych sposobach rozwiązania tego samego
    problemu. Być może istnieje szybszy sposób obliczania długości listy?
    Zajmijmy się więc przez krótką chwilę koncepcją pokrewną koncepcji złożoności
    obliczeniowej programu — jest nią koncepcja złożoności obliczeniowej
    problemu.

    Na początku rozdziału stwierdziliśmy, że naszym celem będzie badanie
    "czasu działania programu". Taki cel może jednak budzić pewien niesmak:
    dlaczego mielibyśmy robić coś takiego?

    Czas (także w swym informatycznym znaczeniu, jako ilość operacji) jest
    cennym zasobem i nie chcielibyśmy używać go nadaremnie ani marnować.
    Jeżeli poznamy złożoność obliczeniową zarówno problemu, jak i jego
    rozwiązania, to będziemy mogli stwierdzić, czy nasze rozwiązanie jest
    optymalne (w sensie asymptotycznym, czyli dla instancji problemu, w
    której rozmiary argumentów są bardzo duże).

    Na nasze potrzeby zdefiniujmy złożoność problemu jako złożoność najszybszego
    programu, który rozwiązuje ten problem. Podobnie jak pojęcie złożoności
    obliczeniowej programu, jest niemożliwe, aby pojęcie to sformalizować w
    Coqu, będziemy się więc musieli zadowolić dywagacjami nieformalnymi.

    Zacznijmy od [head] i problemu zwrócenia głowy listy. Czy można to zrobić
    szybciej, niż w czasie stałym? Oczywiście nie. Czas stały to najlepsze, co
    możemy uzyskać (zastanów się przez chwilę nad tym, dlaczego tak jest).
    Oczywiście należy to zdanie rozumieć w sensie asymptotycznym: jeżeli chodzi
    o dokładną złożoność, to różne funkcje działające w czasie stałym mogą
    wykonywać różną ilość operacji — zarówno "jeden" jak i "milion" oznaczają
    czas stały. Wobec tego złożoność problemu zwrócenia głowy listy to O(1).

    A co z obliczaniem długości listy? Czy można to zrobić szybciej niż w czasie
    O(n)? Tutaj również odpowiedź brzmi "nie". Jest dość oczywiste, że w celu
    obliczenia długość całej listy musimy przejść ją całą. Jeżeli przejdziemy
    tylko pół, to obliczymy długość jedynie połowy listy. *)

(** * Przyspieszanie funkcji rekurencyjnych *)

(** ** Złożoność [rev] *)

(** Przyjrzyjmy się złożoności funkcji [rev]. *)

Print rev.
(* ===> rev = 
        fix rev (A : Type) (l : list A) {struct l} : list A :=
        match l with
            | [] => []
            | h :: t => rev A t ++ [h]
        end
        : forall A : Type, list A -> list A *)

(** Oznaczmy szukaną złożoność przez T(n). Z przypadku gdy [l] jest postaci
    [[]] uzyskujemy T(0) = 1. W przypadku gdy [l] jest postaci [h :: t]
    mamy wywołanie rekurencyjne o koszcie T(n); dostawiamy też [h] na koniec
    odwróconego ogona. Jaki jest koszt tej operacji? Aby to zrobić, musimy
    przebyć [rev t] od początku do końca, a więc koszt ten jest równy długości
    listy [l]. Stąd T(n + 1) = T(n) + n.

    Pozostaje nam rozwiązać równanie. Jeżeli nie potrafisz tego zrobić,
    dla prostych równań pomocna może być strona https://www.wolframalpha.com/.
    Rozwijając to równanie mamy T(n) = n + (n - 1) + (n - 2) + ... + 1, więc
    T jest rzędu O(n^2).

    A jaka jest złożoność problemu odwracania listy? Z pewnością nie można tego
    zrobić, jeżeli nie dotkniemy każdego elementu listy. Wobec tego możemy ją
    oszacować z dołu przez Omega(n).

    Z taką sytuacją jeszcze się nie spotkaliśmy: wiemy, że asymptotycznie
    problem wymaga Omega(n) operacji, ale nasze rozwiązanie wykonuje O(n^2)
    operacji. Być może zatem możliwe jest napisanie funkcji [rev] wydajniej. *)

(** ** Pamięć *)

(** Przyjrzyj się jeszcze raz definicji funkcji [rev]. Funkcja [rev] nie ma
    pamięci — nie pamięta ona, jaką część wyniku już obliczyła. Po prostu
    wykonuje dopasowanie na swym argumencie i wywołuje się rekurencyjnie.

    Funkcję [rev] będziemy mogli przyspieszyć, jeżeli dodamy jej pamięć. Na
    potrzeby tego rozdziału nie będziemy traktować pamięci jak zasobu, lecz
    jako pewną abstrakcyjną ideę. Przyjrzyjmy się poniższej, alternatywnej
    implementacji funkcji odwracającej listę. *)

Fixpoint rev_aux {A : Type} (l acc : list A) : list A :=
match l with
    | [] => acc
    | h :: t => rev_aux t (h :: acc)
end.

Fixpoint rev' {A : Type} (l : list A) : list A := rev_aux l [].

(** Funkcja [rev_aux] to serce naszej nowej implementacji. Mimo, że odwraca
    ona listę [l], ma aż dwa argumenty — poza [l] ma też argument [acc : list A],
    który nazywać będziemy akumulatorem. To właśnie on jest pamięcią tej
    funkcji. Jednak jego "bycie pamięcią" nie wynika z jego nazwy, a ze
    sposobu, w jaki użyliśmy go w definicji [rev_aux].

    Gdy [rev_aux] natrafi na pustą listę, zwraca wartość swego akumulatora.
    Nie powinno nas to dziwić — wszakże ma w nim zapamiętany cały wynik (bo
    zjadła już cały argument [l]). Jeżeli napotyka listę postaci [h :: t],
    to wywołuje się rekurencyjnie na ogonie [t], ale z akumulatorem, do
    którego dostawia na początek [h]. *)

Compute rev_aux [1; 2; 3; 4; 5] [].
(* ===> = [5; 4; 3; 2; 1] : list nat *)

(** Widzimy więc na własne oczy, że [rev_aux] rzeczywiście odwraca listę.
    Robi to przerzucając swój argument główy kawałek po kawałku do swojego
    akumulatora — głowa [l] trafia do akumulatora na samym początku, a więc
    znajdzie się na samym jego końcu, gdyż przykryją ją dalsze fragmenty
    listy [l]. *)

Compute rev_aux [1; 2; 3; 4; 5] [6; 6; 6].

(** Trochę cię okłamałem twierdząc, że [rev_aux] odwraca [l]. Tak naprawdę
    oblicza ona odwrotność [l] z doklejonym na końcu akumulatorem. Tak więc
    wynik zwracany przez [rev_aux] zależy nie tylko od [l], ale także od
    akumulatora [acc]. Właściwą funkcję [rev'] uzyskujemy, inicjalizując
    wartość akumulatora w [rev_aux] listą pustą. *)

(** **** Ćwiczenie *)

(** Udowodnij poprawność funkcji [rev']. *)

Lemma rev_aux_spec :
  forall (A : Type) (l acc : list A),
    rev_aux l acc = rev l ++ acc.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intro.
    trivial.
    rewrite IHt. rewrite <- app_assoc. cbn. trivial.
Qed.
(* end hide *)

Theorem rev'_spec :
  forall (A : Type) (l : list A), rev' l = rev l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?rev_aux_spec; trivial.
Qed.
(* end hide *)

(** Skoro już wiemy, że udało nam się poprawnie zdefiniować [rev'], czyli
    alternatywne rozwiązanie problemu odwracania listy, pozostaje nam tylko
    sprawdzić, czy rzeczywiście jest ono szybsze niż [rev]. Zanim dokonamy
    analizy, spróbujemy sprawdzić naszą hipotezę empirycznie — w przypadku
    zejścia z O(n^2) do O(n) przyspieszenie powinno być widoczne gołym
    okiem. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcje [to0], gdzie [to0 n] jest listą liczb od [n] do [0].
    Udowodnij poprawność zdefiniowanej funkcji. *)

(* begin hide *)
Fixpoint to0 (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: to0 n'
end.
(* end hide *)

Theorem to0_spec :
  forall n k : nat, k <= n -> elem k (to0 n).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H; subst; clear H. constructor.
    destruct k as [| k']; cbn.
      constructor. apply IHn'. lia.
      inversion H; subst; clear H.
        constructor.
        right. apply IHn'. assumption.
Qed.
(* end hide *)

Time Eval compute in rev (to0 2000).
(* ===> (...) Finished transaction in 7. secs (7.730824u,0.s) *)

Time Eval compute in rev' (to0 2000).
(* ===> (...) Finished transaction in 4. secs (3.672441u,0.s) *)

(** Nasze mierzenie przeprowadzić możemy za pomocą komendy [Time]. Odwrócenie
    listy 2000 elementów na moim komputerze zajęło [rev] 7.73 sekundy, zaś
    [rev'] 3.67 sekundy, a więc jest ona w tym przypadku ponad dwukrotnie
    szybsza. Należy jednak zaznaczyć, że empiryczne próby badania szybkości
    programów w Coqu nie są dobrym pomysłem, gdyż nie jest on przystosowany
    do szybkiego wykonywania programów — jest on wszakże głównie asystentem
    dowodzenia.

    Zakończmy analizą teoretyczną złożoności [rev']. Oznaczmy czas działania
    [rev_aux] przez T(n). Dla [[]] zwraca ona jedynie akumulator, a zatem
    T(0) = 1. Dla [h :: t] przekłada ona głowę argumentu do akumulatora i
    wywołuje się rekurencyjnie, czyli T(n + 1) = T(n) + 1. Rozwiązując
    równanie rekurencyjne dostajemy T(n) = n + 1, a więc złożoność [rev_aux]
    to O(n). Jako, że [rev'] wywołuje [rev_aux] z pustym akumulatorem, to
    również jej złożoność wynosi O(n). *)

(** * Podsumowanie *)

(** W tym rozdziale postawiliśmy sobie za cel mierzenie "czasu" działania
    programu. Szybko zrezygnowaliśmy z tego celu i zamieniliśmy go na analizę
    złożonóści obliczeniowej, choć bezpośrednie mierzenie nie jest niemożliwe.

    Nauczyliśmy się analizować złożoność funkcji rekurencyjnych napisanych
    w Coqu, a także analizować złożoność samych problemów, które owe funkcje
    rozwiązują. Poznaliśmy też kilka sztuczek, w których posłużyliśmy się
    Coqiem do upewnienia się w naszych analizach.

    Następnie porównując złożoność problemu odwracania listy ze złożonością
    naszego rozwiązania zauważyliśmy, że moglibyśmy rozwiązać go wydajniej.
    Poznaliśmy abstrakcyjne pojęcie pamięci i przyspieszyliśmy za jego pomocą
    funkcję [rev].

    Zdobytą wiedzę będziesz mógł od teraz wykorzystać w praktyce — za każdym
    razem, kiedy wyda ci się, że jakaś funcja "coś wolno działa", zbadaj jej
    złożoność obliczeniową i porównaj ze złożonością problemu, który rozwiązuje.
    Być może uda ci się znaleźć szybsze rozwiązanie. *)