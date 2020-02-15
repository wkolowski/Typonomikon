(** * Typy induktywne są najlepsze *)

(** Znamy już podstawowe typy induktywne, jak liczby naturalne oraz
    listy elementów typu [A]. Wiemy też, że ich induktywność objawia
    się głównie w tym, że możemy definiować funkcje przez rekursję
    strukturalną po argumentach tych typów oraz dowodzić przez indukcję.

    W takim podejściu indukcja i sama induktywność typów induktywnych
    wydają się być czymś w rodzaju domina - wystarczy popchnąć pierwsze
    kilka kostek (przypadki bazowe) i zapewnić, że pozostałe kostki są
    dobrze ułożone (przypadki rekurencyjne), aby zainicjować reakcję
    łańcuchową, która będzie przewracać kostki w nieskończoność.

    Nie jest to jednak jedyny sposób patrzenia na typy induktywne. W tym
    podrozdziale spróbuję przedstawić inny sposób patrzenia, w którym typ
    induktywny to najlepszy typ do robienia termów o pewnym kształcie, a
    rekursja to zmiana kształtu z lepszego na gorszy, ale bardziej
    użyteczny.

    Żeby móc patrzeć z tej perspektywy musimy najpierw ustalić, czym
    jest kształt. Uwaga: "kształt" nie jest pojęciem technicznym i nie
    ma ścisłej definicji - używam tego słowa, żeby ułatwić pracę twojej
    wyobraźni.

    Czym jest kształt termu? Najprościej rzecz ujmując każdy term jest
    drzewkiem, którego korzeniem jest jakiś konstrukt językowy (stała,
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
    - [let x := Prop in 16] - [let]
    - ... i wiele, wiele innych!

    Tak wiele różnych sposobów robienia termów to niesamowite bogactwo,
    więc żeby zgodnie z przysłowiem od tego przybytku nie rozbolała nas
    głowa, musimy pomyśleć o nich w nieco bardziej jednorodny sposób.
    Rozwiązanie jest na szczęście bajecznie proste: zauważ, że wszystkie
    powyższe konstrukty językowe można po prostu zawinąć w funkcję, która
    bierze pewną liczbę argumentów (być może zero) i zwraca coś typu
    [nat].

    To jednak nie w pełni mityguje przyszły-niedoszły ból głowy. O ile
    mamy teraz jednorodny sposób myślenia o kształtach termów, to i tak
    kształtów tych mogą być olbrzymie ilości. Z tego powodu dokonamy
    samoograniczenia i zamiast o wszystkich możliwych kształtach termów
    będziemy wybiórczo skupiać naszą uwagę tylko na tych kształtach,
    które akurat będą nas interesować.

    Dla przykładu, możemy interesować się termami typu [nat] zrobionymi
    wyłącznie za pomocą:
    - konstruktorów [0] i [S]
    - konstruktora [0], stałej [1] oraz funkcji [plus 2]
    - funkcji [plus] i stałych [5] oraz [42]
    - funkcji [mult] i stałej [1]
    - funkcji [length : list nat -> nat] *)

(** **** Ćwiczenie *)

(** Narysuj jakieś nietrywialne termy typu [nat] o takich kształtach. *)

(* begin hide *)
Module wut.
Require Import List.
Import ListNotations.

Definition hehe : nat :=
  length [@length nat []; length [@length nat []; @length nat []]].
End wut.
(* end hide *)

(** **** Ćwiczenie *)

(** Liczbę [n] da się wyrazić za pomocą termu [t], jeżeli [t] oblicza
    się do [n], tzn. komenda [Compute t] daje w wyniku [n].

    Pytanie: termy o których z powyższych kształtów mogą wyrazić
    wszystkie liczby naturalne? *)

(** **** Ćwiczenie *)

(** Liczba [n] ma unikalną reprezentację za pomocą termów o danym
    kształcie, gdy jest tylko jeden term [t], który reprezentuje [n].

    Pytanie: które z powyższych sposobów unikalnie reprezentują
    wszystkie liczby naturalne? *)

(** Sporo już osiągnęliśmy w wyklarowywaniu pojęcia kształtu, ale
    zatrzymajmy się na chwilę i zastanówmy się, czy jest ono zgodne
    z naszymi intuicjami.

    Okazuje się, że otóż nie do końca, bo w naszej obecnej formulacji
    kształty [(0, plus)] oraz [(1, mult)] są różne, podczas gdy obrazki
    jasno pokazują nam, że np. [plus 0 (plus 0 0)] oraz [mult 1 (mult 1 1)]
    wyglądają bardzo podobnie, tylko nazwy są różne.

    Dlatego też modyfikujemy nasze pojęcie kształtu - teraz kształtem
    zamiast stałych i funkcji, jak [0] i [plus], nazywać będziemy typy
    tych stałych i funkcji. Tak więc kształtem termów zrobionych z [0]
    i [plus] będzie [nat] (bo [0 : nat]) i [nat -> nat -> nat] (bo
    [plus : nat -> nat -> nat]). Teraz jest już jasne, że [1] i [mult]
    dają dokładnie ten sam kształt, bo typem [1] jest [nat], zaś typem
    [mult] jest [nat -> nat -> nat].

    Zauważmy, że można nasze pojęcie kształtu jeszcze troszkę uprościć:
    - po pierwsze, każdą stałą można traktować jako funkcję biorącą
      argument typu [unit], np. możemy [0 : nat] reprezentować za pomocą
      funkcji [Z : unit -> nat] zdefiniowanej jako
      [Z := fun _ : unit => 0]
    - po drugie, funkcje biorące wiele argumentów możemy reprezentować za
      pomocą funkcji biorących jeden argument, np.
      [plus : nat -> nat -> nat] możemy reprezentować za pomocą
      [plus' : nat * nat -> nat], który jest zdefiniowany jako
      [plus' := fun '(n, m) => plus n m]
    - po trzecie, ponieważ kodziedzina wszystkich funkcji jest taka
      sama (w naszym przypadku [nat]), możemy połączyć wiele funkcji w
      jedną, np. [0] i [plus] możemy razem reprezentować jako
      [Zplus : unit + nat * nat -> nat], zdefiniowaną jako
      [Zplus := fun x => match x with | inl _ => 0 | inr (n, m) => plus n m end]

    Dzięki tym uproszczeniom (albo utrudnieniom, zależy kogo spytacie)
    możemy teraz jako kształt traktować nie funkcje albo same ich typy,
    lecz tylko jeden typ, który jest dziedziną takiej połączonej funkcji.
    Tak więc zarówno [(0, plus)] jak i [(1, mult)] są kształtu
    [unit + nat * nat]. Ma to sporo sensu: drzewa reprezentujące te termy
    są albo liściem (reprezentowanym przez [unit]), albo węzłem, który
    rozgałęzia się na dwa poddrzewa (reprezentowanym jako [nat * nat]).

    Ale to jeszcze nie wszystko. Przecież [nat] to nie jedyny typ, w
    którym można robić termy o kształcie [unit + nat * nat]. Jeżeli
    przyjrzymy się, jak wyglądają termy zrobione za pomocą ([true, andb])
    albo [(false, orb)], to okaże się, że... mają one dokładnie ten sam
    kształt, mimo że według naszej definicji ich kształt to
    [unit + bool * bool], czyli niby coś innego.

    Ostatnim stadium ewolucji naszego pojęcia kształtu jest taki oto
    zestaw definicji:
    - kształt to funkcja [F : Type -> Type]
    - realizacją kształtu [F] jest typ [X] oraz funkcja [f : F X -> X]

    Widzimy teraz, że [(0, plus)], [(1, mult)], [(true, andb)] oraz
    [(false, orb)] nie są kształtami, lecz realizacjami kształtu
    [F := fun X : Type => 1 + X * X].

    Pora powoli zmierzać ku konkluzji. Na początku powiedzieliśmy, że
    typ induktywny to najlepszy typ do robienia termów o pewnym kształcie.
    Jakim kształcie, zapytasz pewnie, i jak objawia się owa najlepszość?
    Czas się tego dowiedzieć.

    Definiując typ induktywny podajemy jego konstruktory, a całą resztę,
    czyli możliwość definiowania przez dopasowanie do wzorca i rekursję,
    reguły eliminacji etc. dostajemy za darmo. Nie dziwota więc, że to
    właśnie konstruktory są realizacją kształtu, którego dany typ jest
    najlepszym przykładem.

    Napiszmy to jeszcze raz, dla jasności: typ induktywny to najlepszy
    sposobem robienia termów o kształcie realizowanym przez jego
    konstruktory.

    W naszym [nat]owym przykładzie oznacza to, że [nat] jest najlepszym
    sposobem robienia termów o kształcie [F := fun X => unit + X], czyli
    termów w kształcie "sznurków" (konstruktor [S] to taki supełek na
    sznurku, a [0] reprezentuje koniec sznurka). Są też inne realizacje
    tego sznurkowego kształtu, jak np. stała [42 : nat] i funkcja
    [plus 8 : nat -> nat] albo stała [true : bool] i funkcja
    [negb : bool -> bool], albo nawet zdanie [False : Prop] oraz
    negacja [not : Prop -> Prop], ale żadna z nich nie jest najlepsza.

    Jak objawia się najlepszość typu induktywnego? Ano, dwojako:
    - po pierwsze, objawia się w postaci rekursora, który bierze jako
      argument inną realizację danego kształtu i przerabia term typu
      induktywnego (czyli przedstawiciela najlepszej reprezentacji)
      na term w tej innej realizacji
    - po drugie, rekursor jest unikalny

    Żeby nie być gołosłownym, zobaczmy przykłady: *)

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
    oblicza się do [true]. *)

(** **** Ćwiczenie *)

(** Mamy [nat_rec' true negb : nat -> bool], a zatem zmiana realizacji
    sznurka z [(0, S)] na [(true, negb)] odpowiada sprawdzeniu jakiejś
    właściwości liczb naturalnych. Jakiej?

    Pisząc wprost: zdefiniuj bezpośrednio przez rekursję taką funkcję
    [f : nat -> bool], że [forall n : nat, nat_rec' true negb n = f n]
    (oczywiście musisz udowodnić, że wszystko się zgadza). *)

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

Module wuut.

Axioms
  (N : Type)
  (Z : N)
  (S : N -> N)
  (N_rec :
    forall {X : Type} (z : X) (s : X -> X), N -> X)
  (N_rec_Z :
    forall {X : Type} (z : X) (s : X -> X),
      N_rec z s Z = z)
  (N_rec_S :
    forall {X : Type} (z : X) (s : X -> X) (n : N),
      N_rec z s (S n) = s (N_rec z s n))
  (N_uniq :
    forall (f : forall {X : Type} (z : X) (s : X -> X), N -> X),
      (forall {X : Type} (z : X) (s : X -> X),
        f z s Z = z) ->
      (forall {X : Type} (z : X) (s : X -> X) (n : N),
        f z s (S n) = s (f z s n)) ->
      @f = @N_rec)
  (N_ind :
    forall
      {P : N -> Type}
      (z : P Z) (s : forall n : N, P n -> P (S n)),
        forall n : N, P n)
  (N_ind_Z :
    forall
      {P : N -> Type}
      (z : P Z) (s : forall n : N, P n -> P (S n)),
        N_ind z s Z = z)
  (N_ind_S :
    forall
      {P : N -> Type}
      (z : P Z) (s : forall n : N, P n -> P (S n))
      (n : N),
        N_ind z s (S n) = s n (N_ind z s n)).

