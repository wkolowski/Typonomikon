(** * D2b: Różne spojrzenia na rekursję [TODO] *)

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

(** * [foldr] i [foldl], czyli reguły rekursji dla list (TODO) *)

From Typonomikon Require Import D5a.

Fixpoint foldr
  {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : B :=
match l with
| [] => b
| h :: t => f h (foldr f b t)
end.

Fixpoint foldl
  {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : A :=
match l with
| [] => a
| h :: t => foldl f (f a h) t
end.

(** Nie będę na razie tłumaczył, jaka ideologia stoi za [foldr] i [foldl].
    Napiszę o tym później, a na razie porcja zadań.

    Zaimplementuj za pomocą [foldr] i [foldl] następujące funkcje:
    [length], [app], [rev], [map], [join], [filter], [takeWhile],
    [dropWhile].

    Udowodnij, że zdefiniowane przez ciebie funkcje pokrywają się ze
    swoimi klasycznymi odpowiednikami. *)

(* begin hide *)
(* Reszta polecenia: [repeat], [nth], [take], [drop] *)

Functional Scheme foldr_ind := Induction for foldr Sort Prop.
Functional Scheme foldl_ind := Induction for foldl Sort Prop.

Definition lengthF {A : Type} (l : list A) : nat :=
  foldr (fun _ => S) 0 l.

Definition snocF {A : Type} (x : A) (l : list A) : list A :=
  foldr (@cons A) [x] l.

Definition appF {A : Type} (l1 l2 : list A) : list A :=
  foldr (@cons A) l2 l1.

Definition revF {A : Type} (l : list A) : list A :=
  foldr snoc [] l.

Definition revF' {A : Type} (l : list A) : list A :=
  foldl (fun t h => h :: t) [] l.

Definition mapF {A B : Type} (f : A -> B) (l : list A) : list B :=
  foldr (fun h t => f h :: t) [] l.

Definition joinF {A : Type} (l : list (list A)) : list A :=
  foldr app [] l.

Require Import Bool.

Definition allF {A : Type} (p : A -> bool) (l : list A) : bool :=
  foldr (fun h t => p h && t) true l.

Definition anyF {A : Type} (p : A -> bool) (l : list A) : bool :=
  foldr (fun h t => p h || t) false l.

Definition findF {A : Type} (p : A -> bool) (l : list A) : option A :=
  foldr (fun h t => if p h then Some h else t) None l.

Definition findIndexF
  {A : Type} (p : A -> bool) (l : list A) : option nat :=
    foldr (fun h t => if p h then Some 0 else option_map S t) None l.

Definition countF {A : Type} (p : A -> bool) (l : list A) : nat :=
  foldr (fun h t => (if p h then 1 else 0) + t) 0 l.

Definition filterF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then h :: t else t) [] l.

Definition takeWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then h :: t else []) [] l.

Ltac solve_fold := intros;
match goal with
| |- context [@foldr ?A ?B ?f ?a ?l] =>
  functional induction @foldr A B f a l; cbn; trivial;
  match goal with
  | H : ?x = _ |- context [?x] => rewrite ?H; auto
  end
| |- context [@foldl ?A ?B ?f ?a ?l] =>
  functional induction @foldl A B f a l; cbn; trivial;
  match goal with
  | H : ?x = _ |- context [?x] => rewrite ?H; auto
  end
end.

(* end hide *)

Lemma lengthF_spec :
  forall (A : Type) (l : list A),
    lengthF l = length l.
(* begin hide *)
Proof.
  unfold lengthF; induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold lengthF. solve_fold.
Qed.
(* end hide *)

Lemma snocF_spec :
  forall (A : Type) (x : A) (l : list A),
    snocF x l = snoc x l.
(* begin hide *)
Proof.
  intros. unfold snocF. solve_fold.
Qed.
(* end hide *)

Lemma appF_spec :
  forall (A : Type) (l1 l2 : list A),
    appF l1 l2 = l1 ++ l2.
(* begin hide *)
Proof.
  unfold appF; induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    rewrite IHt1. trivial.
Restart.
  intros. unfold appF. solve_fold.
Qed.
(* end hide *)

Lemma revF_spec :
  forall (A : Type) (l : list A),
    revF l = rev l.
(* begin hide *)
Proof.
  unfold revF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold revF. solve_fold.
Qed.
(* end hide *)

(* begin hide *)
Lemma revF'_spec :
  forall (A : Type) (l : list A),
    revF' l = rev l.
Proof.
  unfold revF'. intros. replace (rev l) with (rev l ++ []).
    remember [] as acc. clear Heqacc. generalize dependent acc.
      induction l as [| h t]; cbn; intros; subst.
        reflexivity.
        rewrite IHt, app_snoc_l. reflexivity.
    apply app_nil_r.
Qed.
(* end hide *)

Lemma mapF_spec :
  forall (A B : Type) (f : A -> B) (l : list A),
    mapF f l = map f l.
(* begin hide *)
Proof.
  unfold mapF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold mapF. solve_fold.
Qed.
(* end hide *)

Lemma joinF_spec :
  forall (A : Type) (l : list (list A)),
    joinF l = join l.
(* begin hide *)
Proof.
  unfold joinF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold joinF. solve_fold.
Qed.
(* end hide *)

Lemma allF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    allF p l = all p l.
(* begin hide *)
Proof.
  unfold allF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      assumption.
      reflexivity.
Qed.
(* end hide *)

Lemma anyF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    anyF p l = any p l.
(* begin hide *)
Proof.
  unfold anyF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma findF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    findF p l = find p l.
(* begin hide *)
Proof.
  unfold findF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma findIndexF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndexF p l = findIndex p l.
(* begin hide *)
Proof.
  unfold findIndexF.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      rewrite IHt.
      destruct (findIndex p t); cbn; reflexivity.
Qed.
(* end hide *)

Lemma countF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    countF p l = count p l.
(* begin hide *)
Proof.
  unfold countF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      rewrite IHt. reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma filterF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    filterF p l = filter p l.
(* begin hide *)
Proof.
  unfold filterF; induction l as [| h t].
    cbn. trivial.
    cbn. rewrite IHt. trivial.
Restart.
  intros. unfold filterF. solve_fold.
Qed.
(* end hide *)

Lemma takeWhileF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    takeWhileF p l = takeWhile p l.
(* begin hide *)
Proof.
  unfold takeWhileF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold takeWhileF. solve_fold.
Qed.
(* end hide *)

(** ** Lematy o foldach (TODO) *)

Lemma foldr_app :
  forall (A B : Type) (f : A -> B -> B) (b : B) (l1 l2 : list A),
    foldr f b (l1 ++ l2) = foldr f (foldr f b l2) l1.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Lemma foldr_rev :
  forall (A B : Type) (f : A -> B -> B) (l : list A) (b : B),
    foldr f b (rev l) = foldl (flip f) b l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite snoc_app_singl, foldr_app. cbn. rewrite IHt. unfold flip. reflexivity.
Qed.
(* end hide *)

Lemma foldl_app :
  forall (A B : Type) (f : A -> B -> A) (l1 l2 : list B) (a : A),
    foldl f a (l1 ++ l2) = foldl f (foldl f a l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma foldl_snoc :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A) (b : B),
    foldl f a (l ++ [b]) = f (foldl f a l) b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma foldl_rev :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    foldl f a (rev l) = foldr (flip f) a l.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l). rewrite foldr_rev.
  rewrite rev_rev. reflexivity.
Qed.
(* end hide *)

(** * Sumy kroczące (TODO) *)

Fixpoint scanl
  {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : list A :=
    a ::
match l with
| [] => []
| h :: t => scanl f (f a h) t
end.

Compute scanl plus 0 [1; 2; 3; 4; 5].

Definition scanl1
  {A : Type} (f : A -> A -> A) (l : list A) : list A :=
match l with
| [] => []
| h :: t => scanl f h t
end.

Compute scanl1 plus [1; 2; 3; 4; 5].

Fixpoint scanr
  {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : list B :=
match l with
| [] => [b]
| h :: t =>
  let
    qs := scanr f b t
  in
  match qs with
  | [] => [f h b]
  | q :: _ => f h q :: qs
  end
end.

Compute scanr plus 0 [1; 2; 3; 4; 5].

Fixpoint scanr1
  {A : Type} (f : A -> A -> A) (l : list A) : list A :=
match l with
| [] => []
| [h] => [h]
| h :: t =>
  let
    qs := scanr1 f t
  in
  match qs with
  | [] => []
  | q :: _ => f h q :: qs
  end
end.

Compute scanr1 plus [1; 2; 3; 4; 5].

Lemma isEmpty_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    isEmpty (scanl f a l) = false.
(* begin hide *)
Proof.
  destruct l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    length (scanl f a l) = 1 + length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma scanl_app :
  forall (A B : Type) (f : A -> B -> A) (l1 l2 : list B) (a : A),
    scanl f a (l1 ++ l2) = 
    take (length l1) (scanl f a l1) ++ scanl f (foldl f a l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    f_equal. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma scanl_snoc :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A) (b : B),
    scanl f a (l ++ [b]) = scanl f a l ++ [foldl f a (l ++ [b])].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma head_scanr :
  forall (A B : Type) (f : A -> B -> B) (b : B) (l : list A),
    head (scanr f b l) =
      match l with
      | [] => Some b
      | _  => Some (foldl (flip f) b (rev l))
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (scanr f b t) eqn: Heq; cbn in *.
      destruct t; inv IHt.
      destruct t; inv IHt.
        inv Heq. cbn. reflexivity.
        cbn. rewrite !snoc_app_singl, !foldl_app. unfold flip; cbn. reflexivity.
Qed.
(* end hide *)

Lemma scanl_rev :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    scanl f a (rev l) = rev (scanr (flip f) a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite snoc_app_singl, scanl_snoc, IHt. destruct (scanr (flip f) a t) eqn: Heq.
      destruct t; cbn in Heq.
        inversion Heq.
        destruct (scanr (flip f) a t); inversion Heq.
      rewrite foldl_app. cbn. unfold flip. do 3 f_equal.
        apply (f_equal head) in Heq. rewrite head_scanr in Heq.
          destruct t; inv Heq.
            cbn. rewrite !snoc_app_singl. reflexivity.
            cbn. rewrite !snoc_app_singl, !foldl_app. unfold flip; cbn. reflexivity.
Qed.
(* end hide *)

Lemma head_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    head (scanl f a l) = Some a.
(* begin hide *)
Proof.
  destruct l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma last_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    last (scanl f a l) = Some (foldl f a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (scanl f (f a h) t) eqn: Heq.
      apply (f_equal isEmpty) in Heq. rewrite isEmpty_scanl in Heq.
        cbn in Heq. congruence.
      rewrite <- Heq, IHt. reflexivity.
Qed.
(* end hide *)