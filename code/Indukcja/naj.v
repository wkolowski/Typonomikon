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
    podrozdziale spróbuję przedstawić inny, w którym typ induktywny to
    najlepszy typ do robienia termów o pewnym kształcie.

    Żeby móc patrzeć z tej perspektywy musimy najpierw ustalić, czym
    jest kształt. Uwaga: "kształt" nie jest pojęciem technicznym i nie
    me ścisłej definicji - używam tego słowa, żeby ułatwić pracę twojej
    wyobraźni.

    Na nasze potrzeby kształtem nazwiemy po prostu rodzinę typów
    indeksowaną typami, czyli coś typu [Type -> Type]. Przykłady:
    - [F = fun A : Type => unit + A]
    - [G = fun A : Type => unit + nat * A]
    - [H = fun _ : Type => B * C]

    Uwaga: zdefiniujmy naprędce pewną notację, która przyda nam się
    już za sekundkę. Jeżeli [f : A -> X] oraz [g : B -> X], to
    [[f, g] : A + B -> X] jest dane przez [[f, g] (inl a) = f a]
    oraz [[f, g] (inr b) = g b].

    Realizacją danego kształtu [F : Type -> Type] nazwiemy typ
    [X : Type] wraz z funkcją [f : F X -> X]. Przykłady:
    - dla [F]: [nat] wraz z funkcją [[fun _ => 0], S]
    - dla [G]: [nat] wraz z funkcją [[fun _ => 42], plus], gdzie
      trochę oszukujemy i myślimy, że [plus] ma typ [nat * nat -> nat]
    - dla [H]: [B * C] wraz z funkcją [fun x : B * C => x] *)

(** Resztki starego podejścia:

    Rozważmy bardzo konkretny przykład, czyli typ [list nat]. Jak jest
    struktura tego typu? Co to w ogóle jest struktura typu? Lista
    elementów typu [A] może być albo [nil]em, albo być postaci [cons h t]
    dla [h : A] i [t : list A]. Tak więc możemy powiedzieć, że strukturą
    danego typu induktywnego są jego konstruktory. Wobec tego struktura
    typu [list A] to

    [nil : list nat]

    oraz

    [cons : nat -> list nat -> list nat]

    Możemy niezbyt spostrzegawczo powiedzieć, że typ [list nat] ma
    strukturę typu [list nat]. Fajnie, ale czy są jakieś inne typy,
    niekoniecznie induktywne, które mają taką samą strukturę jak
    [list nat]? I co mogłoby to w ogóle znaczyć, że typ ma jakąś
    strukturę? Nie wszystkie typy są przecież induktywne, a zatem
    nie wszystkie mają konstruktory.

    Dla dowolnego typu [X] za jego strukturę będziemy uznawać jakieś
    funkcje, o których w danej chwili wygodnie nam będzie myśleć jak
    o jego strukturze.

    Dla ukonkretnienia sytuacji niech naszym [X]em będzie typ [nat].
    Czy [nat] ma strukturę typu [list nat]? Intuicyjnie mogłoby się
    wydawać, że nie, wszakże konstruktory typu [nat] wyglądają inaczej
    niż dla [list nat]. Jednak szukanymi przez nas funkcjami, które
    dadzą [nat] strukturę [list nat] nie muszą być konstruktory - mogą
    to być dowolne inne funkcje. I faktycznie, są takie:

    [0 : nat]

    [plus : nat -> nat -> nat]

*)