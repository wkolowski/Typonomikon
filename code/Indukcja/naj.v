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
    ma ścisłej definicji - używam tego słowa, żeby ułatwić pracę twojej
    wyobraźni.

    Czym jest kształt termu? Najprościej rzecz ujmując, jest to drzewko,
    którego korzeniem jest konstrukt językowy (konstruktor, uprzednio
    zdefiniowana funkcja lub stała, dopasowanie do wzorca, [let], lub
    cokolwiek innego) użyty do stworzenia termu, a poddrzewa to argumenty
    tego konstruktu.

    Dla przykładu, termy typu [nat] mogą mieć takie kształty:
    - [0] - stała
    - [S (S (S 0))] - konstruktor
    - [plus 0 5], [mult 0 5] - uprzednio zdefiniowana funkcja
    - [if andb false false then 42 else S 42] - [if]
    - [match 0 with | 0 => 666 | S _ => 123] - dopasowanie do wzorca
    - [length [true; false]] - uprzednio zdefiniowana funkcja
    - [let x := Prop in 16] - [let]
    - ... i wiele, wiele innych!

    Istnienie tak wielu kształtów jest dość problematyczne, więc
    musimy nieco uprościć sobie życie. Po pierwsze zauważmy, że
    każdy konstrukt językowy możemy zawinąć w funkcję, a zatem
    wszystkie powyższe "kształty" sprowadzają się tak naprawdę do
    funkcji o przeciwdziedzinie [nat], zaaplikowanych do jakichś
    argumentów (np. [0] to funkcja [f : unit -> nat :=] zdefiniowana
    jako [f _ := 0], zaaplikowana do [tt : unit].

*)