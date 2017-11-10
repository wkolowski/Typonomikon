(** * Metafora dla rekursji/indukcji dobrze ufundowanej *)

Require Import Recdef.

Check well_founded_ind.

(** Wyobraźmy sobie drabinę. Czy zerowy szczebel drabiny jest dostępny?
    Aby tak było, każdy szczebel poniżej niego musi być dostępny. Weźmy
    więc dowolny szczebel poniżej zerowego. Jednakże takie szczeble nie
    istnieją, a zatem zerowy szczebel jest dostępny.

    Czy pierwszy szczebel jest dostępny? Aby tak było, dostępne muszą
    być wszystkie szczeble poniżej niego, a więc także zerowy, o którym
    już wiemy, że jest dostępny. Tak więc pierwszy szczebel też jest
    dostępny.

    A czy szczebel 2 jest dostępny? Tak, bo szczeble 0 i 1 są dostępne.
    A szczebel 3? Tak, bo 0, 1 i 2 są dostępne. Myślę, że widzisz już,
    dokąd to zmierza: każdy szczebel tej drabiny jest dostępny.

    Możemy tę dostępność zinterpretować na dwa sposoby. Z jednej strony,
    jesteśmy w stanie wspiąć się na dowolne wysoki szczebel. Z drugiej
    strony, nieważne jak wysoko jesteśmy, zawsze będziemy w stanie zejść
    na ziemię w skończonej liczbie kroków.

    Powyższy przykład pokazuje nam, że relacja [<] jest dobrze ufundowana.
    A co z relacją [<=]?

    Czy 0 jest dostępne? Jest tak, jeżeli wszystkie n <= 0 są dostępne.
    Jest jedna taka liczba: 0. Tak więc 0 jest dostępne pod warunkiem,
    że 0 jest dostępne. Jak widać, wpadliśmy w błędne koło. Jaest tak,
    bo w relacji [<=] jest nieskończony łańcuch malejący, mianowicie
    [0 <= 0 <= 0 <= 0 <= ...].

    Alternatywna charakteryzacja dobrego ufundowania głosi, że relacja
    dobrze ufundowana to taka, w której nie ma nieskończonych łańcuchów
    malejących. Relacja [<=] nie spełnia tego warunku, nie jest więc
    relacją dobrze ufundowaną.

    Nasza dobrze ufundowana drabina nie musi być jednak pionowa — mogą
    być w niej rozgałęzienia. Żeby to sobie uświadomić, rozważmy taki
    porządek: x y : Z i x < y := |x| < |y|. *)

(** * Metafora dla monad *)

(** Monady jako sposoby bycia:
    - [Id] nie reprezentuje żadnego efektu. Wartości typu [Id A] są w ten
      sposób, że po prostu są.
    - [option] reprezentuje częściowość. Wartości typu [option A] są w ten
      sposób, że albo są, albo ich nie ma
    - [sum E] reprezentuje możliwość wystąpienia błędu. Wartości typu
      [sum E A] są w ten sposób, że albo są poprawne, albo ich nie ma, gdyż
      wystąpił błąd typu [E].
    - [list] reprezentuje niedeterminizm (uporządkowany). Wartości typu
      [list A] są w ten sposób, że może ich być wiele lub może ich nie być
      wcale i są w sposób uporządkowany.
    - [State S] reprezentuje stan. Wartości typu [State S A] są w ten
      sposób, że są i mają pamięć, tzn. mogą się zmieniać w zależności
      od stanu.
    - [Reader R] reprezentuje możliwość odczytania konfiguracji.
    - [Writer W] reprezentuje możliwość zapisywania logów.
    - [Future] reprezentuję asynchroniczność. Wartości typu [Future A]
      są w ten sposób, że albo są teraz, albo będą później.
    - [STM] reprezentuje tranzakcje. Wartościu typu [STM A] są w ten
      sposób, że są w jednym kawałku, są transakcjami.
    - [SQL] reprezentuje operacje bazodanowe. Wartości typu [SQL A] są
      w ten sposób, że albo po prostu są, albo są w bazie danych. *)