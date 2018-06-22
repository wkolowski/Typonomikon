(** TODO:
    - [isEmpty] od [count]a wzwyż
    - [insert] od [findIndices]: TODO: find, findLast, removeFirst,
        removeLast, findIndex
    - [snoc] od [NoDup]
    - [pmap] (sprawdź czy jest wszystko)
    - [remove] (trochę brakuje)

*)

(** Najnowszy plan refaktoringu:
    - Wstęp
    - R1: Logika konstruktywna, potem klasyczna
    - R2: Typy induktywne — enumeracje (na przykładzie dni tygodnia?).
          Podstawy obliczeń (to co obecnie jest przy opisie typu [bool]).
    - R3: Logika boolowska (dokładnie wszystko opisać i powiązać z logiką
          klasyczną) — obecne X1
    - R4: Typy induktywne — polimorfizm (na przykładzie typu [option]?)
    - R5: Równość i obliczenia (obecnie fragment R2 i część notatki)
    - R6: Typy i funkcje — podstawy teorii typów, przemycić teorię
          kategorii (obecne X4)
    - R7: Relacje — obecne X5
    - R8: Typy induktywne — konstruktory rekurencyjne.
          Arytmetyka Peano — obecne X2) 
    - R9: Listy
*)

(** Ogólne plany na rozdziały X:
    - typ [bool] (powinien być osobny rozdział). Inne:
      - boolowska logika ternarna, być może jako tour de force dla
        automatyzacji? albo test kreatywności
    - typ [option] (być może przy okazji funktory?)
    - wcisnąć tu rozdział o produktach, sumach i funkcjach?
    - arytmetyka i typ [nat]. Reszta arytmetyki:
      - liczby dodatnie (positive)
      - binarne liczby naturalne
      - liczby całkowite
      - liczby wymierne
      - systemy liczbowe
    - listy [list] i ich różne pochodne:
      - listy niepuste [nel]
      - wektory zależne [vec]
      - wektory podtypowe (jak w ssreflekcie)
    - drzewa ukorzenione:
      - binarne węzłowe [BTree]
      - binarne liściowe (wisienki)
      - ogólne węzłowe [Tree]
      - ogólne liściowe [RoseTree]
      - jakieś inne? (węzłowe niepuste)
    - algorytmy
      - drzewa wyszukiwań
      - sterty
      - sortowanie
*)

(** TODO dla R1:
    - zrefaktoryzować rozdział: opisać zarówno logikę konstruktywną jak i
      klasyczną oraz przedstawić je obie jako użyteczne
    - przenieść paradoksy na końce opisów obu logik, żeby zobrazować
      różnice między językiem naturalnym i matematycznym
    - przejrzeć zadania
*)

(** TODO dla X3:
    - dokończ [isEmpty]
    - rozwiń [bind]
    - przenieś monadowe operacje na koniec
    - dodaj operacje aplikatywne
    - dodaj operację [snoc] (być może wcale nie zrobioną za pomocą
      [app], tylko normalnie, w celu dydaktycznym)
    - opisz niestandardowe reguły indukcyjne dla list (najlepiej przed
      przed funkcją [intersperse].
    - przenieś [intersperse] na sam koniec funkcji i dorzucić jeszcze
      kilka dziwnych (z niestandardowym kształtem indukcji)
    - opisz zwijanie i rozwijanie ([fold] i [foldl])
    - opisz sumy prefiksowe ([scanr] i [scanl])
    - popracować nad [findIndices] (i to w dwóch wersjach - być może
      jest to dobry pretekst dla wprowadzenia stylu programowania z
      akumulatorem?)
    - ogarnij osobny rozdział z zadaniami dla [option].
      Stąd zadania dla [head], [last], [tail] i [init]
    - zrób osobno: funkcje na listach dla typów mających jakieś
      specjalne rzeczy (np. rozstrzygalną równość)
    - palindromy
    - permutacje
    - podlisty, podciągi
    - [AtMost]
*)

(** TODO dla R4:
    - nieopisane taktyki: [induction], [inversion], [destruct]
    - przerobić "drobne taktyki" na "taktyki do zarządzania kontekstem"
    - przenieść opis taktyki [pattern] (i odpowiadające zadanie) do
      części o taktykach dla redukcji
*)

(** * Taktyki do redukcji i obliczeń *)

(** Posłużyć się następującym systemem nazewniczo-klasyfikacyjnym.
    Dla każdej literki są trzy relacje: redukcja, ekspansja i konwersja
    (a może powinna być jeszcze redukcja w wielu krokach?).
    Bazą jest redukcja, która ma jakąś swoją definicję, pisana jest
    a -> b. Relacja ekspansji a <- b zdefiniowana jest jako b -> a, zaś
    relacja konwersji to domknięcie równoważnościowe relacji redukcji.
    W takim układzie redukcja w wielu krokach to domknięcie zwrotno-
    przechodnie relacji redukcji. Podobnie dla ekspansji w wielu krokach.

    Mamy następujące relacje redukcji:
    - alfa (zmiana nazwy jednej zmiennej związanej)
    - beta (podstawienie argumentu za parametr formalny w jednym miejscu)
    - delta (odwinięcie jednej definicji) — uwaga: to w sumie nie jest
      relacja, tylko rodzina relacji parametryzowana/indeksowana nazwami,
      które chcemy odwinąć
    - eta (?)
    - iota (wykonanie jednego dopasowania do wzorca)
    - zeta (redukcja pojedynczego [let]a)

    Odpowiadające taktyki:
    - alfa — brak (ewentualnie [change])
    - beta — [pattern] do beta ekspansji
    - delta — [unfold] (delta redukcja), [fold] (delta ekspansja)
    - eta — [extensionality]
    - iota — raczej brak (ewentualnie [change])
    - zeta — raczej brak (ewentualnie [change]) *)

(** Omówić następujące taktyki (w kolejności):
    - [pattern] (beta ekspansja)
    - [unfold], [fold] (delta redukcja/ekspansja)
    - [change] (konwertowalność)
    - [cbn]
    - [compute], [vm_compute], [native_compute]
    - [cbv], [lazy]
    - [red]
    - [simpl]
    - [hnf] *)

(** Omówić postacie normalne (o ile gdzieś można znaleźć jakiś ich opis. *)

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

(** * Metafora dla indukcji: domino *)
