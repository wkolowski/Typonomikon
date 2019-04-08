(** Sugestie i problemy z koła:
    - nie trzeba specjalizować hipotezy, żeby przepisać
    - być może coś więcej o równości (i jej alternatywnej definicji?)
    - napisać bardziej wprost o deklarowaniu hipotez
    - ulepszyć ściągę z taktykami i komendami
*)

(** Najnowsze TODO:
    - Wydzielić z R2 nowy rozdział o rekordach, klasach i połączyć to z
      rozstrzygalnością oraz typem [reflect]
    - Przemieścić z R2 podrozdziały o sortach i o hierarchii uniwersów.
    - Przemieścić z R1 podrozdziały "Typy i termy" oraz "Typy a zbiory".
    - Dodać podrozdział o typach skończonych.
    - Napisać coś o kodowaniu Churcha.
    - Napisać coś o rekursji ogonowej i opisać poświęcone jej techniki
      dowodzenia.
    - Rozbudować opis równości i konwertowalności o dokładne opisy ewaluacji
      i taktyk typu cbn/cbv etc.
    - Opisać relacje prefix/infix/suffix/interfix dla list jako jakotakie
      ćwiczenie
    - Pięć sposobów na ogólną rekursję w Coqu: rekursja dobrze ufundowana,
      rekursja po paliwie, rekursja wydmuszkowa (Coq'Art), teoria dziedzin
      (computation, CPDT), comp (CPDT), koindukcja (thunk, CPDT). 
*)

(** TODO:
    - ogólnie trzeba będzie zrobić gruntowny refaktoring list według
      planu zawartego w List_sig.v
    - niedokończone funkcje (do niedawna oznaczone jako TODO):
      - isZero (przenieść do rozdziału o arytmetyce)
      - isEmpty
      - snoc
      - bind
      - iterate i iter (join, bind)
      - insert (join, bind, iterate, init)
      - remove
      - take (join, bind, last_take, take_remove),
      - drop (join, bind, remove)
      - iterate (od removeFirst wzwyż)
      - removeFirst (removeFirst_zip)
      - findIndex (init, tail)
      - filter (tail, init)
      - findIndices (join, bind, takeWhile, dropWhile)
      - pmap (iterate, nth, last, tail i init, take i drop, takedrop, zip,
          unzip, zipWith, unzipWith, removeFirst i removeLast, findIndex,
          findIndices)
      - intersperse (init, insert, remove, drop, zip, zipWith, unzip)
      - groupBy
      - Rep (join, nth)
      - AtLeast (nth, head, last, init, tail)
      - Exactly (join, nth, head, tail, init, last, zip)
      - AtMost
    - napisać wstępy do poszczególnych funkcji
*)

(** Najnowszy plan refaktoringu:
    - Wstęp
    - R1: Logika konstruktywna, potem klasyczna. Zrobić tak żeby można było
          pisać "Classically $ coś tam". Na końcu dać podrozdział o
          kombinatorach taktyk.
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
    - zrefaktoryzować rozdział:
      - opisać najpierw logikę konstruktywną, a potem klasyczną
      - przedstawić obie jako użyteczne
      - na końcu każdego z opisów dać paradoksy, żeby zobrazować
        różnice między językiem naturalnym i matematycznym
    - przejrzeć zadania:
      - wyrzucić zadania mącące (mieszające typy i zdania)
      - dodać zadanie dotyczące czytania twierdzeń i dowodów
      - dodać zadania dotyczące czytania formuł (precedencja etc.)
    - dokończyć ściągę i dać na koniec
    - być może podzielić rozdział na kilka
    - potencjalnie pozbyć się sekcji
    - dodać jakieś wyjaśnienia do ćwiczeń
    - więcej zadań z exists
    - zadania z klasycznego rachunku kwantyfikatorów
    - napisać coś o nazwach zmiennych związanych
*)

(** TODO dla X3:
    - dokończ [isEmpty]
    - opisz niestandardowe reguły indukcyjne dla list (najlepiej przed
      przed funkcją [intersperse]).
    - przenieś [intersperse] na sam koniec funkcji i dorzuć jeszcze
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

(** Omówić postacie normalne (o ile gdzieś można znaleźć jakiś ich opis).
    Ogólniej: wstawić jakąś zajawkę wcześnie i bardziej szczegółow opis
    po rozdziale o relacjach. Trzeba by też opisać rachunek lambda. *)

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
    - [STM] reprezentuje transakcje. Wartościu typu [STM A] są w ten
      sposób, że są w jednym kawałku, są transakcjami.
    - [SQL] reprezentuje operacje bazodanowe. Wartości typu [SQL A] są
      w ten sposób, że albo po prostu są, albo są w bazie danych. *)