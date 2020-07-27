# Plan

![Plan](plan.jpg)

## Część 0

### A: Wstęp i inne tego typu pierdoły

## Część 1: Logika, czyli dowodzenia

![Logika](logika.jpg)

### B1: Konstruktywny rachunek zdań.
- Spójniki:
  - Implikacja:
    - rozumowanie "od tyłu" - apply
    - rozumowanie "do przodu" - specialize
    - rozumowanie od tyłu jest lepsze, logika jest bezmyślna
  - Koniunkcja
  - Dysjunkcja
  - Prawda i fałsz
  - równoważność
  - negacja, silna i słaba
  - inne spójniki, np. xor. Ćwiczenie kreatywności?
- Paradoks pieniądza i kebaba
- Zadania:
  - zadania wstawić do tekstu, a na koniec dać tylko te, które łączą wiele spójników.
  - dodać zadanie dotyczące czytania twierdzeń i dowodów
  - dodać zadania dotyczące czytania formuł (precedencja etc.)
- Ściąga
  
### B2: Konstruktywny rachunek kwantyfikatorów.
- Typy i ich elementy (zestawić ze sobą P : Prop, A : Type, p : P, x : A)
- Predykaty i relacje
- Równość
- Kwantyfikatory:
  - uniwersalny
  - egzystencjalny
  - unikatowy
- Zmienne związane
- (Im)predykatywizm - krótki opis.
- Paradoks golibrody
- Zadania:
  - modelowanie różnych sytuacji za pomocą zdań i predykatów
  - rozwiązywanie zagadek logicznych
  - więcej zadań z exists
- Ściąga

### B3: Logika klasyczna
- Prawa logiki klasycznej - enumeracja, krótki opis, podział na grupy (LEM, materialna implikacja i równoważność) vs DNE vs (Peirce, consequentia mirabilis) vs kontrapozycja
- Logika klasyczna jako logika:
  - Boga (LEM) + prawo zachowania informacji
    - metoda zerojedynkowa
  - materialna
  - diabła (DNE i kontrapozycja)
  - cudownych konsekwencji, Peirce'a
Paradoks pijoka
Paradoks Curry'ego
(Paradoksy implikacji materialnej?)
Zadania:
  - udowodnij równoważność praw każde z każdym
  - wyrzucić zadania mącące (mieszające typy i zdania)
- Ściąga

### B4: Inne logiki
- Porównanie logiki konstruktywnej i klasycznej
- Inne logiki:
  - {sub, super}-intuicjonistyczne
  - modalne
  - substrukturalne
  - wielowartościowe
  - logika szalonego Gruzina
- Logika de Morgana jako coś pomiędzy logiką konstruktywną i klasyczną
- Logika modalna
- Pluralizm logiczny
- Aksjomaty w stylu ProofIrrelevance, UIP, K, PropExt
- Kodowanie impredykatywne
- Kombinatory taktyk
- Zadania:
  - rozwiąż wszystkie zadania jeszcze raz, ale tym razem bez używania Module/Section/Hypothesis oraz z jak najkrótszymi dowodami
- Jakieś podsumowanie
- Taktyka firstorder
- Zrobić test tak/nie.
- Zrobić fiszki do nauki nazw praw.

## Część 2: teoria typów, czyli programowanie

### C: Podstawy teorii typów:
- Przedstawić logikę za pomocą dedukcji naturalnej
- Curry-Howard
- Jeszcze raz logika, ale tym razem z prooftermami
- Omówić obliczenia i postacie normalne (o ile gdzieś można znaleźć jakiś ich opis).
- Pięć rodzajów reguł
- HoTT-bookowa teoria typów: pusty, unit, bool, nat, produkt, suma, funkcje, produkt zależny, suma zależna, uniwersa, równość
- Ale nie można zaniedbać formalnej prezentacji teorii typów.
- Wprowadzić tutaj nazwę "motyw eliminacji"

### D: Indukcja

![Indukcja](indukcja.jpg)
![Rekursja](rekursja.jpg)

### D1: Typy induktywne
- Enumeracje, czyli sumy nazwane.
  - Kontent: ewaluacja (to co obecnie jest przy opisie typu `bool`). Przykładowe typy: kierunki, kolory RGB, dni tygodnia, uprawnienia dostępu (R, W, RW, etc.), pusty, unit
  - Ćwiczenia: logika boolowska. Dokładnie wszystko opisać i powiązać z logiką klasyczną
- Parametry.
  - Kontent: polimorfizm. Przykładowe typy: prod, sum.
  - Ćwiczenia: typ option.
- Konstruktory rekurencyjne.
  - Kontent: rekursja. Przykładowe typy: nat
  - Ćwiczenia: arytmetyka Peano.
- Indukcja wzajemna.
- Indeksy, czyli predykaty i relacje
- Indeksy v2, czyli typy danych ostro chwycone za mordę.
- Indukcja-rekursja.
- Indukcja-indukcja.
- Indukcja-indukcja-rekursja.
- Zadania z definiowania induktywnych typów i predykatów
- W międzyczasie: omówić ścisłą pozytywność
- Dodać podrozdział o typach induktywnych z nieskończoną ilością argumentów indukcyjnych (A -> T)

### D2: Definiowanie funkcji
- Rekursja:
  - "prymitywna" (jak w Agdzie)
  - strukturalna
  - polimorficzna
  - "monotoniczna" (fix w fiksie)
  - paliwowa
  - dobrze ufundowana
- metoda Bove-Capretta
- metoda Bove-Capretta z indeksowaną indukcją-rekursją
- Dziwniejsze:
  - rekursja przez iterację
  - rekursja wydmuszkowa (Coq'Art)
  - teoria dziedzin (computation, CPDT)
  - comp (CPDT)
  - koindukcja (thunk, CPDT)

### D4: Arytmetyka Peano

### D5: Listy
- ogólnie trzeba będzie zrobić gruntowny refaktoring list według planu zawartego w List_sig.v
- opisz niestandardowe reguły indukcyjne dla list (najlepiej przed funkcją `intersperse`)
- przenieś `intersperse` na sam koniec funkcji i dorzuć jeszcze kilka dziwnych (z niestandardowym kształtem indukcji)
- opisz zwijanie i rozwijanie (`fold` i `foldl`)
- opisz sumy prefiksowe (`scanr` i `scanl`)
- zrób osobno: funkcje na listach dla typów mających jakieś specjalne rzeczy (np. rozstrzygalną równość)
- Opisać relacje prefix/infix/suffix/interfix dla list jako jakotakie ćwiczenie
- niedokończone funkcje (do niedawna oznaczone jako TODO):
  - isZero (przenieść do rozdziału o arytmetyce)
  - isEmpty
  - snoc
  - bind
  - iterate (od removeFirst wzwyż) i iter (join, bind)
  - insert (join, bind, iterate, init)
  - remove
  - take (join, bind, last_take, take_remove),
  - drop (join, bind, remove)
  - removeFirst (removeFirst_zip)
  - findIndex (init, tail)
  - filter (tail, init)
  - findIndices (join, bind, takeWhile, dropWhile)
  - pmap (iterate, nth, last, tail i init, take i drop, takedrop, zip, unzip, zipWith, unzipWith, removeFirst i removeLast, findIndex, findIndices)
  - intersperse (init, insert, remove, drop, zip, zipWith, unzip)
  - groupBy
  - Rep (join, nth)
  - AtLeast (nth, head, last, init, tail)
  - Exactly (join, nth, head, tail, init, last, zip)
  - AtMost
  - popracować nad `findIndices` (i to w dwóch wersjach - być może jest to dobry pretekst dla wprowadzenia stylu programowania z akumulatorem?)
  - Najnowsze: ćwiczenia z przetwarzania danych, typu "znajdź wszystkie liczby nieparzyste większe od x, których suma cyfr to dupa konia".

### D6: Więcej list
- Alternatywne definicje predykatów i relacji
- Rozstrzyganie predykatów i relacji
- Generowanie różnych rodzajów (pod)struktur typu prefiksy, podciągi etc.
- Wszystko o permutacjach

D7: Ogólne plany na rozdziały X:
- boolowska logika ternarna, być może jako tour de force dla automatyzacji? albo test kreatywności
- typ option (być może przy okazji funktory?) Stąd zadania dla `head`, `last`, `tail` i `init`
- wcisnąć tu rozdział o produktach, sumach i funkcjach?
- arytmetyka i typ `nat`. Reszta arytmetyki:
  liczby dodatnie (positive)
  binarne liczby naturalne
  liczby całkowite
  liczby wymierne
  systemy liczbowe
- `list`y i ich różne pochodne:
  - listy niepuste `nel`
  - wektory zależne `vec`
  - wektory podtypowe (jak w ssreflekcie)
- drzewa ukorzenione:
  - binarne węzłowe `BTree`
  - binarne liściowe (wisienki)
  - ogólne węzłowe `Tree`
  - ogólne liściowe `RoseTree`
  - jakieś inne? (węzłowe niepuste)

### E1: Rekordy, klasy i moduły
- Typy skończone
- Enumerowanie
- Rozstrzygalność i typ `reflect`
- Rozstrzygalna równość
- Rodzaje rekordów: induktywne, koinduktywne, primitive projections
- Silne specyfikacje

### E2: Typy i funkcje
- Aksjomat ekstensjonalności
- Lewa i prawa skracalność
- Lewa i prawa odwrotność
- Izomorfizm
- Injekcja, bijekcja, surjekcja
- Zanurzenia, pokrycia, HoTTowe rzeczy
- Inwolucja i idempotencja
- Przemycać jak najwięcej teorii kategorii

### E3: Typy i relacje
- Odnośnie mechanizmu redukcji:
  - Posłużyć się następującym systemem nazewniczo-klasyfikacyjnym.
  - Dla każdej literki są trzy relacje: redukcja, ekspansja i konwersja (a może powinna być jeszcze redukcja w wielu krokach?).
  - Bazą jest redukcja, która ma jakąś swoją definicję, pisana jest a -> b. Relacja ekspansji a <- b zdefiniowana jest jako b -> a, zaś relacja konwersji to domknięcie równoważnościowe relacji redukcji.
  - W takim układzie redukcja w wielu krokach to domknięcie zwrotno-przechodnie relacji redukcji. Podobnie dla ekspansji w wielu krokach.
- Podsumowując: zdefiniować na relacjach rzeczy, których można by użyć przy formalizacji teorii typów, ale tylko w celu objaśnienia.

### E4: Nowy rozdział o logice boolowskiej
- Tabelki prawdy (definicje) + twierdzenia jako powtórka logiki klasycznej.
- Rozstrzygalność:
  - Co to.
  - Techniczne aspekty.
  - Kiedy nie rozstrzygać (protip: kiedy można niskim kosztem rozstrzygnąć coś bardziej informatywnego).
  - Reflect, BoolSpec, CompareSpec etc.
  - Uwaga: w sumie to taki typ sumor jest dla opcji czymś analogicznym jak BoolSpec dla typu bool.
- Reflekcja małoskalowa.
- Napisać podrozdział poświęcony temu, czy definiować predykaty (i rodziny typów) przez rekursję czy przez indukcję. Użyć jako przykładu takich predykatów jak `elem`, `Exists`, `Forall`, `Exactly`. Jak to się ma do rozstrzygalności.
- Aksjomaty dotyczące sortu `Prop` i jak obejść się bez nich.
- Metoda encode-decode, początkowo jako narzędzie do rozwiązywania problemów, których normalni ludzie nie mają i nigdy mieć nie będą. Potem: izomorfizmy typów.
- Sort `SProp`.

### F: Koindukcja
- F1: Typy koinduktywne - rekordy, parametry i korekursja
- F2: liczby konaturalne
- F3: strumienie
- F4: kolisty
- F5: kodrzewa

### G: Sorty, uniwersa (kodów) i generyczność
- Relewancja: `Prop`, `SProp`
- Programowanie generyczne za pomocą uniwersów
- Jedyny pierścień wyższego rzędu, czyli W-typy i M-typy
- Jedyny pierścień pierwszego rzędu, czyli uniwersa kodów na typy induktywne i koinduktywne
- Uwaga: wyższy rząd vs pierwszy rząd

### H: Ścieżki
- Interpretacja homotopiczna: dowody równości a ścieżki
- Opowiedzieć skąd się biorą ścieżki
- Ścieżki w banalnych typach
- Ścieżki między sumami
- Ścieżki między parami
- Ścieżki między elementami typów induktywnych
- Ścieżki między elementami typów koinduktywnych
- Ścieżki między funkcjami
- Ścieżki między zdaniami - `PropExt`
- Ścieżki między typami - uniwalencja
- Proof Irrelevance
- Aksjomat K
- Aksjomat Uniwalencji
- Wyższe typy induktywne

## Cześć 3: Metapoziom, czyli taktyki

I1: Ltac
  - być może przenieść tu z rozdziału 1 fragment o kombinatorach taktyk
  - `Ltac` się zestarzał, opisać `Ltac2`

I2: Spis taktyk
  - nieopisane taktyki: `induction`, `inversion`, `destruct`
  - przerobić "drobne taktyki" na "taktyki do zarządzania kontekstem"
  - przenieść opis taktyki `pattern` (i odpowiadające zadanie) do części o taktykach dla redukcji
  - Taktyki dla redukcji i obliczeń: Mamy następujące redukcje:
    - alfa (zmiana nazwy jednej zmiennej związanej)
    - beta (podstawienie argumentu za parametr formalny w jednym miejscu)
    - delta (odwinięcie jednej definicji) — uwaga: to w sumie nie jest
      relacja, tylko rodzina relacji parametryzowana/indeksowana nazwami,
      które chcemy odwinąć
    - eta - unikalność dla funkcji, rekordów etc.
    - iota (wykonanie jednego dopasowania do wzorca)
    - zeta (redukcja pojedynczego `let`a)
  - Odpowiadające taktyki:
    - alfa — brak
    - beta — cbn/cbv beta
    - delta — cbn/cbv delta, unfold, fold
    - eta — brak
    - iota — cbn/cbv iota
    - zeta — cbn/cbv zeta
    - ogólna redukcja: cbn, cbv, simpl
    - konwersja: change
  - Omówić następujące taktyki (w kolejności):
    - `pattern` (beta ekspansja)
    - `unfold`, `fold` (delta redukcja/ekspansja)
    - `change` (konwertowalność)
    - `cbn`
    - `compute`, `vm_compute`, `native_compute`
    - `cbv`, `lazy`
    - `red`
    - `simpl`
    - `hnf`

I3: Reflekcja, metapoziom, quote (którego oczywiście w Coqu nie ma, a jak) i inne takie duperele
  - Z cyklu "panie, a na co to komu?": po co prostemu chłopu reflekcja?
  - Semantyka vs składnia

## Część 4: Efekty obliczeniowe dla biedaków

X1: Monady i efekty jako sposoby bycia
- `Id` nie reprezentuje żadnego efektu. Wartości typu `Id A` są w ten
  sposób, że po prostu są.
- `option` reprezentuje częściowość. Wartości typu `option A` są w ten
  sposób, że albo są, albo ich nie ma
- `sum E` reprezentuje możliwość wystąpienia błędu. Wartości typu
  `sum E A` są w ten sposób, że albo są poprawne, albo ich nie ma, gdyż
  wystąpił błąd typu `E`.
- `list` reprezentuje niedeterminizm (uporządkowany). Wartości typu
  `list A` są w ten sposób, że może ich być wiele lub może ich nie być
  wcale i są w sposób uporządkowany.
- `State S` reprezentuje stan. Wartości typu `State S A` są w ten
  sposób, że są i mają pamięć, tzn. mogą się zmieniać w zależności
  od stanu.
- `Reader R` reprezentuje możliwość odczytania konfiguracji.
- `Writer W` reprezentuje możliwość zapisywania logów.
- `Future` reprezentuję asynchroniczność. Wartości typu `Future A`
  są w ten sposób, że albo są teraz, albo będą później.
- `STM` reprezentuje transakcje. Wartościu typu `STM A` są w ten
  sposób, że są w jednym kawałku, są transakcjami.
- `SQL` reprezentuje operacje bazodanowe. Wartości typu `SQL A` są
  w ten sposób, że albo po prostu są, albo są w bazie danych.

### N: Kontynuacje
- Kodowanie Churcha
- Kodowanie Scotta
- Listy różnicowe
- nawiązać do rekursji ogonowej

## Część 5: Funkcyjna algorytmika

Z: Złożoność
  - Napisać coś o rekursji ogonowej i opisać poświęcone jej techniki dowodzenia.

Ź: Algorytmy i struktury danych:
  - sortowanie
  - drzewa wyszukiwań
  - sterty

## Część 6: Podstawy matematyki

### xD_omega: Matematyka
- O typach ilorazowych
- Setoidy
- Monoidy i teoria grup
- Teoria porządków, krat i innych takich
- konstruktywna topologia dla bidoków
- Teoria Kategorii