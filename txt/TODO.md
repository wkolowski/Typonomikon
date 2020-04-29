# TODO

## Długofalowe
1. Użyć jsCoq do zrobienia interaktywnej książki, która wyglądałaby jakoś tak: https://x80.org/rhino-coq/v8.10/
2. Zrobić zwijane/rozwijane dowody i paragrafy.
3. Dodać rozdział o stylu, wcięciach, komentowaniu etc. Patrz tu: https://www.cs.princeton.edu/courses/archive/fall19/cos326/style.php#1

## Rekursja
1. Prymitywna.
2. Wyższego rzędu, tzn. nie w pełni zaaplikowane wywołania rekurencyjne.
3. Przez iterację.
4. Koindukcjowa.

## Indukcja
1. W nowym ujęciu podrozdział o regułach indukcyjnych ma być ściśle powiązany z wprowadzeniem rekursji strukturalnej (tzn. nie-prymitywnej).
2. Argumenty indukcyjne pierwszego i wyższego rzędu.
4. Opisać zippery (czyli różniczkowanie typów).
5. Ćwiczenia:
5.1. Z przetwarzania danych, typu "znajdź wszystkie liczby nieparzyste większe od x, których suma cyfr to dupa konia".
5.2. Z definiowania typów induktywnych (i relacji też). W tym takie:
5.3. Z uogólniania hipotezy indukcyjnej (+ akumulatory i rekursja ogonowa).
6. Indeksowane rodziny induktywne to wystarczająco dla początkujących. Przesunąć rozdziały o indukcji-indukcji/indukcji-rekursji (i wszystkim, czego explicite nie ma w Coqu) dalej.
7. Kwestia non-uniform parametrs i jak je zasymulować przy użyciu indeksów.
8. Typy induktywne z parametrami + równość = rodziny indeksowane.
9. Najogólniejszym nierekurencyjnym HITem jest pushout.

## Listy
1. Opisać na przykładzie list różnice między teorią typów, a hardkorową matematyką konstruktywną opartą na relacjach separacji (apartness).
2. Dokończyć prace nad funkcjami znajdującymi wszystkie struktury danego rodzaju (permutacje, cykle, podciągi, palindromy etc.).
3. Dokończyć prace nad różnymi alternatywnymi definicjami permutacji.
5. Dokończyć prace nad resztą rzeczy z folderu List/.

## Funkcje
1. Dokończyć podrozdział o odwrotnościach i izomorfizmach.
2. Napisać coś o (pre/post)skracalności.

## Inne
3. Znaleźć prostszy przykład dla podrozdziału o ścisłej pozytywności (ale do której konkretnie części?).
9. Izomorfizmy dla typów induktywnych: każde drzewo jest drzewem o jakiejś wysokości. Uogólniając: każdy element typu induktywnego jest elementem odpowiadającego my typu indeksowanego o pewnym indeksie.
14. Opisać taktyki dla redukcji i obliczeń.
15. Opisać podstawy teorii typów.
17. Opisać zmienne egzystencjalne i odpowiadające im taktyki.
18. Opisać taktyki do radzenia sobie z typami zależnymi.
19. Opisać: silnia, współczynniki dwumianowe, sumy szeregów, charakteryzowanie wzorów rekurencyjnych.
26. Odkłamać kwestię polimorfizmu najlepiej przy okazji rozdziału o programowaniu generycznym.
26ipół. Kwestia parametryczności: lam X. lam nil. lam cons. cons X nil - egzotyczna lista
27. Twierdzenie: można zanurzyć liczby naturalne w liczby konaturalne, ale nie można tego zanurzenia odwrócić.
28. Kodowanie Churcha dla typów ilorazowych.
29. Wprowadzić teorię zbiorów za pomocą wyższego typu induktywnego.
30. Być może dokonać rozróżnienia różnych _ex quodlibet_:
- _Ex falso quodlibet_ - `False -> P`
- _Ex contradictione quodlibet_ - `A /\ ~ A -> P`
31. HoTTowe notatki:
- `B : A -> U` jest uniwalentne, gdy dla `x, y : A` jest `(x = y) = (B x = B y)` / https://vimeo.com/338899939
- Homotopy pullback https://vimeo.com/337960032
32. Podkreślić gdzieś mocniej, że reguła indukcji mówi, że nie ma nic poza tym, co można zrobić konstruktorami.

## Sugestie i problemy z koła:
1. Opisać dokładniej definiowanie przez dowód.
2. Nie trzeba specjalizować hipotezy, żeby przepisać.
3. Być może coś więcej o równości (i jej alternatywnej definicji?).
4. Napisać bardziej wprost o deklarowaniu hipotez.
5. Ulepszyć ściągę z taktykami i komendami.
6. Ludzie po czasie zapominają składni.
7. Napisać coś więcej o składni i o rysowaniu termów.
8. Dodać zadanie z dwiema dziwnymi identycznościami (co najmniej intensjonalna i ekstensjonalna, ale nie pamiętam, o co dokładnie chodzi).