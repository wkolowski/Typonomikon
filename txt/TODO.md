# TODO

## Rekursja
1. Prymitywna.
2. Wyższego rzędu, tzn. nie w pełni zaaplikowane wywołania rekurencyjne.
3. Przez iterację.
4. Koindukcjowa.

## Indukcja - podstawy
0. Opisać alternatywne składnie na typy induktywne (czyli te, w których nie trzeba aż tak dużo pisać).
1. Powyższe jest mądrym heurystycznym sposobem rozróżniania różnych poziomów zaawansowania typów induktywnych (rodzin induktywnych nie można definiować bez podawania indeksów w przeciwdziedzinie).
2. W nowym ujęciu podrozdział o regułach indukcyjnych ma być ściśle powiązany z wprowadzeniem rekursji strukturalnej (tzn. nie-prymitywnej).
3. Argumenty indukcyjne pierwszego i wyższego rzędu.
4. Indeksowane rodziny induktywne to wystarczająco dla początkujących. Przesunąć rozdziały o indukcji-indukcji/indukcji-rekursji (i wszystkim, czego explicite nie ma w Coqu) dalej.
5. Alternatywna nazwa na injektywność konstruktorów to niekonfuzja (`NoConfusion`), zaś nazwa na nierówności `t <> c t` to acykliczność.
6. Ćwiczenia:
- Z przetwarzania danych, typu "znajdź wszystkie liczby nieparzyste większe od x, których suma cyfr to dupa konia".
- Z definiowania typów induktywnych (i relacji też).
- Z uogólniania hipotezy indukcyjnej (+ akumulatory i rekursja ogonowa).
7. Opisać zippery (z dwóch perspektyw: łażenie po drzewach i różniczkowanie typów) oraz indeksowanie poddrzew dla typów induktywnych (czyli też, w jakiejś formie, zippery).
8. Odkłamać kwestię "skończoności" typów induktywnych i "nieskończoności" typów koinduktywnych. Tak naprawdę, to chodzi o to, że typy induktywny są dobrze ufundowane, a typy koinduktywne niekoniecznie.

## Indukcja - teoria
1. Kwestia non-uniform parameters i jak je zasymulować przy użyciu indeksów.
2. Typy induktywne z parametrami + równość = rodziny indeksowane.
3. Izomorfizmy dla typów induktywnych: każde drzewo jest drzewem o jakiejś wysokości (no chyba że ma nieskończone rozgałęzienie, to wtedy nie). Uogólniając: każdy element typu induktywnego jest elementem odpowiadającego mu typu indeksowanego o pewnym indeksie. UWAGA: rozróżnienie na drzewa o skończonej wysokości vs drzewa o ograniczonej wysokości.

## HoTT i topologia
2. Wprowadzić teorię zbiorów za pomocą wyższego typu induktywnego.
3. `B : A -> U` jest uniwalentne, gdy dla `x, y : A` jest `(x = y) = (B x = B y)` / https://vimeo.com/338899939
4. Homotopy pullback https://vimeo.com/337960032
6. Najogólniejszym nierekurencyjnym HITem jest pushout.
7. Awodey twierdzi, że uniwalencja ma coś wspólnego z Fregiem i tym, że konwertowalność - ta sama nazwa, ścieżki - to samo znaczenie.
8. Transport wzdłuż ścieżki dla rodzin typów to uogólnienie indiscernability of identicals Leibniza (patrz punkt 3).
9. Podkreślić rozróżnienie między właścwiwością i strukturą, `Prop` i `Type`, surjekcją i postodwracalnością, etc.
10. Ciekawe: z uniwalencją można pokazać, że `(A -> Prop) = {X : Type & {f : X -> A | isEmbedding f}}`, czyli że predykaty na `A` to podtypy `A`.
11. Delikatna kwestia równoważności. Przytoczyć jak najwięcej definicji:
  - biinvertible
  - bijekcjową
  - relacjową
  - half-adjoint equivalence może być zbyt skomplikowany
  - są jeszcze jakieś, ale nie 
12. Włączyć potem do książki rzeczy z HoTTowych notatek.
13. Przestrzeń metryczną można zdefiniować za pomocą "Ball Relation": `Q+ -> X -> X -> Prop`

## Filozofia
1. Mega ważna obserwacja: nazwy zawsze należy nadawać tak, żeby zgadzały się z definicją, czyli nazwy są intensjonalne. Ewentualne ekstensjonalne powiązanie ze sobą (w postaci równoważności) różnych apriori nazw następować musi później, na mocy pokazania równoważności tego, co one oznaczają. Przykład: różne definicje równoważności powinny się nazywać inaczej, np. invertible, biinvertible, contractible etc.

## Sugestie i problemy z koła
1. Opisać dokładniej definiowanie przez dowód.
2. Nie trzeba specjalizować hipotezy, żeby przepisać.
4. Napisać bardziej wprost o deklarowaniu hipotez.
6. Ludzie po czasie zapominają składni.
7. Napisać coś więcej o składni i o rysowaniu termów.

## Długofalowe
1. Użyć jsCoq do zrobienia interaktywnej książki, która wyglądałaby jakoś tak: https://x80.org/rhino-coq/v8.10/
2. Zrobić zwijane/rozwijane dowody i paragrafy.
3. Dodać rozdział o stylu, wcięciach, komentowaniu etc. Patrz tu: https://www.cs.princeton.edu/courses/archive/fall19/cos326/style.php#1
4. W nawiązaniu do powyższego: opisać bardziej rzeczy do strukturyzowania dowodów, np. `{ }` albo bullet pointy `*`, `+` i `-`