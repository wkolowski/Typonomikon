# TODO

Nie zapomnieć o genialnych pomysłach:
1. Tautologie na kodowaniach impredylatywmych jako ćwiczenia z funkcji anonimowych
2. Maszyny stanowe i type-driven design jako ćwiczenia do (indeksowanych) enumeracji.

## Podstawy
1. Od początku użyć nominalizmów do wytłumaczenia na czym polega wiązanie nazw zmiennych.

## Rekursja
0. Rekursja zagnieżdżona, zarówno w sensie zagnieżdżonych wywołań rekurencyjnych, jak i dopasowania wyniku wywołania rekurencyjnego do wzorca.
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
8. Odkłamać kwestię "skończoności" typów induktywnych i "nieskończoności" typów koinduktywnych. Tak naprawdę, to chodzi o to, że typy induktywny są dobrze ufundowane, a typy koinduktywne niekoniecznie.
9. Paradoks sterty.
10. Paradoks "wszystkie konie sa tego samego koloru".
11. Paradoks najmniejszej interesującej liczby.

## Indukcja - teoria
1. Kwestia non-uniform parameters i jak je zasymulować przy użyciu indeksów.
2. Typy induktywne z parametrami + równość = rodziny indeksowane.

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
1. Mega ważna obserwacja: nazwy zawsze należy nadawać tak, żeby zgadzały się z definicją, czyli nazwy są intensjonalne. Ewentualne ekstensjonalne powiązanie ze sobą (w postaci równoważności) różnych apriori nazw następować musi później, na mocy pokazania równoważności tego, co one oznaczają. Przykład: różne definicje równoważności powinny się nazywać inaczej, np. invertible, biinvertible, contractible etc.
2. Reifikacja:
  - Reifikacja jest wtedy, kiedy jakieś zewnętrzne idee zostają elementami pewnego typu.
  - Wobec tego reguły teorii typów to nic innego jak reifikacja różnych pojęć.
  - Uniwersum jako reifikacja pojęcia typu.
  - I tak dalej.

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
4. Co do stylu, to tu jest [Haskell style guide](https://kowainik.github.io/posts/2019-02-06-style-guide)
5. W nawiązaniu do powyższego: opisać bardziej rzeczy do strukturyzowania dowodów, np. `{ }` albo bullet pointy `*`, `+` i `-`

## Zagubione notatki
1. Let `I := U × U`, and let `A : I → U` be defined by `A(X, Y) := (X → Y) × (Y → X)`. Define `B` as `B(X, Y )(f, g) := X × Y` and `r(X, Y )(f, g)(x, y) := (f(x) = y) × (x = g(y))`. Then the associated M-type is a family `M : I → U` and `M(A, B)` is equivalent to `A \equiv B`.
2. DNE holds if and only if every proposition is logically equivalent to the negation of some type.
3. Spróbować dodać minirozdział poświęcony logicznym aspektom racjonalności (tak jak w książe: Keith Stanovich, The Rationality Quotient).
4. Paradoks zwrotności. Są 2 rodzaje ludzi:
  - Ci, którzy uważają, że są dwa rodzaje ludzi.
  - Ci, którzy są innego zdania.