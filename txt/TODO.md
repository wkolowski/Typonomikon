# TODO

## Logika
1. Opisy spójników podzielić ze względu na reguły (wprowadzania, eliminacji, formowania jako wstęp).
2. Po każdej regule proste ćwiczenia.
3. Wspomnieć o autoreferencji od razu na samym początku: paradoks Curry'ego, potem golibrody, w międzyczasie heterologiczność.
4. Opisać rozróżnienie esencjalizm (domyślny) vs strukturalizm ("Yoneda perspective", np. zdanie to kolekcja wszystkich swoich dowodów, impredykatywne definicje spójników, etc.).
5. Bonusowe paradoksy do pamiętania:
- Hilbert-Bernays: https://en.wikipedia.org/wiki/Hilbert%E2%80%93Bernays_paradox
- Barbershop: https://en.wikipedia.org/wiki/Barbershop_paradox
- paradoks kłamcy

## Indukcja
2. W nowym ujęciu podrozdział o regułach indukcyjnych ma być ściśle powiązany z wprowadzeniem rekursji strukturalnej (tzn. nie-prymitywnej).
3. Argumenty indukcyjne pierwszego i wyższego rzędu.
5. Alternatywna nazwa na injektywność konstruktorów to niekonfuzja (`NoConfusion`), zaś nazwa na nierówności `t <> c t` to acykliczność.
6. Ćwiczenia:
- Z przetwarzania danych, typu "znajdź wszystkie liczby nieparzyste większe od x, których suma cyfr to dupa konia".
- Z definiowania typów induktywnych (i relacji też).
- Z uogólniania hipotezy indukcyjnej (+ akumulatory i rekursja ogonowa).
- Ogólnie z myślenia induktywnego. Ciekawy typ ćwiczeniowy: listy o parzystej długości.
8. Odkłamać kwestię "skończoności" typów induktywnych i "nieskończoności" typów koinduktywnych. Tak naprawdę, to chodzi o to, że typy induktywny są dobrze ufundowane, a typy koinduktywne niekoniecznie.
9. Opisać zależny pattern matching (w rozdziale o zaawansowanej indukcji).
10. Opisać jak zasymulować indukcję-indukcję za pomocą indeksów ("presyntax"). To samo dla indukcji-rekursji.

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
3. Powiązane z powyższym: iks jest first-class jeżeli można sformować typ wszystkich iksów (albo jego przybliżenie, jak w przypadku uniwersum typów `Type`).
4. Opisać gdzies ideę Settings types: wszystkie argumenty funkcji pakować w rekord z nazwanymi polami i dobrymi wartościami domyślnymi. W sumie ma to sporo wspólnego z moim podejściem do algorytmów.
5. Opisać gdzieś bardziej inżynieriooprogramowaniowe rzeczy. Ważna idea: vertical vs horizontal Refactoring, czyli zmienić definicje paru funkcji to co innego niż zmienić sposób obsługi błędów w całym programie.

## Długofalowe
1. Użyć jsCoq do zrobienia interaktywnej książki, która wyglądałaby jakoś tak: https://x80.org/rhino-coq/v8.10/
2. Zrobić zwijane/rozwijane dowody i paragrafy.

## Zagubione notatki
1. Let `I := U × U`, and let `A : I → U` be defined by `A(X, Y) := (X → Y) × (Y → X)`. Define `B` as `B(X, Y )(f, g) := X × Y` and `r(X, Y )(f, g)(x, y) := (f(x) = y) × (x = g(y))`. Then the associated M-type is a family `M : I → U` and `M(A, B)` is equivalent to `A \equiv B`.
2. `DNE` zachodzi wtedy i tylko wtedy, gdy każde zdanie jest negacją jakiegoś typu (to z jakiejś HoTTowej pracy, ale nie pamiętam jakiej).
3. Spróbować dodać minirozdział poświęcony logicznym aspektom racjonalności (tak jak w książce: Keith Stanovich, The Rationality Quotient).
4. Paradoks zwrotności. Są 2 rodzaje ludzi:
  - Ci, którzy uważają, że są dwa rodzaje ludzi.
  - Ci, którzy są innego zdania.

  ## Przemyślenia nad permutacjami
  1. Dwa drzewa `t1` i `t2` trzymające elementy typu `A` są swoimi permutacjami, gdy dla każdego elementu `x : A` typ pozycji `x` w `t1` jest izomorficzny z typem pozycji `x` w `t2`.
  2. Taka definicja jest niewygodna do użycia, więc można spróbować ją zdefunkcjonalizować albo na różne sposoby wyspecjalizować, np.:
  - definicja przez "zabieranie" po jednym elemencie z każdego drzewa na raz (ale trzeba być ostrożnym, bo z ogólnych drzew nie zabiera się tak łatwo jak z list). No i trzeba pamiętać o tym, że jeżeli drzewo jest nieskończone, to zabieranie po jednym elemencie nie jest najmądrzejsze...
  - dualnie można zrobić definicję przez "dodawanie" po jednym elemencie do każdego drzewa, ale trzeba pamiętać o konstruktorach do zamiany miejscami (no i znowu jest kwestia nieskończonych drzew)
  - definicja przez transpozycje. Dla list jest to łatwe, ale w ogólności jest trudniej. Ogólna transpozycja polega na zamianie pozycji dwóch elementów `x` i `y`... pod warunkiem, że oba drzewa mają ten sam kształt, bo jak nie, to jest jeszcze trudniej.
  - jeżeli elementy występują w drzewie skończoną ilość razy (i mają rozstrzygalną równośc (i samo drzewo jest skończone)), to można użyć definicji opartej o liczenie wystąpień