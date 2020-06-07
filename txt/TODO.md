# TODO

## Logika
1. bind i compM w podrozdziale o modalnościach
2. Być może dokonać rozróżnienia różnych _ex_ ... _quodlibet_:
  - _Ex falso quodlibet_ - `False -> P`
  - _Ex contradictione quodlibet_ - `A /\ ~ A -> P`

```Coq
Lemma not_not_bind :
  forall P Q : Prop,
    ~ ~ P -> (P -> ~ ~ Q) -> ~ ~ Q.
Proof.
  intros P Q nnp pnnq nq.
  apply nnp. intro p.
  apply pnnq.
    assumption.
    assumption.
Qed.

Lemma not_not_compM :
  forall P Q R : Prop,
    (P -> ~ ~ Q) -> (Q -> ~ ~ R) -> (P -> ~ ~ R).
(* begin hide *)
Proof.
  intros P Q R pnnq qnnr p nr.
  apply pnnq.
    assumption.
    intro q. apply qnnr.
      assumption.
      assumption.
Qed.
(* end hide *)
```

## Rekursja
1. Prymitywna.
2. Wyższego rzędu, tzn. nie w pełni zaaplikowane wywołania rekurencyjne.
3. Przez iterację.
4. Koindukcjowa.

## Indukcja
0. Opisać alternatywne składnie na typy induktywne (czyli te, w których nie trzeba aż tak dużo pisać).
1. Powyższe jest mądrym heurystycznym sposobem rozróżniania różnych poziomów zaawansowania typów induktywnych (rodzin induktywnych nie można definiować bez podawania indeksów w przeciwdziedzinie).
1. W nowym ujęciu podrozdział o regułach indukcyjnych ma być ściśle powiązany z wprowadzeniem rekursji strukturalnej (tzn. nie-prymitywnej).
2. Argumenty indukcyjne pierwszego i wyższego rzędu.
4. Opisać zippery (czyli różniczkowanie typów).
6. Indeksowane rodziny induktywne to wystarczająco dla początkujących. Przesunąć rozdziały o indukcji-indukcji/indukcji-rekursji (i wszystkim, czego explicite nie ma w Coqu) dalej.
7. Kwestia non-uniform parametrs i jak je zasymulować przy użyciu indeksów.
8. Typy induktywne z parametrami + równość = rodziny indeksowane.
10. Alternatywna nazwa na injektywność konstruktorów to niekonfuzja (`NoConfusion`), zaś nazwa na nierówności `t <> c t` to acykliczność.
5. Ćwiczenia:
- Z przetwarzania danych, typu "znajdź wszystkie liczby nieparzyste większe od x, których suma cyfr to dupa konia".
- Z definiowania typów induktywnych (i relacji też). W tym takie:
- Z uogólniania hipotezy indukcyjnej (+ akumulatory i rekursja ogonowa).

## Listy
1. Opisać na przykładzie list różnice między teorią typów, a hardkorową matematyką konstruktywną opartą na relacjach separacji (apartness).
2. Dokończyć prace nad funkcjami znajdującymi wszystkie struktury danego rodzaju (permutacje, cykle, podciągi, palindromy etc.).
3. Dokończyć prace nad różnymi alternatywnymi definicjami permutacji.
5. Dokończyć prace nad resztą rzeczy z folderu List/.

## Funkcje
1. Dokończyć podrozdział o odwrotnościach i izomorfizmach.
2. Napisać coś o (pre/post)skracalności.

## HoTT
1. Kodowanie Churcha dla typów ilorazowych.
2. Wprowadzić teorię zbiorów za pomocą wyższego typu induktywnego.
3. `B : A -> U` jest uniwalentne, gdy dla `x, y : A` jest `(x = y) = (B x = B y)` / https://vimeo.com/338899939
4. Homotopy pullback https://vimeo.com/337960032
5. Napisać o bijekcjach, injekcjach i surjekcjach z bardziej HoTTowej perspektywy.
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
  - są jeszcze jakieś, ale nie pamiętam

## Monady
1. Monady dla logiki klasycznej! Klasyczne funkcje, aksjomat wyboru i nie tylko: https://arxiv.org/pdf/1008.1213.pdf
2. Subtelna uwaga: monada to nie to samo co nieskończoność-monada, więc homotopiowo trzeba uważać.

## Inne
1. Znaleźć prostszy przykład dla podrozdziału o ścisłej pozytywności (ale do której konkretnie części?).
9. Izomorfizmy dla typów induktywnych: każde drzewo jest drzewem o jakiejś wysokości (no chyba że ma nieskończone rozgałęzienie, to wtedy nie). Uogólniając: każdy element typu induktywnego jest elementem odpowiadającego my typu indeksowanego o pewnym indeksie.
14. Opisać taktyki dla redukcji i obliczeń.
15. Opisać podstawy teorii typów.
17. Opisać zmienne egzystencjalne i odpowiadające im taktyki.
18. Opisać taktyki do radzenia sobie z typami zależnymi.
19. Opisać: silnia, współczynniki dwumianowe, sumy szeregów, charakteryzowanie wzorów rekurencyjnych.
26. Odkłamać kwestię polimorfizmu najlepiej przy okazji rozdziału o programowaniu generycznym.
26. Kwestia parametryczności: `lam X. lam nil. lam cons. cons X nil` - egzotyczna lista.
27. Twierdzenie: można zanurzyć liczby naturalne w liczby konaturalne, ale nie można tego zanurzenia odwrócić.
32. Podkreślić gdzieś mocniej, że reguła indukcji mówi, że nie ma nic poza tym, co można zrobić konstruktorami.
33. Powiązanie reguł wprowadzania/eliminacji/obliczania/unikalności z równoważnościami.
34. A równoważności to nic innego jak właściwości (czy też konstrukcje) uniwersalne.
35. Intuicja dla reguł unikalności: dzida składa się z przeddzidzia dzidy, śróddzidzia dzidy i zadzidzia dzidy.
36. Przestrzeń metryczną można zdefiniować za pomocą "Ball Relation": `Q+ -> X -> X -> Prop`

## Filozofia
1. Mega ważna obserwacja: nazwy zawsze należy nadawać tak, żeby zgadzały się z definicją, czyli nazwy są intensjonalne. Ewentualne ekstensjonalne powiązanie ze sobą (w postaci równoważności) różnych apriori nazw następować musi później, na mocy pokazania równoważności tego, co one oznaczają. Przykład: różne definicje równoważności powinny się nazywać inaczej, np. invertible, biinvertible, contractible etc.

## Sugestie i problemy z koła
1. Opisać dokładniej definiowanie przez dowód.
2. Nie trzeba specjalizować hipotezy, żeby przepisać.
3. Być może coś więcej o równości (i jej alternatywnej definicji?).
4. Napisać bardziej wprost o deklarowaniu hipotez.
5. Ulepszyć ściągę z taktykami i komendami.
6. Ludzie po czasie zapominają składni.
7. Napisać coś więcej o składni i o rysowaniu termów.
8. Dodać zadanie z dwiema dziwnymi identycznościami (co najmniej intensjonalna i ekstensjonalna, ale nie pamiętam, o co dokładnie chodzi).
9. Osąd `x : A` możemy czytać jako "x jest typu A", zaś konkretnie `x : nat` jako "x jest liczbą naturalną". Zrobić więcej ściąg z czytania różnych rzeczy.

## Długofalowe
1. Użyć jsCoq do zrobienia interaktywnej książki, która wyglądałaby jakoś tak: https://x80.org/rhino-coq/v8.10/
2. Zrobić zwijane/rozwijane dowody i paragrafy.
3. Dodać rozdział o stylu, wcięciach, komentowaniu etc. Patrz tu: https://www.cs.princeton.edu/courses/archive/fall19/cos326/style.php#1
4. W nawiązaniu do powyższego: opisać bardziej rzeczy do strukturyzowania dowodów, np. `{ }` albo bullet pointy `*`, `+` i `-`