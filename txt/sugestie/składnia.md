# O lepszej składni

Coqowa składnia nie jest optymalna. Szczerze mówiąc, to jest trochę nadmiarowa. Stąd pomysł, żeby jakoś ją ulepszyć. Na szczęście programiści dawno temu wymyślili pewną mądrą zasadę: don't repeat yourself, w skrócie DRY, którą można tutaj zastosować. Idea jest taka, żeby nie pisać niczego dwa (lub więcej) razy.

## Typy induktywne

Jest nawet pewien prosty sposób osiągnięcia tego. Otóż w definicjach typów induktywnych mamy parametry i indeksy, przy czym parametry nie mogą się zmieniać, a indeksy owszem.

Skoro parametry nie mogą się zmieniać, to po cholerę pisać je za każdym razem? Wot, wymyśliliśmy ulepszenie.

Stara wersja:
```Coq
Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.
```

Nowa wersja:
```Coq
Inductive list (A : Type) : Type :=
    | nil : list
    | cons : A -> list -> list.
```

Jednym słowem: nie ma sensu za każdym razem pisać `list A`, skoro i tak wiadomo, że musi tam być `A`.

Obecnie można pisać niemal tak jak w nowej wersji, ale trzeba ustawić `A` jako argument domyślny, co sprawia, że w ostatecznym rozrachunku musimy napisać znacznie więcej, bo potem trzeba jeszcze wyczyścić deklaracje argumentów domyślnych.

Obecnie tak wolno:
```Coq
Inductive list {A : Type} : Type :=
    | nil : list
    | cons : A -> list -> list.

Arguments list _ : clear implicits.
```

Zyski z tego są żadne, a nawet ujemne, bo wygląda to dużo gorzej.

Oczywiście proponowane ulepszenie można by połączyć z innymi, które już są dostępne, i np. nie pisać typu zwracanego.

Nowa wersja:
```Coq
Inductive list (A : Type) : Type :=
    nil | cons (h : A) (t : list).
```

Obecnie wolno tylko tak:
```Coq
Inductive list {A : Type} : Type :=
    nil | cons (h : A) (t : list).

Arguments list _ : clear implicits.
```

## Funkcje rekurencyjne

Tę samą zasadę można zastosować do definicji przez rekursję: wymuszamy, że parametry nie mogą się zmieniać, i wobec tego nie musimy ich pisać. Zmieniają się jedynie indeksy, które musimy wprost zaznaczyć jako takie.

Oczywiście to trochę komplikuje sprawę, bo komenda `Fixpoint` słabo się do takiego stylu definiowania nadaje, ale można temu zaradzić definicjami przez równania, jak w Haskellu czy Agdzie.

Stary sposób
```Coq
Fixpoint plus (n m : nat) : nat :=
match n with
    | 0 => m
    | S n' => S (plus n' m)
end.
```

Nowy sposób
```Coq
plus (n : nat) : nat -> nat :=
| 0 => n
| S m' => S (plus m')
```

Zauważmy, że nowy sposób definiowania wymusza na nas, żeby dodawanie było zdefiniowane przez rekursję po drugim argumencie, bo pierwszy jest parametrem, czyli nie może się zmieniać. 

## Nazwy argumentów w konstruktorach

Obecnie jeżeli konstruktor ma dużo argumentów

```Coq
Inductive wut : Type :=
    | w : A -> B -> C -> D.
```

to przy dopasowaniu do wzorca trzeba je wiązać (albo pomijać za pomocą `_`)

```Coq
fun x : wut =>
match x with
    | w a _ _ d => ...
end
```

Mądrym pomysłem byłoby, żeby skoro i tak można dawać argumentom konstruktorów nazwy

```Coq
Inductive wut : Type :=
    | w (a : A) (b : B) (c : C) (d : D).
```

to żeby można było tych nazw jakoś potem używać

```Coq
fun x : wut =>
match x with
    | w => tutaj można pisać x.a, x.b, x.c, x.d
end
```

Dobrze byłoby też, żeby te nazwy były poważniej traktowane przy domyślnym generowaniu nazw. Obecnie są używane, jeżeli nie poda się żadnej nazwy, no chyba że są już zajęte, to wtedy nie. Zamiast tego `destruct x` dla `x : wut` mógłby automatycznie nazywać rzeczy `x.a : A`, `x.b : B`, `x.c : C`, `x.d : D`.

Update: w Haskellu jest ciekawe rozszerzenie GHC, mianowicie [Record Wildcards](https://kodimensional.dev/recordwildcards).

Dzięki czemuś podobnego dla Coqa można by pisać jeszcze zwięźlej:

```Coq
fun x : wut =>
match x with
    | w{..} => tutaj można odnosić się do pól w pisząc a, b, c, d
end
```

Można by to w sumie też połączyć z Haskellowym `@` (np. `l@(h : t)` w Haskellu oznacza wzorzec na listę z głową `h` i ogonem `t`, a całość dodatkowo można też nazywać `l`). W Coqu ten sam wzorzec jest zapisywany jako `l as h :: t`.

```Coq
fun x : wut =>
match x with
    | w@ => tutaj można pisać a, b, c, d
end
```

Na koniec uwaga, dość subtelna: sugestie z tej sekcji są mało kompatybilne z sugestiami z poprzedniej...

## Kropka

Żeby powyższa sugestia o domyślnych nazwach działała, musi zniknąć największe szataństwo składniowe, jakie widział świat, czyli kropkę na końcu definicji/`Inductive`ów/`match`ów etc.

## Triwia

Definiowanie przez równania w Coqu umożliwia pakiet [Equations](https://github.com/mattam82/Coq-Equations), ale bez możliwości pomijania parametrów.

Pomysł na lekką składnię z pomijaniem parametrów jest wzięty z języka [Lean](https://leanprover.github.io/).

##  F*

Ostatnio dowiedziałęm się, że F* ma parę fajnych składniowych rzeczy:
- Dyskryminatory sprawdzający, którym konstruktorem zrobiono term typu induktywnego, np. `Nil? : list 'a -> bool`, `Cons? : list 'a -> bool`
- Projektory, które wyjmują argumenty z konstruktorów, ale tylko gdy term faktycznie został zrobiony takim właśnie konstruktorem. Przykłady: `Cons?.hd : l : list 'a{Cons? l} -> 'a` oraz `Cons?.tl : l : list 'a{Cons? l} -> list 'a`