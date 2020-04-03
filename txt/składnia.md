# O lepszej składni

Coqowa składnia nie jest optymalna. Szczerze mówiąc, to jest do dupy. Stąd pomysł, żeby jakoś ją ulepszyć. Na szczęście programiści dawno temu wymyślili pewną mądrą zasadę: don't repeat yourself, w skrócie DRY, którą można tutaj zastosować. Idea jest taka, żeby nie pisać niczego dwa (lub więcej) razy.

## Typy induktywne

Jest nawet pewien prosty sposób osiągnięcia tego. Otóż w definicjach typów induktywnych mamy parametry i indeksy, przy czym parametry nie mogą się zmieniać, a indeksy owszem.

Skoro parametry nie mogą się zmieniać, to po cholerę pisać je za każdym razem? Wot, wymyśliliśmy ulepszenie.

Stara wersja
```Coq
Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.
```

Nowa wersja
```Coq
Inductive list (A : Type) : Type :=
    | nil : list
    | cons : A -> list -> list.
```

Jednym słowem: nie ma sensu za każdym razem pisać `list A`, skoro i tak wiadomo, że musi tam być `A`.

Oczywiście to ulepszenie można połączyć z innymi, które już są dostępne, i np. nie pisać typu zwracanego.

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

## Triwia

Definiowanie przez równania w Coqu umożliwia pakiet [Equations](https://github.com/mattam82/Coq-Equations), ale bez możliwości pomijania parametrów.

Pomysł lekką składnię z pomijaniem parametrów jest wzięty z języka [Lean](https://leanprover.github.io/).