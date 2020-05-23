# Rekordy (nie, nie sportowe)

Stan rekordów w Coqu i ogólnie w zasadzie w każdym możliwym języku jest smutny, a chyba mógłby być lepszy. 

Problem z rekordami jest taki, że _typy rekordowe_ (ang. _record types_) są bytami gorszego sortu. Konkretniej rzecz biorąc, istnieją one w metajęzyku (można o nich mówić w języku polskim), ale nie istnieją w języku (nie można w Coqu powiedzieć np. "dla wszystkich typów rekordowych").

Wynika z tego wiele upierdliwieństw, którym można byłoby zaradzić, gdyby typy rekordowe miały pełnię praw obywatelskich. Co to znaczy "pełnia praw"?

Ano, powinien istnieć typ induktywny, który nazwiemy na potrzeby tej notatki `Rec`, a którego elementami byłyby kody, które można interpretować jako typy rekordowe.

Dla przykładu, poniższy typ rekordowy

```coq
Record Sigma (A B : Type) : Type :=
{
    outl : A;
    outr : B;
}.
```

mógłby być interpretacją następującego kodu

```coq
Field "outr" B (Field "outl" A Nil)
```

Szczegóły typu kodów pozostawmy naszej wyobraźni, choć gdyby w Coqu była indukcja-rekursja, to można by go zdefiniować jakoś tak:

```coq
Inductive Rec : Type :=
    | RNil : Rec
    | RCons :
        forall {R : Rec} {P : El R -> Type} {x : El R},
            string -> P x -> Rec
```

gdzie `El` to funkcja interpretująca kody jako faktyczne typy rekordowe.

Ok, formalne duperele na bok. Co fajnego można by robić z tak pomyślanymi rekordami? Tu jest krótka lista (dla ułatwienia, zamiast kodami, będziemy operować typami rekordowymi i konkretną składnią):
- subtypowanie - mając dwa rekordy można łatwo sprawdzić, czy jeden jest podtypem drugiego. Dla przykładu `R = {x : nat, y : bool, z : True}` jest podtypem `R' = {x : nat, y : bool}`, więc `R` można łatwo zrzutować na `R'`, po prostu zapominając pole `z`.
- ustawienie wartości - można robić typy rekordowe z niektórymi polami z góry ustawionymi na określone wartości. Niech `R = {x : nat, y : bool, z : True}`. Moglibyśmy napisać np. `R with x = 42` i dostalibyśmy typ `{x = 42 : nat, y : bool, z : True}`, którego wartościami są w sumie takie same jak typu `{y : bool, z : True}`. Po co komu coś takiego? Jest to swego rodzaju "częściowa aplikacja" dla rekordów.
- zmiana nazwy - można zmienić nazwę pola na wygodniejszą w danej sytuacji. Niech `R = {x : nat, y : bool}`. Możemy napisać `R renaming (x to n, y to b)` i dostać typ `{n : nat, b : bool}`
- 