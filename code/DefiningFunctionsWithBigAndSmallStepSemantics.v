(** Ciekawa perspektywa: jakby się tak trochę zastanowić, to induktywna definicja
    wykresu funkcji wygląda zupełnie jak semantyka dużych kroków dla bardzo
    ubogiego rachunku, w którym:
    - termy to elementy dziedziny funkcji
    - wartości to prawe strony równań definiujących funkcję, w których nie ma wywołań rekurencyjnych

    W takiej perspektywie semantykę dużych kroków dla STLC definiujemy dlatego,
    że nie umiemy zdefiniować funkcji normalizującej (bo wymaga niezłych fikołków),
    a dla zwykłego rachunku lambda dlatego, że w ogóle nie da się zdefiniować
    funkcji normalizującej.

    W takim ujęciu "semantyka małych kroków" dla danej funkcji odpowiada relacji
    dobrze ufundowanej, która pozwala najwygodniej zdefiniować tę funkcję.

    Czy się mylę? I czy da się wycisnąć z tego jakieś profity? *)

Fixpoint add (n m : nat) : nat :=
match n with
| 0 => m
| S n' => S (add n' m)
end.

Inductive Graph_add : nat -> nat -> nat -> Prop :=
| Graph_add_0 : forall m : nat, Graph_add 0 m m
| Graph_add_S : forall n m r : nat, Graph_add n m r -> Graph_add (S n) m (S r).

(* Inductive Small_add : nat * nat -> nat * nat -> Prop := *)
