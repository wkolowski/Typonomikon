Fixpoint evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

(** Funkcja [evenb] zwraca [true], gdy jej argument jest parzysty, zaś
    [false], gdy jest nieparzysty. Możemy myśleć o niej jako o odpowiedniku
    zdefiniowanego przez nas wcześniej induktywnego predykatu [even].

    Definicja rekurecyjna różni się od induktywnej już na pierwszy
    rzut oka: pattern matching ma trzy przypadki, podczas gdy w
    definicji induktywnej wystąpiły jedynie dwa konstruktory. Wynika
    to z faktu, że definicja induktywna mówi jedynie, kiedy liczba
    jest parzysta, milczy zaś o liczbach, które parzyste nie są.
    Żeby udowodnić, że liczba nie jest parzysta, musimy posłużyć się
    negacją i udowodnić zdanie [~ even n].
*)


(*Theorem even_n_Sn : forall n : nat,
    even n -> even (S n) -> False.
Proof.
  induction n as [| n'].
    inversion 2.
    intros. apply IHn'.
      inversion H0; subst. assumption.
      assumption.
Qed.
Require Import Arith.*)