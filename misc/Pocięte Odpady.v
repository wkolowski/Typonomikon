(** Ćwiczenie 10. *)
Theorem ex_and_impl : forall (A : Type) (P Q : A -> Prop),
    (exists x : A, P x /\ Q x) -> (exists y : A, P y) /\ (exists z : A, Q z).
Proof.
  intros. destruct H as [x H]. destruct H.
  split; exists x; assumption.
Restart.
  intros. destruct H as [x [HP HQ]].
  (** Zauważ, że wzorce przekazywane do taktyki 'destruct' można zagnieżdżać,
     dzięki czemu unikamy nadmiernego pisania, gdy nasze hipotezy są
     mocno zagnieżdżone (np. wielokrotna koniunkcja). *)
  split; exists x; assumption.
Restart.
  intros A P Q [x [HP HQ]].
  (** Taktyki 'intros' i 'destruct' można połączyć, przekazując
     jako argumenty dla taktyki 'intro' wzorce zamiast nazw. *)
  split; exists x; assumption.
Qed.



Fixpoint fac (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => n * fac n'
end.

Require Import Arith.

Theorem le_1_fac : forall n : nat, 1 <= fac n.
Proof.
  induction n as [| n']; simpl.
    auto.
    apply le_plus_trans. assumption.
Qed.

Theorem le_lin_fac : forall n : nat, n <= fac n.
Proof.
  induction n as [| n']; simpl.
    auto.
    replace (S n') with (1 + n'); auto.
    apply plus_le_compat.
      apply le_1_fac.
      replace n' with (n' * 1) at 1.
        apply mult_le_compat_l. apply le_1_fac.
        rewrite mult_comm. simpl. rewrite plus_comm. simpl. trivial.
Qed.

Fixpoint pow2 (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => 2 * pow2 n'
end.

Theorem le_exp_Fac : forall n : nat,
    4 <= n -> pow2 n <= fac n.
Proof.
  induction 1; simpl.
    repeat constructor.
    rewrite plus_0_r. apply plus_le_compat.
      assumption.
      replace (pow2 m) with (1 * pow2 m).
        apply mult_le_compat.
          apply le_trans with 4; auto.
          assumption.
        rewrite mult_1_l. trivial.
Qed.

    

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

Require Import List.
Import ListNotations.

Fixpoint range (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: range n'
end.