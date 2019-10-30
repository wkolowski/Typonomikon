(** * Metoda induktywnej dziedziny *)


Require Import Omega.

Inductive divD : nat -> nat -> Prop :=
    | divD_lt : forall n m : nat, n < S m -> divD n m
    | divD_ge :
        forall n m : nat,
          n >= S m -> divD (n - S m) m -> divD n m.

Lemma divD_lt_inv :
  forall n m : nat, n < S m ->
    forall d : divD n m, exists H : n < S m, d = divD_lt n m H.
Proof.
  destruct d.
    exists l. reflexivity.
    abstract omega.
Defined.

Lemma divD_ge_inv :
  forall n m : nat, n >= S m -> divD n m -> divD (n - S m) m.
Proof.
  destruct 2.
    abstract omega.
    exact H1.
Defined.

Require Import NArith.

Search lt.

Check le_lt_dec.
Check @left.
Definition div_aux {n m : nat} (d : divD n m) : nat.
Proof.
  refine (
    fix div_aux {n m : nat} (d : divD n m) {struct d} : nat :=
    match le_lt_dec (S m) n with
        | right _ => 0
        | left H => S (div_aux (divD_ge_inv n m H d))
    end
  ).

destruct (le_lt_dec (S m) n).
  apply S. apply (div_aux (n - S m) m).
    apply (divD_ge_inv n m l d). Guarded.



Fixpoint div'_aux {n m : nat} (H : divD n m) : nat :=
match H with
    | divD_lt _ _ _ => 0
    | divD_ge _ _ _ H' => S (div'_aux H')
end.