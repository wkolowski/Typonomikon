(** Jakby się tak trochę zastanowić, to induktywna definicja wykresu funkcji
    wygląda zupełnie jak semantyka dużych kroków dla bardzo ubogiego rachunku,
    w którym:
    - termy to elementy dziedziny funkcji
    - wartości to prawe strony równań definiujących funkcję, w których nie ma
      wywołań rekurencyjnych

    Patrząc z takiej perspektywy, semantykę dużych kroków dla STLC definiujemy
    dlatego, że nie umiemy zdefiniować funkcji normalizującej (bo wymaga trochę
    fikołków), a dla zwykłego rachunku lambda dlatego, że w ogóle nie da się
    zdefiniować funkcji normalizującej.

    Semantyka małych kroków dla rachunku w świecie funkcji odpowiada zaś relacji
    dobrze ufundowanej, która pozwala najwygodniej zdefiniować tę funkcję. *)

Fixpoint add (n m : nat) : nat :=
match n with
| 0 => m
| S n' => S (add n' m)
end.

Inductive Graph_add : nat -> nat -> nat -> Prop :=
| Graph_add_0 : forall m : nat, Graph_add 0 m m
| Graph_add_S : forall n m r : nat, Graph_add n m r -> Graph_add (S n) m (S r).

Lemma Graph_add_correct :
  forall n m r : nat,
    Graph_add n m r -> r = add n m.
Proof.
  now induction 1; cbn; [| rewrite IHGraph_add].
Qed.

Lemma Graph_add_complete :
  forall n m r : nat,
    r = add n m -> Graph_add n m r.
Proof.
  induction n as [| n']; cbn; intros m r ->.
  - now constructor.
  - now constructor; apply IHn'.
Qed.

Inductive Small_add (add : nat -> nat -> nat) : nat -> nat -> nat -> Prop :=
| Small_add_0 : forall m : nat, Small_add add 0 m m
| Small_add_S : forall n m : nat, Small_add add (S n) m (S (add n m)).

Lemma Small_add_correct :
  forall {f : nat -> nat -> nat} (n m r : nat),
    Small_add f n m r -> f = add.
Proof.
Abort.