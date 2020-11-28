(** * D4: Arytmetyka Peano *)

(* begin hide *)

(*
TODO: opisać silnię, współczynniki dwumianowe, sumy szeregów
TODO: opisać charakteryzowanie wzorów rekurencyjnych
*)

(* end hide *)

(** Poniższe zadania mają służyć utrwaleniu zdobytej dotychczas wiedzy na
    temat prostej rekursji i indukcji. Większość powinna być robialna po
    przeczytaniu rozdziału o konstruktorach rekurencyjnych, ale niczego nie
    gwarantuję.

    Celem zadań jest rozwinięcie arytmetyki do takiego poziomu, żeby można
    było tego używać gdzie indziej w jakotakim stopniu. Niektóre zadania
    mogą pokrywać się z zadaniami obecnymi w tekście, a niektóre być może
    nawet z przykładami. Staraj się nie podglądać.

    Nazwy twierdzeń nie muszą pokrywać się z tymi z biblioteki standardowej,
    choć starałem się, żeby tak było. *)

Module MyNat.

(** * Podstawy *)

(** ** Definicja i notacje *)

(** Zdefiniuj liczby naturalne. *)

(* begin hide *)
Inductive nat : Set :=
    | O : nat
    | S : nat -> nat.
(* end hide *)

Notation "0" := O.
Notation "1" := (S 0).

(** ** [0] i [S] *)

(** Udowodnij właściwości zera i następnika. *)

Lemma neq_0_Sn :
  forall n : nat, 0 <> S n.
(* begin hide *)
Proof.
  do 2 intro. inversion H.
Qed.
(* end hide *)

Lemma neq_n_Sn :
  forall n : nat, n <> S n.
(* begin hide *)
Proof.
  induction n as [| n'].
    apply neq_0_Sn.
    intro. apply IHn'. inversion H. assumption.
Qed.
(* end hide *)

Lemma not_eq_S :
  forall n m : nat, n <> m -> S n <> S m.
(* begin hide *)
Proof.
  intros; intro. apply H. inversion H0. trivial.
Qed.
(* end hide *)

Lemma S_injective :
  forall n m : nat, S n = S m -> n = m.
(* begin hide *)
Proof.
  inversion 1. trivial.
Qed.
(* end hide *)

(** ** Poprzednik *)

(** Zdefiniuj funkcję zwracającą poprzednik danej liczby naturalnej.
    Poprzednikiem [0] jest [0]. *)

(* begin hide *)
Definition pred (n : nat) : nat :=
match n with
    | 0 => 0
    | S n' => n'
end.
(* end hide *)

Lemma pred_0 : pred 0 = 0.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma pred_Sn :
  forall n : nat, pred (S n) = n.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

(** * Proste działania *)

(** ** Dodawanie *)

(** Zdefiniuj dodawanie (rekurencyjnie po pierwszym argumencie) i
    udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint plus (n m : nat) : nat :=
match n with
    | 0 => m
    | S n' => S (plus n' m)
end.
(* end hide *)

Lemma plus_0_l :
  forall n : nat, plus 0 n = n.
(* begin hide *)
Proof.
  intro. cbn. trivial.
Qed.
(* end hide *)

Lemma plus_0_r :
  forall n : nat, plus n 0 = n.
(* begin hide *)
Proof.
  intro. induction n as [| n'].
    trivial.
    cbn. f_equal. assumption.
Qed.
(* end hide *)

Lemma plus_n_Sm :
  forall n m : nat, S (plus n m) = plus n (S m).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intro.
    trivial.
    rewrite IHn'. trivial.
Qed.
(* end hide *)

Lemma plus_Sn_m :
  forall n m : nat, plus (S n) m = S (plus n m).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; trivial.
Qed.
(* end hide *)

Lemma plus_assoc :
  forall a b c : nat,
    plus a (plus b c) = plus (plus a b) c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn.
    trivial.
    intros. rewrite IHa'. trivial.
Qed.
(* end hide *)

Lemma plus_comm :
  forall n m : nat, plus n m = plus m n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite plus_0_r. trivial.
    induction m as [| m']; cbn.
      rewrite plus_0_r. trivial.
      rewrite IHn'. rewrite <- IHm'. cbn. rewrite IHn'.
        trivial.
Qed.
(* end hide *)

Lemma plus_no_annihilation_l :
  ~ exists a : nat, forall n : nat, plus a n = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S 0)).
  rewrite plus_comm in H. cbn in H. induction a as [| a'].
    inversion H.
    apply IHa'. inversion H. assumption.
Qed.
(* end hide *)

Lemma plus_no_annihilation_r :
  ~ exists a : nat, forall n : nat, plus n a = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S 0)).
  rewrite plus_comm in H. cbn in H. induction a as [| a'].
    inversion H.
    apply IHa'. rewrite plus_comm in *. cbn in *.
      inversion H. assumption.
Qed.
(* end hide *)

Lemma plus_no_inverse_l :
  ~ forall n : nat, exists i : nat, plus i n = 0.
(* begin hide *)
Proof.
  intro. destruct (H (S 0)) as [i H']. rewrite plus_comm in H'.
  inversion H'.
Qed.
(* end hide *)

Lemma plus_no_inverse_r :
  ~ forall n : nat, exists i : nat, plus n i = 0.
(* begin hide *)
Proof.
  intro. destruct (H (S 0)) as [i H']. inversion H'.
Qed.
(* end hide *)

Lemma plus_no_inverse_l_strong :
  forall n i : nat, n <> 0 -> plus i n <> 0.
(* begin hide *)
Proof.
  destruct i; cbn; intros.
    assumption.
    inversion 1.
Qed.
(* end hide *)

Lemma plus_no_inverse_r_strong :
  forall n i : nat, n <> 0 -> plus n i <> 0.
(* begin hide *)
Proof.
  intros. rewrite plus_comm. apply plus_no_inverse_l_strong. assumption.
Qed.
(* end hide *)

(** ** Alternatywne definicje dodawania *)

(** Udowodnij, że poniższe alternatywne metody zdefiniowania dodawania
    rzeczywiście definiują dodawanie. *)

Fixpoint plus' (n m : nat) : nat :=
match m with
    | 0 => n
    | S m' => S (plus' n m')
end.

Lemma plus'_is_plus :
  forall n m : nat, plus' n m = plus n m.
(* begin hide *)
Proof.
  intros n m. generalize dependent n.
  induction m as [| m']; cbn; intros.
    rewrite plus_0_r. trivial.
    rewrite IHm'. rewrite (plus_comm n (S m')). cbn.
      rewrite plus_comm. trivial.
Qed.
(* end hide *)

Fixpoint plus'' (n m : nat) : nat :=
match n with
    | 0 => m
    | S n' => plus'' n' (S m)
end.

Lemma plus''_is_plus :
  forall n m : nat, plus'' n m = plus n m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    intro. rewrite IHn', plus_comm. cbn. rewrite plus_comm. reflexivity.
Qed.
(* end hide *)

Fixpoint plus''' (n m : nat) : nat :=
match m with
    | 0 => n
    | S m' => plus''' (S n) m'
end.

Lemma plus'''_is_plus :
  forall n m : nat, plus''' n m = plus n m.
(* begin hide *)
Proof.
  intros n m. generalize dependent n.
  induction m as [| m']; cbn; intros.
    rewrite plus_0_r. reflexivity.
    rewrite IHm'. cbn. rewrite (plus_comm n (S _)). cbn.
      rewrite plus_comm. reflexivity.
Qed.
(* end hide *)

(** ** Odejmowanie *)

(** Zdefiniuj odejmowanie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint minus (n m : nat) : nat :=
match n, m with
    | 0, _ => 0
    | _, 0 => n
    | S n', S m' => minus n' m'
end.
(* end hide *)

Lemma minus_1_r :
  forall n : nat, minus n 1 = pred n.
(* begin hide *)
Proof.
  repeat (destruct n; cbn; trivial).
Qed.
(* end hide *)

Lemma minus_0_l :
  forall n : nat, minus 0 n = 0.
(* begin hide *)
Proof.
  cbn. trivial.
Qed.
(* end hide *)

Lemma minus_0_r :
  forall n : nat, minus n 0 = n.
(* begin hide *)
Proof.
  destruct n; trivial.
Qed.
(* end hide *)

Lemma minus_S :
  forall n m : nat,
    minus (S n) (S m) = minus n m.
(* begin hide *)
Proof.
  cbn. trivial.
Qed.
(* end hide *)

Lemma minus_diag:
  forall n : nat, minus n n = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; trivial.
Qed.
(* end hide *)

Lemma minus_plus_l :
  forall n m : nat,
    minus (plus n m) n = m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    apply minus_0_r.
    apply IHn'.
Qed.
(* end hide *)

Lemma minus_plus_r :
  forall n m : nat,
    minus (plus n m) m = n.
(* begin hide *)
Proof.
  intros. rewrite plus_comm. apply minus_plus_l.
Qed.
(* end hide *)

Lemma minus_plus_distr :
  forall a b c : nat,
    minus a (plus b c) = minus (minus a b) c.
(* begin hide *)
Proof.
  induction a as [| a'].
    cbn. trivial.
    destruct b, c; cbn; trivial.
Restart.
  induction a; destruct b, c; cbn; trivial.
Qed.
(* end hide *)

Lemma minus_exchange :
  forall a b c : nat,
    minus (minus a b) c = minus (minus a c) b.
(* begin hide *)
Proof.
  intros a b. generalize dependent a. induction b as [| b'].
    intros. repeat rewrite minus_0_r. trivial.
    intros a c. generalize dependent a. induction c as [| c'].
      intro. repeat rewrite minus_0_r. trivial.
      destruct a as [| a'].
        cbn. trivial.
        cbn in *. rewrite <- IHc'. rewrite IHb'. destruct a'; cbn.
          trivial.
          rewrite IHb'. trivial.
Qed.

Lemma minus_not_assoc :
  ~ forall a b c : nat,
      minus a (minus b c) = minus (minus a b) c.
(* begin hide *)
Proof.
  intro. specialize (H 1 1 1). cbn in H. inversion H.
Qed.
(* end hide *)

Lemma minus_not_comm :
  ~ forall n m : nat,
      minus n m = minus m n.
(* begin hide *)
Proof.
  intro. specialize (H 1 0). cbn in H. inversion H.
Qed.
(* end hide *)

(** ** Odejmowanie v2 *)

Fixpoint sub (n m : nat) : nat :=
match m with
    | 0    => n
    | S m' => pred (sub n m')
end.

Lemma sub_1_r :
  forall n : nat, sub n 1 = pred n.
(* begin hide *)
Proof.
  reflexivity.
Qed.
(* end hide *)

Lemma sub_pred_l :
  forall n m : nat,
    sub (pred n) m = pred (sub n m).
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    reflexivity.
    rewrite IHm'. reflexivity.
Qed.
(* end hide *)

(* Lemma sub_pred_r :
  forall n m : nat,
    sub n (pred m) = sub n m.
(* begin hide *)
Proof.
  intros n m. revert n.
  induction m as [| m']; cbn; intros.
    reflexivity.
    rewrite <- IHm' at 2.
    inducti
    rewrite <- sub_pred_l.
    rewrite IHm'. reflexivity.
Qed.
(* end hide *)
 *)

Lemma sub_0_l :
  forall n : nat, sub 0 n = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma sub_0_r :
  forall n : nat, sub n 0 = n.
(* begin hide *)
Proof.
  reflexivity.
Qed.
(* end hide *)

Lemma sub_S_S :
  forall n m : nat,
    sub (S n) (S m) = sub n m.
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    reflexivity.
    rewrite <- IHm'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma pred_sub_S :
  forall n m : nat,
    pred (sub (S n) m ) = sub n m.
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    reflexivity.
    rewrite IHm'. reflexivity.
Qed.

(* end hide *)
Lemma sub_diag :
  forall n : nat, sub n n = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite pred_sub_S, IHn'. reflexivity.
Qed.
(* end hide *)

Lemma sub_plus_l :
  forall n m : nat,
    sub (plus n m) n = m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    intro. rewrite pred_sub_S. apply IHn'.
Qed.
(* end hide *)

Lemma sub_plus_r :
  forall n m : nat,
    sub (plus n m) m = n.
(* begin hide *)
Proof.
  intros. rewrite plus_comm. apply sub_plus_l.
Qed.
(* end hide *)

Lemma sub_plus_distr :
  forall a b c : nat,
    sub a (plus b c) = sub (sub a b) c.
(* begin hide *)
Proof.
  induction b as [| b']; cbn; intros.
    reflexivity.
    rewrite IHb', sub_pred_l. reflexivity.
Qed.
(* end hide *)

Lemma sub_exchange :
  forall a b c : nat,
    sub (sub a b) c = sub (sub a c) b.
(* begin hide *)
Proof.
  induction b as [| b']; cbn.
    reflexivity.
    intro. rewrite sub_pred_l, IHb'. reflexivity.
Qed.
(* end hide *)

Lemma sub_not_assoc :
  ~ forall a b c : nat,
      sub a (sub b c) = sub (sub a b) c.
(* begin hide *)
Proof.
  intro. specialize (H 1 1 1). cbn in H. inversion H.
Qed.
(* end hide *)

Lemma sub_not_comm :
  ~ forall n m : nat,
      sub n m = sub m n.
(* begin hide *)
Proof.
  intro. specialize (H 1 0). cbn in H. inversion H.
Qed.
(* end hide *)

(** ** Mnożenie *)

(** Zdefiniuj mnożenie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint mult (n m : nat) : nat :=
match n with
    | 0 => 0
    | S n' => plus m (mult n' m)
end.
(* end hide *)

Lemma mult_0_l :
  forall n : nat, mult 0 n = 0.
(* begin hide *)
Proof.
  cbn. reflexivity.
Qed.
(* end hide *)

Lemma mult_0_r :
  forall n : nat, mult n 0 = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    assumption.
Restart.
  induction n; trivial.
Qed.
(* end hide *)

Lemma mult_1_l :
  forall n : nat, mult 1 n = n.
(* begin hide *)
Proof.
  destruct n as [| n'].
    cbn. trivial.
    cbn. rewrite plus_0_r. trivial.
Restart.
  destruct n; cbn; try rewrite plus_0_r; trivial.
Qed.
(* end hide*)

Lemma mult_1_r :
  forall n : nat, mult n 1 = n.
(* begin hide *)
Proof.
  induction n.
    cbn. trivial.
    cbn. rewrite IHn. trivial.
Restart.
  induction n; cbn; try rewrite IHn; trivial.
Qed.
(* end hide *)

Lemma mult_comm :
  forall n m : nat,
    mult n m = mult m n.
(* begin hide *)
Proof.
  induction n as [| n']; intro.
    rewrite mult_0_l, mult_0_r. trivial.
    induction m as [| m'].
      rewrite mult_0_l, mult_0_r. trivial.
      cbn in *. rewrite IHn', <- IHm', IHn'. cbn.
        do 2 rewrite plus_assoc. rewrite (plus_comm n' m'). trivial.
Qed.
(* begin hide *)

Lemma mult_plus_distr_l :
  forall a b c : nat,
    mult a (plus b c) = plus (mult a b) (mult a c).
(* begin hide *)
Proof.
  induction a as [| a']; cbn; trivial.
  intros. rewrite IHa'. repeat rewrite plus_assoc.
  f_equal. repeat rewrite <- plus_assoc. f_equal.
  apply plus_comm.
Qed.
(* end hide *)

Lemma mult_plus_distr_r :
  forall a b c : nat,
    mult (plus a b) c = plus (mult a c) (mult b c).
(* begin hide *)
Proof.
  intros. rewrite mult_comm. rewrite mult_plus_distr_l.
  f_equal; apply mult_comm.
Qed.
(* end hide *)

Lemma mult_minus_distr_l :
  forall a b c : nat,
    mult a (minus b c) = minus (mult a b) (mult a c).
(* begin hide *)
Proof.
  induction a as [| a']; cbn; trivial.
  induction b as [| b'].
    intros. repeat rewrite mult_0_r. cbn. trivial.
    induction c as [| c'].
      rewrite mult_0_r. cbn. trivial.
      cbn. rewrite (mult_comm a' (S b')). cbn.
        rewrite (mult_comm a' (S c')). cbn.
        rewrite IHb'. repeat rewrite minus_plus_distr.
        f_equal. Focus 2. apply mult_comm.
        replace (plus b' (plus a' _)) with (plus a' (plus b' (mult b' a'))).
          rewrite minus_exchange. rewrite minus_plus_l.
            rewrite mult_comm. trivial.
          repeat rewrite plus_assoc. rewrite (plus_comm a' b'). trivial.
Qed.
(* end hide *)

Lemma mult_minus_distr_r :
  forall a b c : nat,
    mult (minus a b) c = minus (mult a c) (mult b c).
(* begin hide *)
Proof.
  intros. rewrite mult_comm. rewrite mult_minus_distr_l.
  f_equal; apply mult_comm.
Qed.
(* end hide *)

Lemma mult_assoc :
  forall a b c : nat,
    mult a (mult b c) = mult (mult a b) c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn; trivial.
  intros. rewrite mult_plus_distr_r.
  rewrite IHa'. trivial.
Qed.
(* end hide *)

Lemma mult_no_inverse_l :
  ~ forall n : nat, exists i : nat, mult i n = 1.
(* begin hide *)
Proof.
  intro. destruct (H (S 1)) as [i H']. rewrite mult_comm in H'.
  cbn in H'. rewrite plus_0_r in H'. destruct i.
    inversion H'.
    cbn in H'. rewrite plus_comm in H'. cbn in H'. inversion H'.
Qed.
(* end hide *)

Lemma mult_no_inverse_r :
  ~ forall n : nat, exists i : nat, mult n i = 1.
(* begin hide *)
Proof.
  intro. destruct (H (S 1)) as [i H']. cbn in H'.
  rewrite plus_0_r in H'. destruct i.
    inversion H'.
    cbn in H'. rewrite plus_comm in H'. cbn in H'. inversion H'.
Qed.
(* end hide *)

Lemma mult_no_inverse_l_strong :
  forall n i : nat, n <> 1 -> mult i n <> 1.
(* begin hide *)
Proof.
  induction i; cbn; intros.
    inversion 1.
    destruct n as [| [| n']]; cbn.
      rewrite mult_0_r. assumption.
      contradiction H. reflexivity.
      inversion 1.
Qed.
(* end hide *)

Lemma mult_no_inverse_r_strong :
  forall n i : nat, n <> 1 -> mult n i <> 1.
(* begin hide *)
Proof.
  intros. rewrite mult_comm.
  apply mult_no_inverse_l_strong. assumption.
Qed.
(* end hide *)

Lemma mult_2_plus :
  forall n : nat, mult (S (S 0)) n = plus n n.
(* begin hide *)
Proof.
  intro. cbn. rewrite plus_0_r. trivial.
Qed.
(* end hide *)

(** ** Potęgowanie *)

(** Zdefiniuj potęgowanie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint pow (n m : nat) : nat :=
match m with
    | 0 => 1
    | S m' => mult n (pow n m')
end.
(* end hide *)

Lemma pow_0_r :
  forall n : nat, pow n 0 = 1.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma pow_0_l :
  forall n : nat, pow 0 (S n) = 0.
(* begin hide *)
Proof.
  destruct n; cbn; reflexivity.
Qed.
(* end hide *)

Lemma pow_1_l :
  forall n : nat, pow 1 n = 1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; try rewrite plus_0_r; trivial.
Qed.
(* end hide *)

Lemma pow_1_r :
  forall n : nat, pow n 1 = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; try rewrite mult_1_r; trivial.
Qed.
(* end hide *)

Lemma pow_no_neutr_l :
  ~ exists e : nat, forall n : nat, pow e n = n.
(* begin hide *)
Proof.
  destruct 1 as [e H]. specialize (H 0). cbn in H. inversion H.
Qed.
(* end hide *)

Lemma pow_no_annihilator_r :
  ~ exists a : nat, forall n : nat, pow n a = a.
(* begin hide *)
Proof.
  destruct 1 as [a H]. destruct a;
  [specialize (H 1) | specialize (H 0)]; inversion H.
Qed.
(* end hide *)

Lemma pow_plus :
  forall a b c : nat,
    pow a (plus b c) = mult (pow a b) (pow a c).
(* begin hide *)
Proof.
  induction b as [| b']; induction c as [| c']; cbn.
    reflexivity.
    rewrite plus_0_r. reflexivity.
    rewrite plus_0_r, mult_1_r. reflexivity.
    rewrite IHb'. cbn. rewrite !mult_assoc. reflexivity.
Qed.
(* end hide *)

Lemma pow_mult :
  forall a b c : nat,
    pow (mult a b) c = mult (pow a c) (pow b c).
(* begin hide *)
Proof.
  induction c as [| c']; cbn.
    trivial.
    rewrite IHc'. repeat rewrite mult_assoc. f_equal.
      repeat rewrite <- mult_assoc. f_equal. apply mult_comm.
Qed.
(* end hide *)

Lemma pow_pow :
  forall a b c : nat,
    pow (pow a b) c = pow a (mult b c).
(* begin hide *)
Proof.
  induction c as [| c']; cbn.
    rewrite mult_0_r. cbn. trivial.
    rewrite IHc', (mult_comm b (S c')). cbn.
      rewrite <- pow_plus. rewrite mult_comm. trivial.
Qed.
(* end hide *)

(** * Porządek *)

(** ** Porządek [<=] *)

(** Zdefiniuj relację "mniejszy lub równy" i udowodnij jej właściwości. *)

(* begin hide *)
Inductive le (n : nat) : nat -> Prop :=
    | le_n : le n n
    | le_S : forall m : nat, le n m -> le n (S m).
(* end hide *)

Notation "n <= m" := (le n m).

Lemma le_0_n :
  forall n : nat, 0 <= n.
(* begin hide *)
Proof.
  induction n as [| n'].
    apply le_n.
    apply le_S. assumption.
Qed.
(* end hide *)

Lemma le_n_Sm :
  forall n m : nat, n <= m -> n <= S m.
(* begin hide *)
Proof.
  apply le_S.
Qed.
(* end hide *)

Lemma le_Sn_m :
  forall n m : nat, S n <= m -> n <= m.
(* begin hide *)
Proof.
  induction m as [| m'].
    inversion 1.
    intros. inversion H.
      apply le_S, le_n.
      apply le_S, IHm'. assumption.
Qed.
(* end hide *)

Lemma le_n_S :
  forall n m : nat, n <= m -> S n <= S m.
(* begin hide *)
Proof.
  induction 1.
    apply le_n.
    apply le_S. assumption.
Qed.
(* end hide *)

Lemma le_S_n :
  forall n m : nat, S n <= S m -> n <= m.
(* begin hide *)
Proof.
  intros n m. generalize dependent n. induction m as [| m'].
    intros. inversion H.
      apply le_n.
      inversion H1.
    inversion 1.
      apply le_n.
      apply le_S. apply IHm'. assumption.
Qed.
(* end hide *)

Lemma le_Sn_n :
  forall n : nat, ~ S n <= n.
(* begin hide *)
Proof.
  induction n as [| n']; intro.
    inversion H.
    apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma le_refl :
  forall n : nat, n <= n.
(* begin hide *)
Proof.
  apply le_n.
Qed.
(* end hide *)

Lemma le_trans :
  forall a b c : nat,
    a <= b -> b <= c -> a <= c.
(* begin hide *)
Proof.
  induction 1.
    trivial.
    intro. apply IHle. apply le_Sn_m. assumption.
Qed.
(* end hide *)

Lemma le_antisym :
  forall n m : nat,
    n <= m -> m <= n -> n = m.
(* begin hide *)
Proof.
  induction n as [| n'].
    inversion 2. trivial.
    induction m as [| m'].
      inversion 1.
      intros. f_equal. apply IHn'; apply le_S_n; assumption.
Qed.
(* end hide *)

Lemma le_pred :
  forall n : nat, pred n <= n.
(* begin hide *)
Proof.
  destruct n; cbn; repeat constructor.
Qed.
(* end hide *)

Lemma le_n_pred :
  forall n m : nat,
    n <= m -> pred n <= pred m.
(* begin hide *)
Proof.
  inversion 1.
    constructor.
    cbn. apply le_trans with n.
      apply le_pred.
      assumption.
Qed.
(* end hide *)

Lemma no_le_pred_n :
  ~ forall n m : nat,
      pred n <= pred m -> n <= m.
(* begin hide *)
Proof.
  intro. specialize (H 1 0 (le_n 0)). inversion H.
Qed.
(* end hide *)

Lemma le_plus_l :
  forall a b c : nat,
    b <= c -> plus a b <= plus a c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn.
    trivial.
    intros. apply le_n_S. apply IHa'. assumption.
Qed.
(* end hide *)

Lemma le_plus_r :
  forall a b c : nat,
    a <= b -> plus a c <= plus b c.
(* begin hide *)
Proof.
  intros. rewrite (plus_comm a c), (plus_comm b c).
  apply le_plus_l. assumption.
Qed.
(* end hide *)

Lemma le_plus :
  forall a b c d : nat,
    a <= b -> c <= d -> plus a c <= plus b d.
(* begin hide *)
Proof.
  induction 1.
    apply le_plus_l.
    intros. cbn. apply le_S. apply IHle. assumption.
Qed.
(* end hide *)

Lemma le_minus_S :
  forall n m : nat,
    minus n (S m) <= minus n m.
(* begin hide *)
Proof.
  induction n as [| n'].
    cbn. constructor.
    destruct m; cbn.
      rewrite minus_0_r. do 2 constructor.
      apply IHn'.
Qed.
(* end hide *)

Lemma le_minus_l :
  forall a b c : nat,
    b <= c -> minus a c <= minus a b.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply le_trans with (minus a m).
      apply le_minus_S.
      assumption.
Qed.
(* end hide *)

Lemma le_minus_r :
  forall a b c : nat,
    a <= b -> minus a c <= minus b c.
(* begin hide *)
Proof.
  intros a b c. generalize dependent a. generalize dependent b.
  induction c as [| c'].
    intros. do 2 rewrite minus_0_r. trivial.
    destruct a, b; cbn; intro; trivial.
      apply le_0_n.
      inversion H.
      apply IHc'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma le_mult_l :
  forall a b c : nat,
    b <= c -> mult a b <= mult a c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn.
    constructor.
    intros. apply le_plus.
      assumption.
      apply IHa'. assumption.
Qed.
(* end hide *)

Lemma le_mult_r :
  forall a b c : nat,
    a <= b -> mult a c <= mult b c.
(* begin hide *)
Proof.
  intros. rewrite (mult_comm a c), (mult_comm b c).
  apply le_mult_l. assumption.
Qed.
(* end hide *)

Lemma le_mult :
  forall a b c d : nat,
    a <= b -> c <= d -> mult a c <= mult b d.
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    apply le_mult_l. assumption.
    change (mult a c) with (plus 0 (mult a c)). apply le_plus.
      apply le_0_n.
      apply IHle. assumption.
Qed.
(* end hide *)

Lemma le_plus_exists :
  forall n m : nat,
    n <= m -> exists k : nat, plus n k = m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    intros. exists m. trivial.
    intros. destruct (IHn' m) as [k Hk].
      apply le_Sn_m in H. assumption.
      destruct k; cbn.
        rewrite plus_0_r in Hk. subst. cut False.
          inversion 1.
          apply (le_Sn_n m). assumption.
        exists k. rewrite plus_comm in Hk. cbn in Hk.
          rewrite plus_comm. assumption.
Qed.
(* end hide *)

Lemma le_pow_l :
  forall a b c : nat,
    a <> 0 -> b <= c -> pow a b <= pow a c.
(* begin hide *)
Proof.
  induction 2.
    constructor.
    destruct a; cbn.
      contradiction H. trivial.
      change (pow (S a) b) with (plus 0 (pow (S a) b)).
        rewrite (plus_comm (pow (S a) m) _). apply le_plus.
          apply le_0_n.
          assumption.
Qed.
(* end hide *)

Lemma le_pow_r :
  forall a b c : nat,
    a <= b -> pow a c <= pow b c.
(* begin hide *)
Proof.
  induction c as [| c']; cbn.
    constructor.
    intro. apply le_mult; auto.
Qed.
(* end hide *)

Lemma sub_0 :
  forall n m : nat,
    sub n m = 0 -> n <= m.
(* begin hide *)
Proof.
  intros n m. revert n.
  induction m as [| m']; cbn; intros.
    rewrite H. constructor.
    destruct n as [| n']; cbn.
      apply le_0_n.
      apply le_n_S, IHm'. rewrite pred_sub_S in H. assumption.
Qed.
(* end hide *)

Lemma sub_S_l :
  forall n m : nat,
    m <= n -> sub (S n) m = S (sub n m).
(* begin hide *)
Proof.
  induction m as [| m']; cbn; intros.
    reflexivity.
    rewrite IHm'.
      cbn. destruct (sub n m') eqn: Heq.
        apply sub_0 in Heq. edestruct le_Sn_n. eapply le_trans.
          exact H.
          assumption.
        cbn. reflexivity.
      eapply le_trans with (S m').
        do 2 constructor.
        assumption.
Qed.
(* end hide *)

Lemma le_sub_l :
  forall n m : nat,
    sub n m <= n.
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    constructor.
    apply le_trans with (sub n m').
      apply le_pred.
      assumption.
Qed.
(* end hide *)

Lemma sub_inv :
  forall n m : nat,
    m <= n -> sub n (sub n m) = m.
(* begin hide *)
Proof.
  intros n m. revert n.
  induction m as [| m']; intros.
    rewrite sub_0_r, sub_diag. reflexivity.
    induction n as [| n'].
      inversion H.
      cbn. rewrite pred_sub_S, sub_S_l, IHm'.
        reflexivity.
        apply le_S_n. assumption.
        apply le_sub_l.
Qed.
(* end hide *)

(** ** Porządek [<] *)

Definition lt (n m : nat) : Prop := S n <= m.

Notation "n < m" := (lt n m).

Lemma lt_irrefl :
  forall n : nat, ~ n < n.
(* begin hide *)
Proof.
  unfold lt, not; intros. apply le_Sn_n in H. assumption.
Qed.
(* end hide *)

Lemma lt_trans :
  forall a b c : nat, a < b -> b < c -> a < c.
(* begin hide *)
Proof.
  unfold lt; intros. destruct b.
    inversion H.
    destruct c as [| [| c']].
      inversion H0.
      inversion H0. inversion H2.
      apply le_S_n in H0. constructor. eapply le_trans; eauto.
Qed.
(* end hide *)

Lemma lt_asym :
  forall n m : nat, n < m -> ~ m < n.
(* begin hide *)
Proof.
  unfold lt, not; intros. cut (S n <= n).
    intro. apply le_Sn_n in H1. assumption.
    apply le_trans with m.
      assumption.
      apply le_Sn_m. assumption.
Qed.
(* end hide *)

(** ** Minimum i maksimum *)

(** Zdefiniuj operacje brania minimum i maksimum z dwóch liczb naturalnych
    oraz udowodnij ich właściwości. *)

(* begin hide *)
Fixpoint min (n m : nat) : nat :=
match n, m with
    | 0, _ => 0
    | _, 0 => 0
    | S n', S m' => S (min n' m')
end.

Fixpoint max (n m : nat) : nat :=
match n, m with
    | 0, _ => m
    | _, 0 => n
    | S n', S m' => S (max n' m')
end.
(* end hide *)

Lemma min_0_l :
  forall n : nat, min 0 n = 0.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma min_0_r :
  forall n : nat, min n 0 = 0.
(* begin hide *)
Proof.
  destruct n; cbn; reflexivity.
Qed.
(* end hide *)

Lemma max_0_l :
  forall n : nat, max 0 n = n.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma max_0_r :
  forall n : nat, max n 0 = n.
(* begin hide *)
Proof.
  destruct n; cbn; reflexivity.
Qed.
(* end hide *)

Lemma min_le :
  forall n m : nat, n <= m -> min n m = n.
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    destruct m as [| m'].
      inversion 1.
      intro. cbn. f_equal. apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma max_le :
  forall n m : nat, n <= m -> max n m = m.
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    destruct m as [| m'].
      inversion 1.
      intro. cbn. f_equal. apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma min_assoc :
  forall a b c : nat,
    min a (min b c) = min (min a b) c.
(* begin hide *)
Proof.
  induction a as [| a'].
    trivial.
    destruct b, c; auto. cbn. rewrite IHa'. trivial.
Qed.
(* end hide *)

Lemma max_assoc :
  forall a b c : nat,
    max a (max b c) = max (max a b) c.
(* begin hide *)
Proof.
  induction a as [| a'].
    trivial.
    destruct b, c; auto. cbn. rewrite IHa'. trivial.
Qed.
(* end hide *)

Lemma min_comm :
  forall n m : nat, min n m = min m n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m; cbn; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Lemma max_comm :
  forall n m : nat, max n m = max m n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m; cbn; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Lemma min_refl :
  forall n : nat, min n n = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Lemma max_refl :
  forall n : nat, max n n = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Lemma min_no_neutr_l :
  ~ exists e : nat, forall n : nat, min e n = n.
(* begin hide *)
Proof.
  intro. destruct H as [e H]. specialize (H (S e)).
  induction e.
    inversion H.
    cbn in H. inversion H. apply IHe. assumption.
Qed.
(* end hide *)

Lemma min_no_neutr_r :
  ~ exists e : nat, forall n : nat, min n e = n.
(* begin hide *)
Proof.
  intro. apply min_no_neutr_l. destruct H as [e H].
  exists e. intro. rewrite min_comm. apply H.
Qed.
(* end hide *)

Lemma max_no_annihilator_l :
  ~ exists a : nat, forall n : nat, max a n = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S a)).
  induction a; inversion H. apply IHa. assumption.
Qed.
(* end hide *)

Lemma max_no_annihilator_r :
  ~ exists a : nat, forall n : nat, max n a = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. apply max_no_annihilator_l.
  exists a. intro. rewrite max_comm. apply H.
Qed.
(* end hide *)

Lemma is_it_true :
  (forall n m : nat, min (S n) m = S (min n m)) \/
  (~ forall n m : nat, min (S n) m = S (min n m)).
(* begin hide *)
Proof.
  right. intro. specialize (H 0 0). cbn in H. inversion H.
Qed.
(* end hide *)

(** * Rozstrzygalność *)

(** ** Rozstrzygalność porządku *)

(** Zdefiniuj funkcję [leb], która sprawdza, czy [n <= m]. *)

(* begin hide *)
Fixpoint leb (n m : nat) : bool :=
match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
end.
(* end hide *)

Lemma leb_n :
  forall n : nat,
    leb n n = true.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; trivial.
Qed.
(* end hide *)

Lemma leb_spec :
  forall n m : nat,
    n <= m <-> leb n m = true.
(* begin hide *)
Proof.
  split; generalize dependent m.
    induction n as [| n'].
      cbn. trivial.
      destruct m; cbn; intro.
        inversion H.
        apply IHn'. apply le_S_n. assumption.
    induction n as [| n']; intros.
      apply le_0_n.
      destruct m; cbn.
        cbn in H. inversion H.
        cbn in H. apply le_n_S. apply IHn'. assumption.
Restart.
  split; generalize dependent m; induction n as [| n']; destruct m;
  cbn; trivial; try (inversion 1; fail); intro.
    apply IHn'. apply le_S_n. assumption.
    apply le_n.
    apply le_0_n.
    apply le_n_S. apply IHn'. assumption.
Qed.
(* end hide *)

(** ** Rozstrzygalność równości *)

(** Zdefiniuj funkcję [eqb], która sprawdza, czy [n = m]. *)

(* begin hide *)
Fixpoint eqb (n m : nat) : bool :=
match n, m with
    | 0, 0 => true
    | S n', S m' => eqb n' m'
    | _, _ => false
end.
(* end hide *)

Lemma eqb_spec :
  forall n m : nat,
    n = m <-> eqb n m = true.
(* begin hide *)
Proof.
  split; generalize dependent m; generalize dependent n.
    destruct 1. induction n; auto.
    induction n as [| n']; destruct m as [| m']; cbn; inversion 1; auto.
      f_equal. apply IHn'. assumption.
Qed.
(* end hide *)

(** * Dzielenie i podzielność *)

(** ** Dzielenie przez 2 *)

(** Pokaż, że indukcję na liczbach naturalnych można robić "co 2".
    Wskazówka: taktyk można używać nie tylko do dowodzenia. Przypomnij
    sobie, że taktyki to programy, które generują dowody, zaś dowody
    są programami. Dzięki temu nic nie stoi na przeszkodzie, aby
    taktyki interpretować jako programy, które piszą inne programy.
    I rzeczywiście — w Coqu możemy używać taktyk do definiowania
    dowolnych termów. W niektórych przypadkach jest to bardzo częsta
    praktyka. *)

Fixpoint nat_ind_2
  (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
  (HSS : forall n : nat, P n -> P (S (S n))) (n : nat) : P n.
(* begin hide *)
Proof.
  destruct n.
    apply H0.
    destruct n.
      apply H1.
      apply HSS. apply nat_ind_2; auto.
Qed.
(* end hide *)

(** Zdefiniuj dzielenie całkowitoliczbowe przez [2] oraz funkcję obliczającą
    resztę z dzielenia przez [2]. *)

(* begin hide *)
Fixpoint div2 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => S (div2 n')
end.

Fixpoint mod2 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n') => mod2 n'
end.
(* end hide *)

Notation "2" := (S (S 0)).

Lemma div2_even :
  forall n : nat, div2 (mult 2 n) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite plus_0_r in *. rewrite <- ?plus_n_Sm. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma div2_odd :
  forall n : nat, div2 (S (mult 2 n)) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite plus_0_r in *. rewrite <- ?plus_n_Sm. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma mod2_even :
  forall n : nat, mod2 (mult 2 n) = 0.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite plus_0_r, <- ?plus_n_Sm in *. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma mod2_odd :
  forall n : nat, mod2 (S (mult 2 n)) = 1.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite plus_0_r, <- ?plus_n_Sm in *. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma div2_mod2_spec :
  forall n : nat, plus (mult 2 (div2 n)) (mod2 n) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite plus_0_r in *. rewrite <- plus_n_Sm. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma div2_le :
  forall n : nat, div2 n <= n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial; try (repeat constructor; fail).
  apply le_n_S. constructor. assumption.
Qed.
(* end hide *)

Lemma div2_pres_le :
  forall n m : nat, n <= m -> div2 n <= div2 m.
(* begin hide *)
Proof.
  induction n using nat_ind_2; cbn; intros; try apply le_0_n.
  destruct m as [| [| m']]; cbn.
    inversion H. 
    inversion H. inversion H1.
    apply le_n_S, IHn. do 2 apply le_S_n. assumption.
Qed.  
(* end hide *)

Lemma mod2_le :
  forall n : nat, mod2 n <= n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial; repeat constructor; assumption.
Qed.
(* end hide *)

Lemma mod2_not_pres_e :
  exists n m : nat, n <= m /\ mod2 m <= mod2 n.
(* begin hide *)
Proof.
  exists (S (S (S 0))), (S (S (S (S 0)))). cbn.
  split; repeat constructor.
Qed.
(* end hide *)

Lemma div2_lt :
  forall n : nat,
    0 <> n -> div2 n < n.
(* begin hide *)
Proof.
  induction n using nat_ind_2; cbn; intros.
    contradiction H. reflexivity.
    apply le_n.
    unfold lt in *. destruct n as [| n'].
      cbn. apply le_n.
      specialize (IHn ltac:(inversion 1)). apply le_n_S.
        apply le_trans with (S n').
          assumption.
          apply le_S, le_n.
Qed.
(* end hide *)

(** ** Podzielność *)

Module divides.

Definition divides (k n : nat) : Prop :=
  exists m : nat, mult k m = n.

Notation "k | n" := (divides k n) (at level 40).

(** [k] dzieli [n] jeżeli [n] jest wielokrotnością [k]. Udowodnij podstawowe
    właściwości tej relacji. *)

Lemma divides_0 :
  forall n : nat, n | 0.
(* begin hide *)
Proof.
  intro. red. exists 0. apply mult_0_r.
Qed.
(* end hide *)

Lemma not_divides_0 :
  forall n : nat, n <> 0 -> ~ 0 | n.
(* begin hide *)
Proof.
  unfold not, divides; intros. destruct H0 as [m Hm].
  rewrite mult_0_l in Hm. congruence.
Qed.
(* end hide *)

Lemma divides_1 :
  forall n : nat, 1 | n.
(* begin hide *)
Proof.
  intro. red. exists n. apply mult_1_l.
Qed.
(* end hide *)

Lemma divides_refl :
  forall n : nat, n | n.
(* begin hide *)
Proof.
  intro. red. exists 1. apply mult_1_r.
Qed.
(* end hide *)

Lemma divides_trans :
  forall k n m : nat, k | n -> n | m -> k | m.
(* begin hide *)
Proof.
  unfold divides; intros.
  destruct H as [c1 H1], H0 as [c2 H2].
  exists (mult c1 c2). rewrite mult_assoc. rewrite H1, H2. trivial.
Qed.
(* end hide *)

Lemma divides_plus :
  forall k n m : nat, k | n -> k | m -> k | plus n m.
(* begin hide *)
Proof.
  unfold divides; intros.
  destruct H as [c1 H1], H0 as [c2 H2].
  exists (plus c1 c2). rewrite mult_plus_distr_l. rewrite H1, H2. trivial.
Qed.
(* end hide *)

Lemma divides_mult_l :
  forall k n m : nat, k | n -> k | mult n m.
(* begin hide *)
Proof.
  unfold divides. destruct 1 as [c H].
  exists (mult c m). rewrite mult_assoc. rewrite H. trivial.
Qed.
(* end hide *)

Lemma divides_mult_r :
  forall k n m : nat, k | m -> k | mult n m.
(* begin hide *)
Proof.
  intros. rewrite mult_comm. apply divides_mult_l. assumption.
Qed.
(* end hide *)

Lemma divides_le :
  ~ forall k n : nat, k | n -> k <= n.
(* begin hide *)
Proof.
  intro. cut (1 <= 0).
    inversion 1.
    apply H. red. exists 0. cbn. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Definition prime (p : nat) : Prop :=
  forall k : nat, k | p -> k = 1 \/ k = p.

Lemma double_not_prime :
  forall n : nat,
    n <> 1 -> ~ prime (mult 2 n).
Proof.
  unfold prime, not; intros.
  destruct (H0 2).
    red. exists n. reflexivity.
    inversion H1.
    destruct n as [| [| n']]; inversion H1.
      apply H. reflexivity.
      rewrite plus_comm in H3. inversion H3.
Qed.
(* end hide *)

End divides.

(** * Silnia *)

(** Zdefiniuj silnię.

    Przykład:
    [fac 5 = 1 * 2 * 3 * 4 * 5 = 120]

*)

(* begin hide *)
Fixpoint fac (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => mult n (fac n')
end.
(* end hide *)

Lemma le_1_fac :
  forall n : nat, 1 <= fac n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    constructor.
    replace 1 with (plus 1 0).
      apply le_plus.
        assumption.
        apply le_0_n.
      apply plus_comm.
Qed.
(* end hide *)

Require Import Setoid.

Lemma le_lin_fac :
  forall n : nat, n <= fac n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    apply le_0_n.
    replace (S n') with (plus 1 n') by reflexivity.
      apply le_plus.
        apply le_1_fac.
        replace n' with (mult n' 1) at 1.
          apply le_mult.
            apply le_n.
            apply le_1_fac.
          apply mult_1_r.
Qed.
(* end hide *)

Fixpoint pow2 (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => mult 2 (pow2 n')
end.

Notation "4" := (S (S (S (S 0)))).

Lemma le_exp_fac :
  forall n : nat, 4 <= n -> pow2 n <= fac n.
(* begin hide *)
Proof.
  induction 1; cbn.
    repeat constructor.
    rewrite plus_0_r. apply le_plus.
      assumption.
      replace (pow2 m) with (mult 1 (pow2 m)).
        apply le_mult.
          apply le_trans with 4; auto. repeat constructor.
          assumption.
        apply mult_1_l.
Qed.
(* end hide *)

(** * Współczynnik dwumianowy (TODO) *)

(** Zdefiniuj współczynnik dwumianowy. Jeżeli nie wiesz co to, to dobrze:
    będziesz miał więcej zabawy. W skrócie [binom n k] to ilość podzbiorów
    zbioru [n] elementowego, którego mają [k] elementów. *)

Require Import Recdef.

(* begin hide *)
Function binom (n k : nat) : nat :=
match n, k with
    | 0, 0 => 1
    | 0, _ => 0
    | _, 0 => 1 
    | S n', S k' => plus (binom n' k') (binom n' k)
end.
(* end hide *)

Fixpoint double (n : nat) : nat :=
match n with
    | 0 => 0
    | S n' => S (S (double n'))
end.

Lemma binom_0_r :
  forall n : nat, binom n 0 = 1.
(* begin hide *)
Proof.
  destruct n; cbn; reflexivity.
Qed.
(* end hide *)

Lemma binom_0_l :
  forall n : nat, binom 0 (S n) = 0.
(* begin hide *)
Proof.
  reflexivity.
Qed.
(* end hide *)

Lemma binom_1_r :
  forall n : nat, binom n 1 = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn', binom_0_r. cbn. reflexivity.
Qed.
(* end hide *)

Lemma binom_gt :
  forall n k : nat, n < k -> binom n k = 0.
(* begin hide *)
Proof.
  induction n as [| n'];
  destruct k as [| k']; cbn;
  try (inversion 1; trivial; fail); intro.
  rewrite !IHn'.
    reflexivity.
    apply lt_trans with (S n').
      apply le_n.
      assumption.
      apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma binom_diag :
  forall n : nat, binom n n = 1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn', binom_gt.
      reflexivity.
      constructor.
Qed.
(* end hide *)

Lemma binom_sym :
  forall n k : nat,
    k <= n -> binom n k = binom n (sub n k).
(* begin hide *)
Proof.
  intros n k. revert n.
  induction k as [| k']; cbn; intros.
    rewrite binom_0_r, binom_diag. reflexivity.
    induction n as [| n']; cbn.
      inversion H.
      rewrite pred_sub_S. destruct (sub n' k') eqn: Heq.
        rewrite IHk', Heq, binom_0_r, binom_gt.
          reflexivity.
          apply sub_0 in Heq. apply le_n_S. assumption.
          apply le_S_n. assumption.
        apply le_S_n in H. inversion H; subst; try rename m into n'.
          rewrite sub_diag in Heq. inversion Heq.
          rewrite plus_comm, IHn', IHk', Heq.
            reflexivity.
            assumption.
            apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma minus_sub :
  forall n m : nat,
    minus n m = sub n m.
(* begin hide *)
Proof.
  induction n as [| n'];
  destruct  m as [| m'];
  cbn.
    reflexivity.
    rewrite sub_0_l. cbn. reflexivity.
    reflexivity.
    rewrite IHn', pred_sub_S. reflexivity.
Qed.
(* end hide *)

Lemma binom_sym' :
  forall n k : nat,
    k <= n -> binom n k = binom n (minus n k).
(* begin hide *)
Proof.
  intros.
  rewrite minus_sub.
  apply binom_sym.
  assumption.
Qed.
(* end hide *)

Function binom' (n k : nat) : nat :=
match k with
    | 0    => 1
    | S k' =>
        match n with
            | 0    => 0
            | S n' => plus (binom' n' k') (binom' n' k)
        end
end.

Lemma binom_S_S :
  forall n k : nat,
    mult (S k) (binom (S n) (S k)) = mult (S n) (binom n k).
(* begin hide *)
Proof.
  intros.
  functional induction binom n k;
  cbn.
    admit.
Admitted.
(* end hide *)

Lemma binom_spec :
  forall n k : nat,
    k <= n -> mult (fac k) (mult (fac (sub n k)) (binom n k)) = fac n.
(* begin hide *)
Proof.
  induction n as [| n'].
    inversion 1; subst. cbn. reflexivity.
    destruct k as [| k'].
      intro. cbn. rewrite plus_0_r, mult_1_r. reflexivity.
      {
        intros. cbn [sub]. rewrite pred_sub_S. cbn [fac].
        replace (mult (mult (S k') _) _) with
                (mult (mult (S k') (binom (S n') (S k'))) (mult (fac k') (fac (sub n' k')))).
          rewrite binom_S_S. replace (mult (mult _ _) _) with
                                     (mult (S n') (mult (fac k') (mult (fac (sub n' k')) (binom n' k')))).
            rewrite IHn'.
              reflexivity.
              apply le_S_n. assumption.
            rewrite <- !mult_assoc. f_equal. rewrite (mult_comm (fac _)).
              rewrite <- !mult_assoc, mult_comm, <- !mult_assoc. reflexivity.
          rewrite <- !mult_assoc. f_equal. rewrite (mult_comm (binom _ _)).
              rewrite <- !mult_assoc, mult_comm, <- !mult_assoc. reflexivity.
      }
Qed.
(* end hide *)

(* begin hide *)
Module Div2. (* TODO: szybkie mnożenie *)

Require Import Div2.

Fixpoint evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

(*
Require Import ZArith.

Fixpoint quickMul (fuel n m : nat) : nat :=
match fuel with
    | 0 => 0
    | S fuel' => match n with
        | 0 => 0
        | _ => let res := quickMul fuel' (div2 n) m in
            if evenb n then plus res res else plus (plus m res) res
        end
end.

Time Eval compute in 430 * 110.
Time Eval compute in quickMul 1000 430 110.

Require Import Recdef.

Function qm (n m : nat) {measure id n} : nat :=
match n with
    | 0 => 0
    | _ => let r := qm (div2 n) m in
        if evenb n then 2 * r else m + 2 * r
end.
Proof.
Abort.

*)
End Div2.
(* end hide *)

(** * Wzory rekurencyjne (TODO) *)

(** * Sumy szeregów (TODO) *)

(** Udowodnij, że [2^0 + 2^1 + 2^2 + ... + 2^n = 2^(n + 1) - 1].
    Zaimplementuj w tym celu celu funkcję [f], która oblicza lewą
    stronę tego równania, a następnie pokaż, że [f n = 2^(n + 1) - 1]
    dla dowolnego [n : nat]. *)

(* begin hide *)
Fixpoint twos (n : nat) : nat :=
match n with
    | 0 => pow2 0
    | S n' => plus (twos n') (pow2 n)
end.
(* end hide *)

Lemma twos_spec :
  forall n : nat, twos n = minus (pow2 (S n)) 1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. rewrite !plus_0_r.
      generalize dependent (plus (pow2 n') (pow2 n')). destruct n.
        reflexivity.
        cbn. rewrite !minus_0_r. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: dziwna indukcja (ale o co tu miało chodzić?) *)
(* end hide *)

End MyNat.

(** * Dyskretny pierwiastek kwadratowy (TODO) *)

(* begin hide *)

(** TODO: dyskretny pierwiastek kwadratowy *)

Require Import Arith.
Require Import Lia Arith.

Lemma root : forall n : nat, {r : nat | r * r <= n < (S r) * (S r)}.
Proof.
  induction n as [| n'].
    exists 0. cbn; split.
      trivial.
      apply le_n.
    destruct IHn' as [r [H1 H2]].
    destruct (le_lt_dec ((S r) * (S r)) (S n')).
      exists (S r). cbn; split.
        cbn in l. assumption.
        cbn in *. apply lt_n_S.
        repeat match goal with
            | H : context [?x + S ?y] |- _ =>
                rewrite (plus_comm x (S y)) in H; cbn in H
            | H : context [?x * S ?y] |- _ =>
                rewrite (mult_comm x (S y)) in H; cbn in H
            | |- context [?x + S ?y] => rewrite (plus_comm x (S y)); cbn
            | |- context [?x * S ?y] => rewrite (mult_comm x (S y)); cbn
        end. lia.
      exists r. cbn; split.
        apply le_trans with n'.
          assumption.
          apply le_S. apply le_n.
        cbn in l. assumption.
Defined.

Definition root' (n : nat) : nat.
Proof.
  destruct (root n). exact x.
Defined.

Eval compute in root' 24.

Fixpoint div4 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | S (S (S (S n'))) => S (div4 n')
end.

Fixpoint nat_ind_4 (P : nat -> Prop) (H0 : P 0) (H1 : P 1) (H2 : P 2) (H3 : P 3)
    (H4 : forall n : nat, P n -> P (S (S (S (S n))))) (n : nat) : P n.
Proof.
  destruct n.
    exact H0.
    destruct n.
    exact H1.
      destruct n.
        exact H2.
        destruct n.
          exact H3.
          apply H4. apply nat_ind_4; assumption.
Defined.

Fixpoint nat_ind_3 (P : nat -> Prop) (H0 : P 0) (H1 : P 1) (H2 : P 2)
    (H3 : forall n : nat, P n -> P (S (S (S n)))) (n : nat) : P n.
Proof.
  destruct n.
    exact H0.
    destruct n.
    exact H1.
      destruct n.
        exact H2.
        apply H3. apply nat_ind_3; assumption.
Defined.

Require Import Wf.

Print well_founded_induction.

Lemma div4_lemma : forall n : nat,
    S (div4 n) < S (S (S (S n))).
Proof.
  induction n using nat_ind_4; cbn; lia.
Qed.

Lemma nat_ind_div4 (P : nat -> Type) (H0 : P 0)
    (Hdiv : forall n : nat, P (div4 n) -> P n) (n : nat) : P n.
Proof.
  apply (Fix lt_wf P). intros.
  destruct x.
    apply H0.
    destruct x.
      apply Hdiv. cbn. apply H0.
      destruct x.
        apply Hdiv. cbn. apply H0.
        destruct x.
          apply Hdiv. cbn. apply H0.
          apply Hdiv. cbn. apply X. apply div4_lemma.
Defined.

Ltac nat_cbn := repeat
match goal with
    | H : context [?x + S ?y] |- _ =>
        rewrite (plus_comm x (S y)) in H; cbn in H
    | H : context [?x * S ?y] |- _ =>
        rewrite (mult_comm x (S y)) in H; cbn in H
    | |- context [?x + S ?y] => rewrite (plus_comm x (S y)); cbn
    | |- context [?x * S ?y] => rewrite (mult_comm x (S y)); cbn
end;
repeat rewrite plus_0_r.

(* end hide *)