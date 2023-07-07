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

Require Import Recdef.
Require Import Setoid.

Require Div2 ZArith.

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
Notation "2" := (S (S 0)).

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

Lemma pred_S :
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
Fixpoint add (n m : nat) : nat :=
match n with
| 0 => m
| S n' => S (add n' m)
end.
(* end hide *)

Lemma add_0_l :
  forall n : nat, add 0 n = n.
(* begin hide *)
Proof.
  intro. cbn. trivial.
Qed.
(* end hide *)

Lemma add_0_r :
  forall n : nat, add n 0 = n.
(* begin hide *)
Proof.
  intro. induction n as [| n'].
    trivial.
    cbn. f_equal. assumption.
Qed.
(* end hide *)

Lemma add_S_l :
  forall n m : nat, add (S n) m = S (add n m).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; trivial.
Qed.
(* end hide *)

Lemma add_S_r :
  forall n m : nat, add n (S m) = S (add n m).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intro.
    trivial.
    rewrite IHn'. trivial.
Qed.
(* end hide *)

Lemma add_assoc :
  forall a b c : nat,
    add a (add b c) = add (add a b) c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn.
    trivial.
    intros. rewrite IHa'. trivial.
Qed.
(* end hide *)

Lemma add_comm :
  forall n m : nat, add n m = add m n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite add_0_r. trivial.
    induction m as [| m']; cbn.
      rewrite add_0_r. trivial.
      rewrite IHn'. rewrite <- IHm'. cbn. rewrite IHn'.
        trivial.
Qed.
(* end hide *)

Lemma add_no_absorbing_l :
  ~ exists a : nat, forall n : nat, add a n = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S 0)).
  rewrite add_comm in H. cbn in H. induction a as [| a'].
    inversion H.
    apply IHa'. inversion H. assumption.
Qed.
(* end hide *)

Lemma add_no_absorbing_r :
  ~ exists a : nat, forall n : nat, add n a = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S 0)).
  rewrite add_comm in H. cbn in H. induction a as [| a'].
    inversion H.
    apply IHa'. rewrite add_comm in *. cbn in *.
      inversion H. assumption.
Qed.
(* end hide *)

Lemma add_no_inverse_l :
  ~ forall n : nat, exists i : nat, add i n = 0.
(* begin hide *)
Proof.
  intro. destruct (H (S 0)) as [i H']. rewrite add_comm in H'.
  inversion H'.
Qed.
(* end hide *)

Lemma add_no_inverse_r :
  ~ forall n : nat, exists i : nat, add n i = 0.
(* begin hide *)
Proof.
  intro. destruct (H (S 0)) as [i H']. inversion H'.
Qed.
(* end hide *)

Lemma add_no_inverse_l_strong :
  forall n i : nat, n <> 0 -> add i n <> 0.
(* begin hide *)
Proof.
  destruct i; cbn; intros.
    assumption.
    inversion 1.
Qed.
(* end hide *)

Lemma add_no_inverse_r_strong :
  forall n i : nat, n <> 0 -> add n i <> 0.
(* begin hide *)
Proof.
  intros. rewrite add_comm. apply add_no_inverse_l_strong. assumption.
Qed.
(* end hide *)

(** ** Alternatywne definicje dodawania *)

(** Udowodnij, że poniższe alternatywne metody zdefiniowania dodawania
    rzeczywiście definiują dodawanie. *)

Fixpoint add' (n m : nat) : nat :=
match m with
| 0 => n
| S m' => S (add' n m')
end.

Lemma add'_is_add :
  forall n m : nat, add' n m = add n m.
(* begin hide *)
Proof.
  intros n m. generalize dependent n.
  induction m as [| m']; cbn; intros.
    rewrite add_0_r. trivial.
    rewrite IHm'. rewrite (add_comm n (S m')). cbn.
      rewrite add_comm. trivial.
Qed.
(* end hide *)

Fixpoint add'' (n m : nat) : nat :=
match n with
| 0 => m
| S n' => add'' n' (S m)
end.

Lemma add''_is_add :
  forall n m : nat, add'' n m = add n m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    intro. rewrite IHn', add_comm. cbn. rewrite add_comm. reflexivity.
Qed.
(* end hide *)

Fixpoint add''' (n m : nat) : nat :=
match m with
| 0 => n
| S m' => add''' (S n) m'
end.

Lemma add'''_is_add :
  forall n m : nat, add''' n m = add n m.
(* begin hide *)
Proof.
  intros n m. generalize dependent n.
  induction m as [| m']; cbn; intros.
    rewrite add_0_r. reflexivity.
    rewrite IHm'. cbn. rewrite (add_comm n (S _)). cbn.
      rewrite add_comm. reflexivity.
Qed.
(* end hide *)

(** ** Odejmowanie *)

(** Zdefiniuj odejmowanie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint sub (n m : nat) : nat :=
match n, m with
| 0, _ => 0
| _, 0 => n
| S n', S m' => sub n' m'
end.
(* end hide *)

Lemma sub_1_r :
  forall n : nat, sub n 1 = pred n.
(* begin hide *)
Proof.
  repeat (destruct n; cbn; trivial).
Qed.
(* end hide *)

Lemma sub_0_l :
  forall n : nat, sub 0 n = 0.
(* begin hide *)
Proof.
  cbn. trivial.
Qed.
(* end hide *)

Lemma sub_0_r :
  forall n : nat, sub n 0 = n.
(* begin hide *)
Proof.
  destruct n; trivial.
Qed.
(* end hide *)

Lemma sub_S_S :
  forall n m : nat,
    sub (S n) (S m) = sub n m.
(* begin hide *)
Proof.
  cbn. trivial.
Qed.
(* end hide *)

Lemma sub_diag:
  forall n : nat, sub n n = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; trivial.
Qed.
(* end hide *)

Lemma sub_add_l :
  forall n m : nat,
    sub (add n m) n = m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    apply sub_0_r.
    apply IHn'.
Qed.
(* end hide *)

Lemma sub_add_l' :
  forall n m : nat,
    sub (add n m) m = n.
(* begin hide *)
Proof.
  intros. rewrite add_comm. apply sub_add_l.
Qed.
(* end hide *)

Lemma sub_add_r :
  forall a b c : nat,
    sub a (add b c) = sub (sub a b) c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn; intros; [easy |].
  destruct b as [| b']; cbn.
  - now destruct c; cbn.
  - now rewrite IHa'.
Qed.
(* end hide *)

Lemma sub_exchange :
  forall a b c : nat,
    sub (sub a b) c = sub (sub a c) b.
(* begin hide *)
Proof.
  intros a b. generalize dependent a. induction b as [| b'].
    intros. repeat rewrite sub_0_r. trivial.
    intros a c. generalize dependent a. induction c as [| c'].
      intro. repeat rewrite sub_0_r. trivial.
      destruct a as [| a'].
        cbn. trivial.
        cbn in *. rewrite <- IHc'. rewrite IHb'. destruct a'; cbn.
          trivial.
          rewrite IHb'. trivial.
Restart.
  now intros; rewrite <- sub_add_r, add_comm, sub_add_r.
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

Lemma sub_comm_char :
  forall n m : nat,
    sub n m = sub m n -> n = m.
(* begin hide *)
Proof.
  induction n as [| n']; intros [| m'] Heq; cbn in *; [easy | inversion Heq.. |].
  now f_equal; apply IHn'.
Qed.
(* end hide *)

(** ** Odejmowanie v2 *)

Fixpoint sub' (n m : nat) : nat :=
match m with
| 0    => n
| S m' => pred (sub' n m')
end.

Lemma sub'_1_r :
  forall n : nat, sub' n 1 = pred n.
(* begin hide *)
Proof.
  reflexivity.
Qed.
(* end hide *)

Lemma sub'_pred_l :
  forall n m : nat,
    sub' (pred n) m = pred (sub' n m).
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    reflexivity.
    rewrite IHm'. reflexivity.
Qed.
(* end hide *)

Lemma sub'_0_l :
  forall n : nat,
    sub' 0 n = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma sub'_0_r :
  forall n : nat,
    sub' n 0 = n.
(* begin hide *)
Proof.
  reflexivity.
Qed.
(* end hide *)

Lemma sub'_S_S :
  forall n m : nat,
    sub' (S n) (S m) = sub' n m.
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    reflexivity.
    rewrite <- IHm'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma pred_sub'_S :
  forall n m : nat,
    pred (sub' (S n) m) = sub' n m.
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    reflexivity.
    rewrite IHm'. reflexivity.
Qed.

(* end hide *)
Lemma sub'_diag :
  forall n : nat,
    sub' n n = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite pred_sub'_S, IHn'. reflexivity.
Qed.
(* end hide *)

Lemma sub'_add_l :
  forall n m : nat,
    sub' (add n m) n = m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    intro. rewrite pred_sub'_S. apply IHn'.
Qed.
(* end hide *)

Lemma sub'_add_l' :
  forall n m : nat,
    sub' (add n m) m = n.
(* begin hide *)
Proof.
  intros. rewrite add_comm. apply sub'_add_l.
Qed.
(* end hide *)

Lemma sub'_add_r :
  forall a b c : nat,
    sub' a (add b c) = sub' (sub' a b) c.
(* begin hide *)
Proof.
  induction b as [| b']; cbn; intros.
    reflexivity.
    rewrite IHb', sub'_pred_l. reflexivity.
Qed.
(* end hide *)

Lemma sub'_exchange :
  forall a b c : nat,
    sub' (sub' a b) c = sub' (sub' a c) b.
(* begin hide *)
Proof.
  induction b as [| b']; cbn.
    reflexivity.
    intro. rewrite sub'_pred_l, IHb'. reflexivity.
Restart.
  now intros; rewrite <- sub'_add_r, add_comm, sub'_add_r.
Qed.
(* end hide *)

Lemma sub'_not_assoc :
  ~ forall a b c : nat,
      sub' a (sub' b c) = sub' (sub' a b) c.
(* begin hide *)
Proof.
  intro. specialize (H 1 1 1). cbn in H. inversion H.
Qed.
(* end hide *)

Lemma sub'_not_comm :
  ~ forall n m : nat,
      sub' n m = sub' m n.
(* begin hide *)
Proof.
  intro. specialize (H 1 0). cbn in H. inversion H.
Qed.
(* end hide *)

(** ** Mnożenie *)

(** Zdefiniuj mnożenie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint mul (n m : nat) : nat :=
match n with
| 0 => 0
| S n' => add m (mul n' m)
end.
(* end hide *)

Lemma mul_0_l :
  forall n : nat,
    mul 0 n = 0.
(* begin hide *)
Proof.
  cbn. reflexivity.
Qed.
(* end hide *)

Lemma mul_0_r :
  forall n : nat,
    mul n 0 = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    assumption.
Restart.
  induction n; trivial.
Qed.
(* end hide *)

Lemma mul_1_l :
  forall n : nat,
    mul 1 n = n.
(* begin hide *)
Proof.
  destruct n as [| n'].
    cbn. trivial.
    cbn. rewrite add_0_r. trivial.
Restart.
  destruct n; cbn; try rewrite add_0_r; trivial.
Qed.
(* end hide*)

Lemma mul_1_r :
  forall n : nat,
    mul n 1 = n.
(* begin hide *)
Proof.
  induction n.
    cbn. trivial.
    cbn. rewrite IHn. trivial.
Restart.
  induction n; cbn; try rewrite IHn; trivial.
Qed.
(* end hide *)

Lemma mul_comm :
  forall n m : nat,
    mul n m = mul m n.
(* begin hide *)
Proof.
  induction n as [| n']; intro.
    rewrite mul_0_l, mul_0_r. trivial.
    induction m as [| m'].
      rewrite mul_0_l, mul_0_r. trivial.
      cbn in *. rewrite IHn', <- IHm', IHn'. cbn.
        do 2 rewrite add_assoc. rewrite (add_comm n' m'). trivial.
Qed.
(* begin hide *)

Lemma mul_add_r :
  forall a b c : nat,
    mul a (add b c) = add (mul a b) (mul a c).
(* begin hide *)
Proof.
  induction a as [| a']; cbn; trivial.
  intros. rewrite IHa'. repeat rewrite add_assoc.
  f_equal. repeat rewrite <- add_assoc. f_equal.
  apply add_comm.
Qed.
(* end hide *)

Lemma mul_add_l :
  forall a b c : nat,
    mul (add a b) c = add (mul a c) (mul b c).
(* begin hide *)
Proof.
  intros. rewrite mul_comm. rewrite mul_add_r.
  f_equal; apply mul_comm.
Qed.
(* end hide *)

Lemma mul_sub_r :
  forall a b c : nat,
    mul a (sub b c) = sub (mul a b) (mul a c).
(* begin hide *)
Proof.
  induction a as [| a']; cbn; trivial.
  induction b as [| b'].
    intros. repeat rewrite mul_0_r. cbn. trivial.
    induction c as [| c'].
      rewrite mul_0_r. cbn. trivial.
      cbn. rewrite (mul_comm a' (S b')). cbn.
        rewrite (mul_comm a' (S c')). cbn.
        rewrite IHb'. repeat rewrite sub_add_r.
        f_equal. 2: apply mul_comm.
        replace (add b' (add a' _)) with (add a' (add b' (mul b' a'))).
          rewrite sub_exchange. rewrite sub_add_l.
            rewrite mul_comm. trivial.
          repeat rewrite add_assoc. rewrite (add_comm a' b'). trivial.
Qed.
(* end hide *)

Lemma mul_sub_l :
  forall a b c : nat,
    mul (sub a b) c = sub (mul a c) (mul b c).
(* begin hide *)
Proof.
  intros. rewrite mul_comm. rewrite mul_sub_r.
  f_equal; apply mul_comm.
Qed.
(* end hide *)

Lemma mul_assoc :
  forall a b c : nat,
    mul a (mul b c) = mul (mul a b) c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn; trivial.
  intros. rewrite mul_add_l.
  rewrite IHa'. trivial.
Qed.
(* end hide *)

Lemma mul_no_inverse_l :
  ~ forall n : nat, exists i : nat, mul i n = 1.
(* begin hide *)
Proof.
  intro. destruct (H (S 1)) as [i H']. rewrite mul_comm in H'.
  cbn in H'. rewrite add_0_r in H'. destruct i.
    inversion H'.
    cbn in H'. rewrite add_comm in H'. cbn in H'. inversion H'.
Qed.
(* end hide *)

Lemma mul_no_inverse_r :
  ~ forall n : nat, exists i : nat, mul n i = 1.
(* begin hide *)
Proof.
  intro. destruct (H (S 1)) as [i H']. cbn in H'.
  rewrite add_0_r in H'. destruct i.
    inversion H'.
    cbn in H'. rewrite add_comm in H'. cbn in H'. inversion H'.
Qed.
(* end hide *)

Lemma mul_no_inverse_l_strong :
  forall n i : nat, n <> 1 -> mul i n <> 1.
(* begin hide *)
Proof.
  induction i; cbn; intros.
    inversion 1.
    destruct n as [| [| n']]; cbn.
      rewrite mul_0_r. assumption.
      contradiction H. reflexivity.
      inversion 1.
Qed.
(* end hide *)

Lemma mul_no_inverse_r_strong :
  forall n i : nat, n <> 1 -> mul n i <> 1.
(* begin hide *)
Proof.
  intros. rewrite mul_comm.
  apply mul_no_inverse_l_strong. assumption.
Qed.
(* end hide *)

Lemma mul_2_l :
  forall n : nat, mul 2 n = add n n.
(* begin hide *)
Proof.
  intro. cbn. rewrite add_0_r. trivial.
Qed.
(* end hide *)

(** ** Potęgowanie *)

(** Zdefiniuj potęgowanie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint pow (n m : nat) : nat :=
match m with
| 0 => 1
| S m' => mul n (pow n m')
end.
(* end hide *)

Lemma pow_0_r :
  forall n : nat,
    pow n 0 = 1.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma pow_0_l :
  forall n : nat,
    pow 0 (S n) = 0.
(* begin hide *)
Proof.
  destruct n; cbn; reflexivity.
Qed.
(* end hide *)

Lemma pow_1_l :
  forall n : nat,
    pow 1 n = 1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; try rewrite add_0_r; trivial.
Qed.
(* end hide *)

Lemma pow_1_r :
  forall n : nat,
    pow n 1 = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; try rewrite mul_1_r; trivial.
Qed.
(* end hide *)

Lemma pow_no_neutr_l :
  ~ exists e : nat, forall n : nat, pow e n = n.
(* begin hide *)
Proof.
  destruct 1 as [e H]. specialize (H 0). cbn in H. inversion H.
Qed.
(* end hide *)

Lemma pow_no_absorbing_r :
  ~ exists a : nat, forall n : nat, pow n a = a.
(* begin hide *)
Proof.
  destruct 1 as [a H]. destruct a;
  [specialize (H 1) | specialize (H 0)]; inversion H.
Qed.
(* end hide *)

Lemma pow_add :
  forall a b c : nat,
    pow a (add b c) = mul (pow a b) (pow a c).
(* begin hide *)
Proof.
  induction b as [| b']; induction c as [| c']; cbn.
    reflexivity.
    rewrite add_0_r. reflexivity.
    rewrite add_0_r, mul_1_r. reflexivity.
    rewrite IHb'. cbn. rewrite !mul_assoc. reflexivity.
Qed.
(* end hide *)

Lemma pow_mul_l :
  forall a b c : nat,
    pow (mul a b) c = mul (pow a c) (pow b c).
(* begin hide *)
Proof.
  induction c as [| c']; cbn.
    trivial.
    rewrite IHc'. repeat rewrite mul_assoc. f_equal.
      repeat rewrite <- mul_assoc. f_equal. apply mul_comm.
Qed.
(* end hide *)

Lemma pow_pow_l :
  forall a b c : nat,
    pow (pow a b) c = pow a (mul b c).
(* begin hide *)
Proof.
  induction c as [| c']; cbn.
    rewrite mul_0_r. cbn. trivial.
    rewrite IHc', (mul_comm b (S c')). cbn.
      rewrite <- pow_add. rewrite mul_comm. trivial.
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

Lemma le_0_l :
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

Lemma le_add_l :
  forall a b c : nat,
    b <= c -> add a b <= add a c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn.
    trivial.
    intros. apply le_n_S. apply IHa'. assumption.
Qed.
(* end hide *)

Lemma le_add_r :
  forall a b c : nat,
    a <= b -> add a c <= add b c.
(* begin hide *)
Proof.
  intros. rewrite (add_comm a c), (add_comm b c).
  apply le_add_l. assumption.
Qed.
(* end hide *)

Lemma le_add :
  forall a b c d : nat,
    a <= b -> c <= d -> add a c <= add b d.
(* begin hide *)
Proof.
  induction 1.
    apply le_add_l.
    intros. cbn. apply le_S. apply IHle. assumption.
Qed.
(* end hide *)

Lemma le_sub_S_S :
  forall n m : nat,
    sub n (S m) <= sub n m.
(* begin hide *)
Proof.
  induction n as [| n'].
    cbn. constructor.
    destruct m; cbn.
      rewrite sub_0_r. do 2 constructor.
      apply IHn'.
Qed.
(* end hide *)

Lemma le_sub_l :
  forall a b c : nat,
    b <= c -> sub a c <= sub a b.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply le_trans with (sub a m).
      apply le_sub_S_S.
      assumption.
Qed.
(* end hide *)

Lemma le_sub_r :
  forall a b c : nat,
    a <= b -> sub a c <= sub b c.
(* begin hide *)
Proof.
  intros a b c. generalize dependent a. generalize dependent b.
  induction c as [| c'].
    intros. do 2 rewrite sub_0_r. trivial.
    destruct a, b; cbn; intro; trivial.
      apply le_0_l.
      inversion H.
      apply IHc'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma le_mul_l :
  forall a b c : nat,
    b <= c -> mul a b <= mul a c.
(* begin hide *)
Proof.
  induction a as [| a']; cbn.
    constructor.
    intros. apply le_add.
      assumption.
      apply IHa'. assumption.
Qed.
(* end hide *)

Lemma le_mul_r :
  forall a b c : nat,
    a <= b -> mul a c <= mul b c.
(* begin hide *)
Proof.
  intros. rewrite (mul_comm a c), (mul_comm b c).
  apply le_mul_l. assumption.
Qed.
(* end hide *)

Lemma le_mul :
  forall a b c d : nat,
    a <= b -> c <= d -> mul a c <= mul b d.
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    apply le_mul_l. assumption.
    change (mul a c) with (add 0 (mul a c)). apply le_add.
      apply le_0_l.
      apply IHle. assumption.
Qed.
(* end hide *)

Lemma le_add_exists :
  forall n m : nat,
    n <= m -> exists k : nat, add n k = m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    intros. exists m. trivial.
    intros. destruct (IHn' m) as [k Hk].
      apply le_Sn_m in H. assumption.
      destruct k; cbn.
        rewrite add_0_r in Hk. subst. cut False.
          inversion 1.
          apply (le_Sn_n m). assumption.
        exists k. rewrite add_comm in Hk. cbn in Hk.
          rewrite add_comm. assumption.
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
      change (pow (S a) b) with (add 0 (pow (S a) b)).
        rewrite (add_comm (pow (S a) m) _). apply le_add.
          apply le_0_l.
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
    intro. apply le_mul; auto.
Qed.
(* end hide *)

Lemma sub'_0 :
  forall n m : nat,
    sub' n m = 0 -> n <= m.
(* begin hide *)
Proof.
  intros n m. revert n.
  induction m as [| m']; cbn; intros.
    rewrite H. constructor.
    destruct n as [| n']; cbn.
      apply le_0_l.
      apply le_n_S, IHm'. rewrite pred_sub'_S in H. assumption.
Qed.
(* end hide *)

Lemma sub'_S_l :
  forall n m : nat,
    m <= n -> sub' (S n) m = S (sub' n m).
(* begin hide *)
Proof.
  induction m as [| m']; cbn; intros.
    reflexivity.
    rewrite IHm'.
      cbn. destruct (sub' n m') eqn: Heq.
        apply sub'_0 in Heq. edestruct le_Sn_n. eapply le_trans.
          exact H.
          assumption.
        cbn. reflexivity.
      eapply le_trans with (S m').
        do 2 constructor.
        assumption.
Qed.
(* end hide *)

Lemma le_sub'_l :
  forall n m : nat,
    sub' n m <= n.
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    constructor.
    apply le_trans with (sub' n m').
      apply le_pred.
      assumption.
Qed.
(* end hide *)

Lemma sub'_inv :
  forall n m : nat,
    m <= n -> sub' n (sub' n m) = m.
(* begin hide *)
Proof.
  intros n m. revert n.
  induction m as [| m']; intros.
    rewrite sub'_0_r, sub'_diag. reflexivity.
    induction n as [| n'].
      inversion H.
      cbn. rewrite pred_sub'_S, sub'_S_l, IHm'.
        reflexivity.
        apply le_S_n. assumption.
        apply le_sub'_l.
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

Lemma max_no_absorbing_l :
  ~ exists a : nat, forall n : nat, max a n = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S a)).
  induction a; inversion H. apply IHa. assumption.
Qed.
(* end hide *)

Lemma max_no_absorbing_r :
  ~ exists a : nat, forall n : nat, max n a = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. apply max_no_absorbing_l.
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
      apply le_0_l.
      destruct m; cbn.
        cbn in H. inversion H.
        cbn in H. apply le_n_S. apply IHn'. assumption.
Restart.
  split; generalize dependent m; induction n as [| n']; destruct m;
  cbn; trivial; try (inversion 1; fail); intro.
    apply IHn'. apply le_S_n. assumption.
    apply le_n.
    apply le_0_l.
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

Lemma div2_even :
  forall n : nat, div2 (mul 2 n) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r in *. rewrite ?add_S_r. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma div2_odd :
  forall n : nat, div2 (S (mul 2 n)) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r in *. rewrite ?add_S_r. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma mod2_even :
  forall n : nat, mod2 (mul 2 n) = 0.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r, ?add_S_r in *. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma mod2_odd :
  forall n : nat, mod2 (S (mul 2 n)) = 1.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r, ?add_S_r in *. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma div2_mod2_spec :
  forall n : nat, add (mul 2 (div2 n)) (mod2 n) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r in *. rewrite add_S_r. cbn. rewrite H. trivial.
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
  induction n using nat_ind_2; cbn; intros; try apply le_0_l.
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
  exists m : nat, mul k m = n.

Notation "k | n" := (divides k n) (at level 40).

(** [k] dzieli [n] jeżeli [n] jest wielokrotnością [k]. Udowodnij podstawowe
    właściwości tej relacji. *)

Lemma divides_0 :
  forall n : nat, n | 0.
(* begin hide *)
Proof.
  intro. red. exists 0. apply mul_0_r.
Qed.
(* end hide *)

Lemma not_divides_0 :
  forall n : nat, n <> 0 -> ~ 0 | n.
(* begin hide *)
Proof.
  unfold not, divides; intros. destruct H0 as [m Hm].
  rewrite mul_0_l in Hm. congruence.
Qed.
(* end hide *)

Lemma divides_1 :
  forall n : nat, 1 | n.
(* begin hide *)
Proof.
  intro. red. exists n. apply mul_1_l.
Qed.
(* end hide *)

Lemma divides_refl :
  forall n : nat, n | n.
(* begin hide *)
Proof.
  intro. red. exists 1. apply mul_1_r.
Qed.
(* end hide *)

Lemma divides_trans :
  forall k n m : nat, k | n -> n | m -> k | m.
(* begin hide *)
Proof.
  unfold divides; intros.
  destruct H as [c1 H1], H0 as [c2 H2].
  exists (mul c1 c2). rewrite mul_assoc. rewrite H1, H2. trivial.
Qed.
(* end hide *)

Lemma divides_add :
  forall k n m : nat, k | n -> k | m -> k | add n m.
(* begin hide *)
Proof.
  unfold divides; intros.
  destruct H as [c1 H1], H0 as [c2 H2].
  exists (add c1 c2). rewrite mul_add_r. rewrite H1, H2. trivial.
Qed.
(* end hide *)

Lemma divides_mul_l :
  forall k n m : nat, k | n -> k | mul n m.
(* begin hide *)
Proof.
  unfold divides. destruct 1 as [c H].
  exists (mul c m). rewrite mul_assoc. rewrite H. trivial.
Qed.
(* end hide *)

Lemma divides_mul_r :
  forall k n m : nat, k | m -> k | mul n m.
(* begin hide *)
Proof.
  intros. rewrite mul_comm. apply divides_mul_l. assumption.
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
    n <> 1 -> ~ prime (mul 2 n).
Proof.
  unfold prime, not; intros.
  destruct (H0 2).
    red. exists n. reflexivity.
    inversion H1.
    destruct n as [| [| n']]; inversion H1.
      apply H. reflexivity.
      rewrite add_comm in H3. inversion H3.
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
| S n' => mul n (fac n')
end.
(* end hide *)

Lemma le_1_fac :
  forall n : nat, 1 <= fac n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    constructor.
    replace 1 with (add 1 0).
      apply le_add.
        assumption.
        apply le_0_l.
      apply add_comm.
Qed.
(* end hide *)

Lemma le_lin_fac :
  forall n : nat, n <= fac n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    apply le_0_l.
    replace (S n') with (add 1 n') by reflexivity.
      apply le_add.
        apply le_1_fac.
        replace n' with (mul n' 1) at 1.
          apply le_mul.
            apply le_n.
            apply le_1_fac.
          apply mul_1_r.
Qed.
(* end hide *)

Notation "4" := (S (S (S (S 0)))).

Lemma le_exp_fac :
  forall n : nat, 4 <= n -> pow 2 n <= fac n.
(* begin hide *)
Proof.
  induction 1; cbn.
    repeat constructor.
    rewrite add_0_r. apply le_add.
      assumption.
      replace (pow 2 m) with (mul 1 (pow 2 m)).
        apply le_mul.
          apply le_trans with 4; auto. repeat constructor.
          assumption.
        apply mul_1_l.
Qed.
(* end hide *)

(** * Współczynnik dwumianowy (TODO) *)

(** Zdefiniuj współczynnik dwumianowy. Jeżeli nie wiesz co to, to dobrze:
    będziesz miał więcej zabawy. W skrócie [binom n k] to ilość podzbiorów
    zbioru [n] elementowego, którego mają [k] elementów. *)

(* begin hide *)
Function binom (n k : nat) : nat :=
match n, k with
| 0, 0 => 1
| 0, _ => 0
| _, 0 => 1
| S n', S k' => add (binom n' k') (binom n' k)
end.
(* TODO: być może przedefiniować współczynnik dwumianowy na bardziej ludzki *)
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
    k <= n -> binom n k = binom n (sub' n k).
(* begin hide *)
Proof.
  intros n k. revert n.
  induction k as [| k']; cbn; intros.
    rewrite binom_0_r, binom_diag. reflexivity.
    induction n as [| n']; cbn.
      inversion H.
      rewrite pred_sub'_S. destruct (sub' n' k') eqn: Heq.
        rewrite IHk', Heq, binom_0_r, binom_gt.
          reflexivity.
          apply sub'_0 in Heq. apply le_n_S. assumption.
          apply le_S_n. assumption.
        apply le_S_n in H. inversion H; subst; try rename m into n'.
          rewrite sub'_diag in Heq. inversion Heq.
          rewrite add_comm, IHn', IHk', Heq.
            reflexivity.
            assumption.
            apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma sub_sub' :
  forall n m : nat,
    sub n m = sub' n m.
(* begin hide *)
Proof.
  induction n as [| n'];
  destruct  m as [| m'];
  cbn.
    reflexivity.
    rewrite sub'_0_l. cbn. reflexivity.
    reflexivity.
    rewrite IHn', pred_sub'_S. reflexivity.
Qed.
(* end hide *)

Lemma binom_sym' :
  forall n k : nat,
    k <= n -> binom n k = binom n (sub n k).
(* begin hide *)
Proof.
  intros.
  rewrite sub_sub'.
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
  | S n' => add (binom' n' k') (binom' n' k)
  end
end.

Lemma binom_S_S :
  forall n k : nat,
    mul (S k) (binom (S n) (S k)) = mul (S n) (binom n k).
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
    k <= n -> mul (fac k) (mul (fac (sub' n k)) (binom n k)) = fac n.
(* begin hide *)
Proof.
  induction n as [| n'].
    inversion 1; subst. cbn. reflexivity.
    destruct k as [| k'].
      intro. cbn. rewrite add_0_r, mul_1_r. reflexivity.
      {
        intros. cbn [sub']. rewrite pred_sub'_S. cbn [fac].
        replace (mul (mul (S k') _) _) with
                (mul (mul (S k') (binom (S n') (S k'))) (mul (fac k') (fac (sub' n' k')))).
          rewrite binom_S_S. replace (mul (mul _ _) _) with
                                     (mul (S n') (mul (fac k') (mul (fac (sub' n' k')) (binom n' k')))).
            rewrite IHn'.
              reflexivity.
              apply le_S_n. assumption.
            rewrite <- !mul_assoc. f_equal. rewrite (mul_comm (fac _)).
              rewrite <- !mul_assoc, mul_comm, <- !mul_assoc. reflexivity.
          rewrite <- !mul_assoc. f_equal. rewrite (mul_comm (binom _ _)).
              rewrite <- !mul_assoc, mul_comm, <- !mul_assoc. reflexivity.
      }
Qed.
(* end hide *)

(* begin hide *)
Module MyDiv2. (* TODO: szybkie mnożenie *)

Import Div2 ZArith.

Fixpoint evenb (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S n') => evenb n'
end.

(*
Fixpoint quickMul (fuel n m : nat) : nat :=
match fuel with
| 0 => 0
| S fuel' =>
  match n with
  | 0 => 0
  | _ =>
    let res := quickMul fuel' (div2 n) m in
      if evenb n then add res res else add (add m res) res
  end
end.

Time Eval compute in 430 * 110.
Time Eval compute in quickMul 1000 430 110.

Function qm (n m : nat) {measure id n} : nat :=
match n with
| 0 => 0
| _ =>
  let r := qm (div2 n) m in
    if evenb n then 2 * r else m + 2 * r
end.
Proof.
Abort.

*)
End MyDiv2.
(* end hide *)

(** * Wzory rekurencyjne (TODO) *)

(** * Sumy szeregów (TODO) *)

(** Udowodnij, że [2^0 + 2^1 + 2^2 + ... + 2^n = 2^(n + 1) - 1].
    Zaimplementuj w tym celu celu funkcję [f], która oblicza lewą
    stronę tego równania, a następnie pokaż, że [f n = 2^(n + 1) - 1]
    dla dowolnego [n : nat]. *)

(* begin hide *)
Fixpoint pow2 (n : nat) : nat :=
match n with
| 0 => 1
| S n' => mul 2 (pow2 n')
end.

Fixpoint twos (n : nat) : nat :=
match n with
| 0 => pow2 0
| S n' => add (twos n') (pow2 n)
end.
(* end hide *)

Lemma twos_spec :
  forall n : nat, twos n = sub (pow2 (S n)) 1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. rewrite !add_0_r.
      generalize dependent (add (pow2 n') (pow2 n')). destruct n.
        reflexivity.
        cbn. rewrite !sub_0_r. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: dziwna indukcja (ale o co tu miało chodzić?) *)
(* end hide *)

End MyNat.

(** * Dyskretny pierwiastek kwadratowy (TODO) *)

(* begin hide *)

(** TODO: dyskretny pierwiastek kwadratowy *)

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
        cbn in *. rewrite <- Nat.succ_lt_mono.
        repeat match goal with
        | H : context [?x + S ?y] |- _ =>
          rewrite (add_comm x (S y)) in H; cbn in H
        | H : context [?x * S ?y] |- _ =>
          rewrite (mul_comm x (S y)) in H; cbn in H
        | |- context [?x + S ?y] => rewrite (add_comm x (S y)); cbn
        | |- context [?x * S ?y] => rewrite (mul_comm x (S y)); cbn
        end. lia.
      exists r. cbn; split.
        apply Nat.le_trans with n'.
          assumption.
          apply le_S. apply le_n.
        cbn in l. assumption.
Defined.

Definition root' (n : nat) : nat.
Proof.
  destruct (root n). exact x.
Defined.

Function root_v2 (n : nat) :=
match n with
| 0 => 0
| S n' =>
    let r := root_v2 n' in
      if Nat.ltb n (S r * S r)
      then r
      else S r
end.

Compute root' 50.
Compute root_v2 50.

Lemma root_v2_spec :
  forall (n : nat) (r := root_v2 n),
    r * r <= n < (S r) * (S r).
Proof.
  induction n as [| n']; [now cbn; lia |].
  destruct IHn' as [H1 H2].
  rewrite root_v2_equation.
  now destruct (Nat.ltb_spec (S n') (S (root_v2 n') * S (root_v2 n'))); lia.
Qed.

Ltac nat_cbn := repeat
match goal with
| H : context [?x + S ?y] |- _ =>
    rewrite (Nat.add_comm x (S y)) in H; cbn in H
| H : context [?x * S ?y] |- _ =>
  rewrite (Nat.mul_comm x (S y)) in H; cbn in H
| |- context [?x + S ?y] => rewrite (Nat.add_comm x (S y)); cbn
| |- context [?x * S ?y] => rewrite (Nat.mul_comm x (S y)); cbn
end;
repeat rewrite Nat.add_0_r.

(* end hide *)

(** * Zadania *)

(** **** Ćwiczenie (przeszukiwanko) *)

Section reverse.

Context
  (f : nat -> nat)
  (Hzero : f 0 = 0)
  (Hincreasing : forall m n, m < n -> f m < f n).

(** Udowodnij, że przy powyższych założeniach dla każdego [y : nat] istnieje [x : nat]
    takie, że [f x <= y <= f (S x)]. Zdefiniuj w tym celu funkcję [g : nat -> nat] i
    udowodnij, że spełnia ona specyfikację. *)

(* begin hide *)

(** **** Rozwiązanie *)

(** Intuicja: znajdź odwrotność funkcji [f]. Np. dla [f x = x * x] dostajemy
    dyskretny pierwiastek kwadratowy, dla [f x = 2 ^ x] dostajemy dyskretny
    logarytm binarny, etc.

    Definicja jest prosta:
    - jeżeli [y] to [0], to zwróć [0]
    - jeżeli [x] który znaleźliśmy dla [y - 1] jest dalej ok, to zwróć [x]
    - w przeciwnym wypadku zwróć [x + 1] *)

Fixpoint g (y : nat) : nat :=
match y with
| 0 => 0
| S y' =>
  let x := g y' in
    if Nat.ltb y (f (S x))
    then x
    else S x
end.

(** Dowód też jest prosty i ma taki sam kształt jak definicja funkcji [g]. *)
Lemma g_correct : forall y (x := g y), f x <= y < f (S x).
Proof.
  induction y as [| y']; simpl.
  - split.
    + rewrite Hzero. apply le_n.
    + rewrite <- Hzero at 1. apply Hincreasing. lia.
  - destruct (Nat.ltb_spec (S y') (f (S (g y')))).
    + split.
      * destruct IHy'. lia.
      * assumption.
    + split.
      * assumption.
      * destruct IHy'. assert (f (S (g y')) < f (S (S (g y')))).
        -- apply Hincreasing. lia.
        -- lia.
Qed.

(** Uwaga: komenda [Function] nie upraszcza powyższego dowodu ani trochę. *)

(* end hide *)

End reverse.