(** * D1b: Arytmetyka Peano *)

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

Require Import Setoid.

Require ZArith.

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
  intros n m; revert n.
  induction m as [| m']; cbn; intros.
  - rewrite add_0_r. trivial.
  - rewrite IHm'. rewrite (add_comm n (S m')). cbn.
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

(** ** Alternatywna definicja odejmowania *)

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

Lemma sub_sub' :
  forall n m : nat,
    sub n m = sub' n m.
(* begin hide *)
Proof.
  induction n as [| n']; destruct  m as [| m']; cbn.
  - reflexivity.
  - rewrite sub'_0_l. cbn. reflexivity.
  - reflexivity.
  - rewrite IHn', pred_sub'_S. reflexivity.
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

Lemma mul_1_inv :
  forall n m : nat,
    mul n m = 1 -> n = 1 /\ m = 1.
(* begin hide *)
Proof.
  destruct n as [| n']; cbn.
  - now inversion 1.
  - destruct m as [| m']; cbn.
    + rewrite mul_0_r.
      now inversion 1.
    + inversion 1.
      destruct n', m'; inversion H1; cbn.
      now split.
Qed.
(* end hide *)

Lemma mul_2_l :
  forall n : nat, mul 2 n = add n n.
(* begin hide *)
Proof.
  intro. cbn. rewrite add_0_r. trivial.
Qed.
(* end hide *)

(** ** Alternatywna definicja mnożenia *)

Fixpoint mul' (n m : nat) : nat :=
match n with
| 0 => 0
| S n' => add (mul' n' m) m
end.

(** Ta definicja ma tę przyjemną właściwość, że lewostronne mnożenie przez 1
    oblicza się do n, a nie do [n + 0]. *)

Lemma mul'_1_l :
  forall n : nat, mul' 1 n = n.
Proof.
  reflexivity.
Qed.

Lemma mul'_spec :
  forall n m : nat,
    mul' n m = mul n m.
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now rewrite IHn', add_comm.
Qed.

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

(** * Minimum i maksimum *)

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

(** * Współczynnik dwumianowy (TODO) *)

(** Zdefiniuj współczynnik dwumianowy. Jeżeli nie wiesz co to, to dobrze:
    będziesz miał więcej zabawy. W skrócie [binom n k] to ilość podzbiorów
    zbioru [n] elementowego, którego mają [k] elementów. *)

(* begin hide *)
Fixpoint binom (n k : nat) : nat :=
match k with
| 0    => 1
| S k' =>
  match n with
  | 0    => 0
  | S n' => add (binom n' k') (binom n' k)
  end
end.
(* end hide *)

Lemma binom_0_r :
  forall n : nat,
    binom n 0 = 1.
(* begin hide *)
Proof.
  now intros [].
Qed.
(* end hide *)

Lemma binom_0_l :
  forall n : nat,
    binom 0 (S n) = 0.
(* begin hide *)
Proof.
  easy.
Qed.
(* end hide *)

Lemma binom_1_r :
  forall n : nat,
    binom n 1 = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; [easy |].
  now rewrite IHn', binom_0_r; cbn.
Qed.
(* end hide *)

Lemma binom_eq_SS :
  forall n k : nat,
    binom (S n) (S k) = add (binom n k) (binom n (S k)).
(* begin hide *)
Proof.
  easy.
Qed.
(* end hide *)

Lemma binom_add_r :
  forall n k : nat,
    binom n (add (S n) k) = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn in *; intros; [easy |].
  rewrite <- add_S_r at 2.
  now rewrite !IHn'; cbn.
Qed.
(* end hide *)

Lemma binom_diag :
  forall n : nat,
    binom n n = 1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; [easy |].
  rewrite IHn'.
  rewrite <- (add_0_r (S n')).
  now rewrite binom_add_r; cbn.
Qed.
(* end hide *)

Lemma binom_sym :
  forall n k : nat,
    binom (add n k) n = binom (add n k) k.
(* begin hide *)
Proof.
  intros n k; revert n.
  induction k as [| k']; cbn; intros.
  - now rewrite add_0_r, binom_diag, binom_0_r.
  - induction n as [| n']; cbn.
    + rewrite binom_diag; cbn.
      rewrite <- (add_0_r (S k')).
      now rewrite binom_add_r.
    + rewrite add_S_r, <- add_S_l.
      rewrite IHk'.
      rewrite add_S_r, <- add_S_l in IHn'.
      rewrite <- IHn'.
      now rewrite add_comm.
Qed.
(* end hide *)

Lemma binom_S_S :
  forall n k : nat,
    mul (S k) (binom (S n) (S k)) = mul (S n) (binom n k).
(* begin hide *)
Proof.
  intros.
Admitted.
(* end hide *)

(** * Wzory rekurencyjne (TODO) *)

(** * Sumy szeregów (TODO) *)

(** **** Ćwiczenie *)

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
| S n' => add (twos n') (pow 2 n)
end.
(* end hide *)

Lemma twos_spec :
  forall n : nat, twos n = sub (pow 2 (S n)) 1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. rewrite !add_0_r.
      generalize dependent (add (pow 2 n') (pow 2 n')). destruct n.
        reflexivity.
        cbn. rewrite !sub_0_r. reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij, że [2 * (1 + 2 + 3 + ... + n) = n * (n + 1)].
    Zaimplementuj w tym celu funkcję [sum_first]. *)

(* begin hide *)
Fixpoint sum_first (n : nat) : nat :=
match n with
| 0 => 0
| S n' => add (sum_first n') n
end.
(* end hide *)

Lemma sum_first_spec :
  forall n : nat,
    mul 2 (sum_first n) = mul n (S n).
(* begin hide *)
Proof.
  induction n as [| n']; [easy |].
  cbn [sum_first].
  rewrite mul_add_r.
  rewrite IHn'.
  rewrite <- mul_add_l.
  rewrite mul_comm, add_comm.
  now cbn [add].
Qed.
(* end hide *)

End MyNat.