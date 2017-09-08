(** * X2: Arytmetyka Peano *)

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

(** Zdefiniuj liczby naturalne. *)

(* begin hide *)
Inductive nat : Set :=
    | O : nat
    | S : nat -> nat.
(* end hide *)

Notation "0" := O.
Notation "1" := (S 0).

(** Udowodnij właściwości zera i następnika. *)

Theorem neq_0_Sn : forall n : nat, 0 <> S n.
(* begin hide *)
Proof.
  do 2 intro. inversion H.
Qed.
(* end hide *)

Theorem neq_n_Sn : forall n : nat, n <> S n.
(* begin hide *)
Proof.
  induction n as [| n'].
    apply neq_0_Sn.
    intro. apply IHn'. inversion H. assumption.
Qed.
(* end hide *)

Theorem not_eq_S : forall n m : nat, n <> m -> S n <> S m.
(* begin hide *)
Proof.
  intros; intro. apply H. inversion H0. trivial.
Qed.
(* end hide *)

Theorem S_injective : forall n m : nat, S n = S m -> n = m.
(* begin hide *)
Proof.
  inversion 1. trivial.
Qed.
(* end hide *)

(** Zdefiniuj funkcję zwracającą poprzednik danej liczby naturalnej.
    Poprzednikiem [0] jest [0]. *)

(* begin hide *)
Definition pred (n : nat) : nat :=
match n with
    | 0 => 0
    | S n' => n'
end.
(* end hide *)

Theorem pred_0 : pred 0 = 0.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Theorem pred_Sn : forall n : nat, pred (S n) = n.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

(** Zdefiniuj dodawanie (rekurencyjnie po pierwszym argumencie) i
    udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint plus (n m : nat) : nat := match n with
    | 0 => m
    | S n' => S (plus n' m)
end.
(* end hide *)

Theorem plus_0_l : forall n : nat, plus 0 n = n.
(* begin hide *)
Proof.
  intro. simpl. trivial.
Qed.
(* end hide *)

Theorem plus_0_r : forall n : nat, plus n 0 = n.
(* begin hide *)
Proof.
  intro. induction n as [| n'].
    trivial.
    simpl. f_equal. assumption.
Qed.
(* end hide *)

Theorem plus_n_Sm : forall n m : nat, S (plus n m) = plus n (S m).
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intro.
    trivial.
    rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem plus_Sn_m : forall n m : nat, plus (S n) m = S (plus n m).
(* begin hide *)
Proof.
  induction n as [| n']; simpl; trivial.
Qed.
(* end hide *)

Theorem plus_assoc : forall a b c : nat,
    plus a (plus b c) = plus (plus a b) c.
(* begin hide *)
Proof.
  induction a as [| a']; simpl.
    trivial.
    intros. rewrite IHa'. trivial.
Qed.
(* end hide *)

Theorem plus_comm : forall n m : nat, plus n m = plus m n.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    rewrite plus_0_r. trivial.
    induction m as [| m']; simpl.
      rewrite plus_0_r. trivial.
      rewrite IHn'. rewrite <- IHm'. simpl. rewrite IHn'.
        trivial.
Qed.
(* end hide *)

Theorem no_annihilation_l :
    ~ exists a : nat, forall n : nat, plus a n = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S 0)).
  rewrite plus_comm in H. simpl in H. induction a as [| a'].
    inversion H.
    apply IHa'. inversion H. assumption.
Qed.
(* end hide *)

Theorem no_annihilation_r :
    ~ exists a : nat, forall n : nat, plus n a = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S 0)).
  rewrite plus_comm in H. simpl in H. induction a as [| a'].
    inversion H.
    apply IHa'. rewrite plus_comm in *. simpl in *.
      inversion H. assumption.
Qed.
(* end hide *)

Theorem no_inverse_l :
    ~ forall n : nat, exists i : nat, plus i n = 0.
(* begin hide *)
Proof.
  intro. destruct (H (S 0)) as [i H']. rewrite plus_comm in H'.
  inversion H'.
Qed.
(* end hide *)

Theorem no_inverse_r :
    ~ forall n : nat, exists i : nat, plus n i = 0.
(* begin hide *)
Proof.
  intro. destruct (H (S 0)) as [i H']. inversion H'.
Qed.
(* end hide *)

(** Pokaż, że [plus' n m = n + m] *)

Fixpoint plus' (n m : nat) : nat :=
match m with
    | 0 => n
    | S m' => plus' (S n) m'
end.

Theorem plus'_0_r : forall n : nat, plus' n 0 = n.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem plus'_S : forall n m : nat, plus' (S n) m = S (plus' n m).
(* begin hide *)
Proof.
  intros. generalize dependent n. induction m as [| m']; simpl; intros.
    trivial.
    rewrite IHm'. trivial.
Qed.
(* end hide *)

Theorem plus'_0_l : forall n : nat, plus' 0 n = n.
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    simpl. rewrite plus'_S. rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem plus'_comm : forall n m : nat, plus' n m = plus' m n.
(* begin hide *)
Proof.
  intros. generalize dependent n. induction m as [| m']; simpl; intros.
    rewrite plus'_0_l. trivial.
    rewrite IHm'. simpl. trivial.
Qed.
(* end hide *)

Theorem plus'_is_plus : forall n m : nat, plus' n m = plus n m.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intro.
    apply plus'_0_l.
    rewrite <- IHn'. rewrite plus'_S. trivial.
Qed.
(* end hide *)

(** Udowodnij powyższe twierdzenie bez używania lematów pomocniczych. *)

Theorem plus'_is_plus_no_lemmas : forall n m : nat,
    plus' n m = plus n m.
(* begin hide *)
Proof.
  intros n m. generalize dependent n.
  induction m as [| m']; simpl; intros.
    rewrite plus_0_r. trivial.
    rewrite IHm'. simpl. rewrite (plus_comm n (S _)). simpl.
      rewrite plus_comm. trivial.
Qed.
(* end hide *)

(** Udowodnij analogiczne twierdzenia dla [plus''] i [plus'''] *)

Fixpoint plus'' (n m : nat) : nat :=
match n with
    | 0 => m
    | S n' => plus'' n' (S m)
end.

Theorem plus''_is_plus : forall n m : nat, plus'' n m = plus n m.
(* begin hide *)
Proof.
  induction n as [| n']; simpl.
    trivial.
    intro. rewrite IHn'. rewrite plus_comm. simpl.
      rewrite plus_comm. trivial.
Qed.
(* end hide *)

Fixpoint plus''' (n m : nat) : nat :=
match m with
    | 0 => n
    | S m' => S (plus''' n m')
end.

Theorem plus'''_is_plus : forall n m : nat,
    plus''' n m = plus n m.
(* begin hide *)
Proof.
  intros n m. generalize dependent n.
  induction m as [| m']; simpl; intros.
    rewrite plus_0_r. trivial.
    rewrite IHm'. rewrite (plus_comm n (S m')). simpl.
      rewrite plus_comm. trivial.
Qed.
(* end hide *)

(** Zdefiniuj odejmowanie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint minus (n m : nat) : nat :=
match n, m with
    | 0, _ => 0
    | _, 0 => n
    | S n', S m' => minus n' m'
end.
(* end hide *)

Theorem minus_pred : forall n : nat,
    minus n 1 = pred n.
(* begin hide *)
Proof.
  repeat (destruct n; simpl; trivial).
Qed.
(* end hide *)

Theorem minus_0_l : forall n : nat,
    minus 0 n = 0.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem minus_0_r : forall n : nat,
    minus n 0 = n.
(* begin hide *)
Proof.
  destruct n; trivial.
Qed.
(* end hide *)

Theorem minus_S : forall n m : nat,
    minus (S n) (S m) = minus n m.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem minus_n : forall n : nat, minus n n = 0.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; trivial.
Qed.
(* end hide *)

Theorem minus_plus_l : forall n m : nat,
    minus (plus n m) n = m.
(* begin hide *)
Proof.
  induction n as [| n']; simpl.
    apply minus_0_r.
    apply IHn'.
Qed.
(* end hide *)

Theorem minus_plus_r : forall n m : nat,
    minus (plus n m) m = n.
(* begin hide *)
Proof.
  intros. rewrite plus_comm. apply minus_plus_l.
Qed.
(* end hide *)

Theorem minus_plus_distr : forall a b c : nat,
    minus a (plus b c) = minus (minus a b) c.
(* begin hide *)
Proof.
  induction a as [| a'].
    simpl. trivial.
    destruct b, c; simpl; trivial.
Restart.
  induction a; destruct b, c; simpl; trivial.
Qed.
(* end hide *)

Theorem minus_exchange : forall a b c : nat,
    minus (minus a b) c = minus (minus a c) b.
(* begin hide *)
Proof.
  intros a b. generalize dependent a. induction b as [| b'].
    intros. repeat rewrite minus_0_r. trivial.
    intros a c. generalize dependent a. induction c as [| c'].
      intro. repeat rewrite minus_0_r. trivial.
      destruct a as [| a'].
        simpl. trivial.
        simpl in *. rewrite <- IHc'. rewrite IHb'. destruct a'; simpl.
          trivial.
          rewrite IHb'. trivial.
Qed.

Theorem minus_not_assoc : ~ forall a b c : nat,
    minus a (minus b c) = minus (minus a b) c.
(* begin hide *)
Proof.
  intro. specialize (H 1 1 1). simpl in H. inversion H.
Qed.
(* end hide *)

Theorem minus_not_comm : ~ forall n m : nat,
    minus n m = minus m n.
(* begin hide *)
Proof.
  intro. specialize (H 1 0). simpl in H. inversion H.
Qed.
(* end hide *)

(** Zdefiniuj mnożenie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint mult (n m : nat) : nat :=
match n with
    | 0 => 0
    | S n' => plus m (mult n' m)
end.
(* end hide *)

Theorem mult_0_l : forall n : nat, mult 0 n = 0.
(* begin hide *)
Proof.
  induction n; trivial.
Qed.
(* end hide *)

Theorem mult_0_r : forall n : nat, mult n 0 = 0.
(* begin hide *)
Proof.
  induction n as [| n']; simpl.
    trivial.
    assumption.
Restart.
  induction n; trivial.
Qed.
(* end hide *)

Theorem mult_1_l : forall n : nat, mult 1 n = n.
(* begin hide *)
Proof.
  destruct n as [| n'].
    simpl. trivial.
    simpl. rewrite plus_0_r. trivial.
Restart.
  destruct n; simpl; try rewrite plus_0_r; trivial.
Qed.
(* end hide*)

Theorem mult_1_r : forall n : nat, mult n 1 = n.
(* begin hide *)
Proof.
  induction n.
    simpl. trivial.
    simpl. rewrite IHn. trivial.
Restart.
  induction n; simpl; try rewrite IHn; trivial.
Qed.
(* end hide *)

Theorem mult_comm : forall n m : nat,
    mult n m = mult m n.
(* begin hide *)
Proof.
  induction n as [| n']; intro.
    rewrite mult_0_l, mult_0_r. trivial.
    induction m as [| m'].
      rewrite mult_0_l, mult_0_r. trivial.
      simpl in *. rewrite IHn', <- IHm', IHn'. simpl.
        do 2 rewrite plus_assoc. rewrite (plus_comm n' m'). trivial.
Qed.
(* begin hide *)

Theorem mult_plus_distr_l : forall a b c : nat,
    mult a (plus b c) = plus (mult a b) (mult a c).
(* begin hide *)
Proof.
  induction a as [| a']; simpl; trivial.
  intros. rewrite IHa'. repeat rewrite plus_assoc.
  f_equal. repeat rewrite <- plus_assoc. f_equal.
  apply plus_comm.
Qed.
(* end hide *)

Theorem mult_plus_distr_r : forall a b c : nat,
    mult (plus a b) c = plus (mult a c) (mult b c).
(* begin hide *)
Proof.
  intros. rewrite mult_comm. rewrite mult_plus_distr_l.
  f_equal; apply mult_comm.
Qed.
(* end hide *)

Theorem mult_minus_distr_l : forall a b c : nat,
    mult a (minus b c) = minus (mult a b) (mult a c).
(* begin hide *)
Proof.
  induction a as [| a']; simpl; trivial.
  induction b as [| b'].
    intros. repeat rewrite mult_0_r. simpl. trivial.
    induction c as [| c'].
      rewrite mult_0_r. simpl. trivial.
      simpl. rewrite (mult_comm a' (S b')). simpl.
        rewrite (mult_comm a' (S c')). simpl.
        rewrite IHb'. repeat rewrite minus_plus_distr.
        f_equal. Focus 2. apply mult_comm.
        replace (plus b' (plus a' _)) with (plus a' (plus b' (mult b' a'))).
          rewrite minus_exchange. rewrite minus_plus_l.
            rewrite mult_comm. trivial.
          repeat rewrite plus_assoc. rewrite (plus_comm a' b'). trivial.
Qed.
(* end hide *)

Theorem mult_minus_distr_r : forall a b c : nat,
    mult (minus a b) c = minus (mult a c) (mult b c).
(* begin hide *)
Proof.
  intros. rewrite mult_comm. rewrite mult_minus_distr_l.
  f_equal; apply mult_comm.
Qed.
(* end hide *)

Theorem mult_assoc : forall a b c : nat,
    mult a (mult b c) = mult (mult a b) c.
(* begin hide *)
Proof.
  induction a as [| a']; simpl; trivial.
  intros. rewrite mult_plus_distr_r.
  rewrite IHa'. trivial.
Qed.
(* end hide *)

Theorem mult_no_inverse_l :
    ~ forall n : nat, exists i : nat, mult i n = 1.
(* begin hide *)
Proof.
  intro. destruct (H (S 1)) as [i H']. rewrite mult_comm in H'.
  simpl in H'. rewrite plus_0_r in H'. destruct i.
    inversion H'.
    simpl in H'. rewrite plus_comm in H'. simpl in H'. inversion H'.
Qed.
(* end hide *)

Theorem mult_no_inverse_r :
    ~ forall n : nat, exists i : nat, mult n i = 1.
(* begin hide *)
Proof.
  intro. destruct (H (S 1)) as [i H']. simpl in H'.
  rewrite plus_0_r in H'. destruct i.
    inversion H'.
    simpl in H'. rewrite plus_comm in H'. simpl in H'. inversion H'.
Qed.
(* end hide *)

Theorem mult_2_plus : forall n : nat, mult (S (S 0)) n = plus n n.
(* begin hide *)
Proof.
  intro. simpl. rewrite plus_0_r. trivial.
Qed.
(* end hide *)

(** Zdefiniuj relację "mniejszy lub równy" i udowodnij jej właściwości. *)

(* begin hide *)
Inductive le (n : nat) : nat -> Prop :=
    | le_n : le n n
    | le_S : forall m : nat, le n m -> le n (S m).
(* end hide *)

Notation "n <= m" := (le n m).

Theorem le_0_n : forall n : nat, 0 <= n.
(* begin hide *)
Proof.
  induction n as [| n'].
    apply le_n.
    apply le_S. assumption.
Qed.
(* end hide *)

Theorem le_n_Sm : forall n m : nat, n <= m -> n <= S m.
(* begin hide *)
Proof.
  apply le_S.
Qed.
(* end hide *)

Theorem le_Sn_m : forall n m : nat, S n <= m -> n <= m.
(* begin hide *)
Proof.
  induction m as [| m'].
    inversion 1.
    intros. inversion H.
      apply le_S, le_n.
      apply le_S, IHm'. assumption.
Qed.
(* end hide *)

Theorem le_n_S : forall n m : nat, n <= m -> S n <= S m.
(* begin hide *)
Proof.
  induction 1.
    apply le_n.
    apply le_S. assumption.
Qed.
(* end hide *)

Theorem le_S_n : forall n m : nat, S n <= S m -> n <= m.
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

Theorem le_Sn_n : forall n : nat, ~ S n <= n.
(* begin hide *)
Proof.
  induction n as [| n']; intro.
    inversion H.
    apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem le_refl : forall n : nat, n <= n.
(* begin hide *)
Proof.
  apply le_n.
Qed.
(* end hide *)

Theorem le_trans : forall a b c : nat,
    a <= b -> b <= c -> a <= c.
(* begin hide *)
Proof.
  induction 1.
    trivial.
    intro. apply IHle. apply le_Sn_m. assumption.
Qed.
(* end hide *)

Theorem le_antisym : forall n m : nat,
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

Theorem le_pred : forall n : nat, pred n <= n.
(* begin hide *)
Proof.
  destruct n; simpl; repeat constructor.
Qed.
(* end hide *)

Theorem le_n_pred : forall n m : nat,
    n <= m -> pred n <= pred m.
(* begin hide *)
Proof.
  inversion 1.
    constructor.
    simpl. apply le_trans with n.
      apply le_pred.
      assumption.
Qed.
(* end hide *)

Theorem no_le_pred_n : ~ forall n m : nat,
    pred n <= pred m -> n <= m.
(* begin hide *)
Proof.
  intro. specialize (H 1 0 (le_n 0)). inversion H.
Qed.
(* end hide *)

Theorem le_plus_l : forall a b c : nat,
    b <= c -> plus a b <= plus a c.
(* begin hide *)
Proof.
  induction a as [| a']; simpl.
    trivial.
    intros. apply le_n_S. apply IHa'. assumption.
Qed.
(* end hide *)

Theorem le_plus_r : forall a b c : nat,
    a <= b -> plus a c <= plus b c.
(* begin hide *)
Proof.
  intros. rewrite (plus_comm a c), (plus_comm b c).
  apply le_plus_l. assumption.
Qed.
(* end hide *)

Theorem le_plus : forall a b c d : nat,
    a <= b -> c <= d -> plus a c <= plus b d.
(* begin hide *)
Proof.
  induction 1.
    apply le_plus_l.
    intros. simpl. apply le_S. apply IHle. assumption.
Qed.
(* end hide *)

Theorem le_minus_S : forall n m : nat,
    minus n (S m) <= minus n m.
(* begin hide *)
Proof.
  induction n as [| n'].
    simpl. constructor.
    destruct m; simpl.
      rewrite minus_0_r. do 2 constructor.
      apply IHn'.
Qed.
(* end hide *)

Theorem le_minus_l : forall a b c : nat,
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

Theorem le_minus_r : forall a b c : nat,
    a <= b -> minus a c <= minus b c.
(* begin hide *)
Proof.
  intros a b c. generalize dependent a. generalize dependent b.
  induction c as [| c'].
    intros. do 2 rewrite minus_0_r. trivial.
    destruct a, b; simpl; intro; trivial.
      apply le_0_n.
      inversion H.
      apply IHc'. apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem le_mult_l : forall a b c : nat,
    b <= c -> mult a b <= mult a c.
(* begin hide *)
Proof.
  induction a as [| a']; simpl.
    constructor.
    intros. apply le_plus.
      assumption.
      apply IHa'. assumption.
Qed.
(* end hide *)

Theorem le_mult_r : forall a b c : nat,
    a <= b -> mult a c <= mult b c.
(* begin hide *)
Proof.
  intros. rewrite (mult_comm a c), (mult_comm b c).
  apply le_mult_l. assumption.
Qed.
(* end hide *)

Theorem le_mult : forall a b c d : nat,
    a <= b -> c <= d -> mult a c <= mult b d.
(* begin hide *)
Proof.
  induction 1; simpl; intro.
    apply le_mult_l. assumption.
    change (mult a c) with (plus 0 (mult a c)). apply le_plus.
      apply le_0_n.
      apply IHle. assumption.
Qed.
(* end hide *)

Theorem le_plus_exists : forall n m : nat,
    n <= m -> exists k : nat, plus n k = m.
(* begin hide *)
Proof.
  induction n as [| n']; simpl.
    intros. exists m. trivial.
    intros. destruct (IHn' m) as [k Hk].
      apply le_Sn_m in H. assumption.
      destruct k; simpl.
        rewrite plus_0_r in Hk. subst. cut False.
          inversion 1.
          apply (le_Sn_n m). assumption.
        exists k. rewrite plus_comm in Hk. simpl in Hk.
          rewrite plus_comm. assumption.
Qed.
(* end hide *)

(** Zdefiniuj minimum i maksimum oraz udowodnij ich właściwości. *)

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

Theorem min_0_l : forall n : nat, min 0 n = 0.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem min_0_r : forall n : nat, min n 0 = 0.
(* begin hide *)
Proof.
  destruct n; simpl; trivial.
Qed.
(* end hide *)

Theorem max_0_l : forall n : nat, max 0 n = n.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem max_0_r : forall n : nat, max n 0 = n.
(* begin hide *)
Proof.
  destruct n; simpl; trivial.
Qed.
(* end hide *)

Theorem min_le : forall n m : nat, n <= m -> min n m = n.
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    destruct m as [| m'].
      inversion 1.
      intro. simpl. f_equal. apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem max_le : forall n m : nat, n <= m -> max n m = m.
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    destruct m as [| m'].
      inversion 1.
      intro. simpl. f_equal. apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem min_assoc : forall a b c : nat,
    min a (min b c) = min (min a b) c.
(* begin hide *)
Proof.
  induction a as [| a'].
    trivial.
    destruct b, c; auto. simpl. rewrite IHa'. trivial.
Qed.
(* end hide *)

Theorem max_assoc : forall a b c : nat,
    max a (max b c) = max (max a b) c.
(* begin hide *)
Proof.
  induction a as [| a'].
    trivial.
    destruct b, c; auto. simpl. rewrite IHa'. trivial.
Qed.
(* end hide *)

Theorem min_comm : forall n m : nat, min n m = min m n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m; simpl; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem max_comm : forall n m : nat, max n m = max m n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m; simpl; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem min_refl : forall n : nat, min n n = n.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem max_refl : forall n : nat, max n n = n.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem min_no_neutr_l :
    ~ exists e : nat, forall n : nat, min e n = n.
(* begin hide *)
Proof.
  intro. destruct H as [e H]. specialize (H (S e)).
  induction e.
    inversion H.
    simpl in H. inversion H. apply IHe. assumption.
Qed.
(* end hide *)

Theorem min_no_neutr_r :
    ~ exists e : nat, forall n : nat, min n e = n.
(* begin hide *)
Proof.
  intro. apply min_no_neutr_l. destruct H as [e H].
  exists e. intro. rewrite min_comm. apply H.
Qed.
(* end hide *)

Theorem max_no_annihilator_l :
    ~ exists a : nat, forall n : nat, max a n = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. specialize (H (S a)).
  induction a; inversion H. apply IHa. assumption.
Qed.
(* end hide *)

Theorem max_no_annihilator_r :
    ~ exists a : nat, forall n : nat, max n a = a.
(* begin hide *)
Proof.
  intro. destruct H as [a H]. apply max_no_annihilator_l.
  exists a. intro. rewrite max_comm. apply H.
Qed.
(* end hide *)

Theorem is_it_true :
    (forall n m : nat, min (S n) m = S (min n m)) \/
    (~ forall n m : nat, min (S n) m = S (min n m)).
(* begin hide *)
Proof.
  right. intro. specialize (H 0 0). simpl in H. inversion H.
Qed.
(* end hide *)

(** Zdefiniuj potęgowanie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint pow (n m : nat) : nat :=
match m with
    | 0 => 1
    | S m' => mult n (pow n m')
end.

Theorem pow_0_l : forall n : nat, n <> 0 -> pow 0 n = 0.
(* begin hide *)
Proof.
  destruct n; simpl.
    intro. contradiction H. trivial.
    trivial.
Qed.
(* end hide *)

Theorem pow_0_r : forall n : nat, pow n 0 = 1.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem pow_1_l : forall n : nat, pow 1 n = 1.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; try rewrite plus_0_r; trivial.
Qed.
(* end hide *)

Theorem pow_1_r : forall n : nat, pow n 1 = n.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; try rewrite mult_1_r; trivial.
Qed.
(* end hide *)

Theorem pow_no_neutr_l :
    ~ exists e : nat, forall n : nat, pow e n = n.
(* begin hide *)
Proof.
  destruct 1 as [e H]. specialize (H 0). simpl in H. inversion H.
Qed.
(* end hide *)

Theorem pow_no_annihilator_r :
    ~ exists a : nat, forall n : nat, pow n a = a.
(* begin hide *)
Proof.
  destruct 1 as [a H]. destruct a;
  [specialize (H 1) | specialize (H 0)]; inversion H.
Qed.
(* end hide *)

Theorem le_pow_l : forall a b c : nat,
    a <> 0 -> b <= c -> pow a b <= pow a c.
(* begin hide *)
Proof.
  induction 2.
    constructor.
    destruct a; simpl.
      contradiction H. trivial.
      change (pow (S a) b) with (plus 0 (pow (S a) b)).
        rewrite (plus_comm (pow (S a) m) _). apply le_plus.
          apply le_0_n.
          assumption.
Qed.
(* end hide *)

Theorem le_pow_r : forall a b c : nat,
    a <= b -> pow a c <= pow b c.
(* begin hide *)
Proof.
  induction c as [| c']; simpl.
    constructor.
    intro. apply le_mult; auto.
Qed.
(* end hide *)

Theorem pow_mult : forall a b c : nat,
    pow (mult a b) c = mult (pow a c) (pow b c).
(* begin hide *)
Proof.
  induction c as [| c']; simpl.
    trivial.
    rewrite IHc'. repeat rewrite mult_assoc. f_equal.
      repeat rewrite <- mult_assoc. f_equal. apply mult_comm.
Qed.
(* end hide *)

Theorem pow_plus : forall a b c : nat,
    pow a (plus b c) = mult (pow a b) (pow a c).
(* begin hide *)
Proof.
  induction b as [| b']; induction c as [| c']; simpl.
    trivial.
    rewrite plus_0_r. trivial.
    rewrite plus_0_r, mult_1_r. trivial.
    rewrite IHb'. simpl. repeat rewrite mult_assoc. trivial.
Qed.
(* end hide *)

Theorem pow_pow : forall a b c : nat,
    pow (pow a b) c = pow a (mult b c).
(* begin hide *)
Proof.
  induction c as [| c']; simpl.
    rewrite mult_0_r. simpl. trivial.
    rewrite IHc', (mult_comm b (S c')). simpl.
      rewrite <- pow_plus. rewrite mult_comm. trivial.
Qed.
(* end hide *)

(** Zdefiniuj funkcję [leb], która sprawdza, czy [n <= m]. *)

(* begin hide *)
Fixpoint leb (n m : nat) : bool :=
match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
end.
(* end hide *)

Theorem leb_n : forall n : nat,
    leb n n = true.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; trivial.
Qed.
(* end hide *)

Theorem leb_spec : forall n m : nat,
    n <= m <-> leb n m = true.
(* begin hide *)
Proof.
  split; generalize dependent m.
    induction n as [| n'].
      simpl. trivial.
      destruct m; simpl; intro.
        inversion H.
        apply IHn'. apply le_S_n. assumption.
    induction n as [| n']; intros.
      apply le_0_n.
      destruct m; simpl.
        simpl in H. inversion H.
        simpl in H. apply le_n_S. apply IHn'. assumption.
Restart.
  split; generalize dependent m; induction n as [| n']; destruct m;
  simpl; trivial; try (inversion 1; fail); intro.
    apply IHn'. apply le_S_n. assumption.
    apply le_n.
    apply le_0_n.
    apply le_n_S. apply IHn'. assumption.
Qed.
(* end hide *)

(** Zdefiniuj funkcję [eqb], która sprawdza, czy [n = m]. *)

(* begin hide *)
Fixpoint eqb (n m : nat) : bool :=
match n, m with
    | 0, 0 => true
    | S n', S m' => eqb n' m'
    | _, _ => false
end.
(* end hide *)

Theorem eqb_spec : forall n m : nat,
    n = m <-> eqb n m = true.
(* begin hide *)
Proof.
  split; generalize dependent m; generalize dependent n.
    destruct 1. induction n; auto.
    induction n as [| n']; destruct m as [| m']; simpl; inversion 1; auto.
      f_equal. apply IHn'. assumption.
Qed.
(* end hide *)

(** Pokaż, że indukcję na liczbach naturalnych można robić "co 2".
    Wskazówka: taktyk można używać nie tylko do dowodzenia. Przypomnij
    sobie, że taktyki to programy, które generują dowody, zaś dowody
    są programami. Dzięki temu nic nie stoi na przeszkodzie, aby
    taktyki interpretować jako programy, które piszą inne programy.
    I rzeczywiście — w Coqu możemy używać taktyk do definiowania
    dowolnych termów. W niektórych przypadkach jest to bardzo częsta
    praktyka. *)

Fixpoint ind_by_2 (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
    (HSS : forall n : nat, P n -> P (S (S n))) (n : nat) : P n.
(* begin hide *)
Proof.
  destruct n.
    apply H0.
    destruct n.
      apply H1.
      apply HSS. apply ind_by_2; auto.
Qed.

End MyNat.

(* begin hide *)

Fixpoint factorial (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => mult n (factorial n')
end.

Function binom (n k : nat) : nat :=
match n, k with
    | 0, 0 => 1
    | 0, _ => 0
    | _, 0 => 1 
    | S n', S k' => plus (binom n' k') (binom n' k)
end.

Fixpoint double (n : nat) : nat :=
match n with
    | 0 => 0
    | S n' => S (S (double n'))
end.

Lemma binom_0_r :
  forall n : nat, binom n 0 = 1.
Proof.
  destruct n; simpl; trivial.
Qed.

Lemma binom_0_l :
  forall n : nat, binom 0 (S n) = 0.
Proof.
  simpl. trivial.
Qed.

Lemma binom_1_r :
  forall n : nat, binom n 1 = n.
Proof.
  induction n as [| n']; simpl.
    trivial.
    rewrite IHn', binom_0_r. simpl. trivial.
Qed.

Require Import Omega.

Lemma binom_gt :
  forall n k : nat, n < k -> binom n k = 0.
Proof.
  induction n as [| n']; destruct k as [| k']; simpl;
  try (inversion 1; trivial; fail); intro.
    rewrite !IHn'; omega.
Qed.

Lemma binom_n : forall n : nat, binom n n = 1.
Proof.
  induction n as [| n']; simpl.
    trivial.
    rewrite IHn', binom_gt; omega.
Qed.

Theorem binom_sym :
  forall n k : nat, k < n -> binom n k = binom n (minus n k).
Proof.
  induction n as [| n']; destruct k as [| k']; simpl; intros.
    trivial.
    omega.
    rewrite binom_n, binom_gt; omega.
    case_eq (n' - k'); intros; subst.
      omega.
      assert (S k' = n' - n). omega. rewrite <- H0, H1, <- !IHn'; omega.
Qed.

Goal forall n k : nat,
  k * binom (S n) (S k) = n * binom n k.
Proof.
  simpl.
  induction n as [| n']; destruct k as [| k']; simpl; try omega.
Abort.

Theorem binom_spec :
  forall n k : nat,
    k <= n -> fact k * fact (n - k) * binom n k = fact n.
Proof.
  induction n as [| n']; destruct k as [| k'].
    trivial.
    inversion 1.
    intros. simpl. omega.
    intros. simpl.
      rewrite !mult_plus_distr_r, !mult_plus_distr_l.
      rewrite IHn'; try omega.
      rewrite <- !plus_assoc. f_equal.
      rewrite <- 2!(mult_assoc k'). rewrite IHn'; try omega.
Restart.
  intros n k.
  functional induction binom n k; intros; simpl; try omega.
    destruct k. inversion y. omega.
    destruct n; simpl; omega.
    destruct n', k'; simpl in *; try omega.
      rewrite binom_0_r, <- plus_n_O, <- minus_n_O in *.
        assert (0 <= S n') by omega.
        specialize (IHn0 H0). rewrite mult_comm. simpl.
        rewrite binom_1_r. trivial.
      assert (S k' <= S n') by omega.
        specialize (IHn0 H0).
        rewrite <- !IHn0.
        rewrite !mult_plus_distr_r, !mult_plus_distr_l.
        repeat (rewrite ?mult_assoc, ?plus_assoc, ?IHn0). f_equal.
Abort.


(*Lemma double_plus : forall n, double n = n + n .
induction n as [| n'].
Case "n = 0". reflexivity.
Case "n = S n'". simpl. rewrite IHn'. rewrite plus_n_Sm. trivial.
Qed.

Theorem plus_ble_compat_l : forall a b c : nat,
ble_nat a b = true -> ble_nat (c + a) (c + b) = true.
induction a as [| a']; intros.
Case "a = 0". rewrite plus_0_r. induction c as [| c'].
    SCase "c = 0". apply H.
    SCase "c = S c'". simpl. apply IHc'.
Case "a = S a'". induction c as [| c'].
    SCase "c = 0". simpl plus. apply H.
    SCase "c = S c'". simpl. apply IHc'.
Qed.
*)

(*
Theorem plus_ble_compat_r : forall a b c : nat,
ble_nat a b = true -> ble_nat (a + c) (b + c) = true.
induction a as [| a']; intros.
Case "a = 0". induction c as [| c'].
    SCase "c = 0". apply H.
    SCase "c = S c'". rewrite <- plus_n_Sm, <- plus_n_Sm. apply IHc'.
Case "a = S a'". induction c as [| c'].
    SCase "c = 0". rewrite plus_0_r, plus_0_r. apply H.
    SCase "c = S c'". rewrite <- plus_n_Sm, <- plus_n_Sm. apply IHc'.
Qed.




Theorem ble_nat_refl : forall n : nat, true = ble_nat n n.
induction n as [| n'].
Case "n = 0". reflexivity.
Case "n = S n'". simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat, beq_nat 0 (S n) = false.
intro. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n : nat, beq_nat (S n) 0 = false.
intro. reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.
intros. rewrite H. trivial. Abort.

Theorem plus_id_exercise : forall a b c : nat, a = b -> b = c -> a + b = b + c.
intros. rewrite H, H0. trivial. Abort.

Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
intros. simpl. trivial. Abort.

Theorem mult_S_1 : forall n m : nat,  m = S n ->  m * (1 + n) = m * m.
intros. simpl. rewrite <- H. trivial. Abort.

Theorem plus_1_neq_0_firsttry : forall n : nat, beq_nat (n + 1) 0 = false.
intro.
destruct n as [| n']; reflexivity. Abort.

Theorem zero_nbeq_plus_1 : forall n : nat, beq_nat 0 (n + 1) = false.
intro.
destruct n; reflexivity.
Qed.

Theorem double_induction: forall (P : nat -> nat -> Prop), P 0 0 ->
(forall m : nat, P m 0 -> P (S m) 0) -> (forall n : nat, P 0 n -> P 0 (S n)) ->
(forall m n : nat, P m n -> P (S m) (S n)) -> forall m n : nat, P m n.
intros P P00 Im In IS. induction m as [| m']; intros.
Case "m = 0". induction n as [| n'].
    SCase "n = 0". apply P00.
    SCase "n = S n'". apply In. apply IHn'.
Case "m = S m'". induction n as [| n'].
    SCase "n = 0". apply Im. apply IHm'.
    SCase "n = S n'". apply IS. apply IHm'.
Qed.

Lemma S_not_eq : forall n m : nat, S n <> S m -> n <> m.
intros n m. unfold not. intros. apply H. apply f_equal. apply H0.
Qed.

Theorem beq_nat_0_l : forall n, beq_nat 0 n = true -> n = 0.
intros. induction n as [| n'].
Case "n = 0". trivial.
Case "n = S n'". inversion H.
Qed.

Theorem beq_nat_0_r : forall n, beq_nat n 0 = true -> n = 0.
intros. induction n as [| n'].
Case "n = 0". trivial.
Case "n = S n'". inversion H.
Qed.

Theorem beq_nat_refl : forall n : nat, true = beq_nat n n.
induction n as [| n'].
Case "n = 0". trivial.
Case "n = S n'". simpl. apply IHn'.
Qed.

Theorem beq_nat_true : forall n m : nat, beq_nat n m = true -> n = m.
induction n as [| n']; intros.
Case "n = 0". destruct m as [|m'].
    SCase "m = 0". trivial.
    SCase "m = S m'". inversion H.
Case "n = Sn'". destruct m as [| m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'". apply f_equal. apply IHn'. simpl in H. apply H.
Qed.

Lemma beq_nat_false : forall (n m : nat), beq_nat n m = false -> n <> m.
induction n as [| n']; intros.
Case "n = 0". destruct m as [| m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'". discriminate.
Case "n = S n'". destruct m as [| m'].
    SCase "m = 0". discriminate.
    SCase "m = S m'". simpl in H. apply IHn' in H. apply not_eq_S. apply H.
Qed.

Lemma beq_nat_false2 : forall (n m : nat), n <> m -> beq_nat n m = false.
induction n as [| n']; intros.
Case "n = 0". destruct m as [| m'].
    SCase "m = 0". contradiction H. trivial.
    SCase "m = S n'". reflexivity.
Case "n = S n'". destruct m as [| m'].
    SCase "m = 0". trivial.
    SCase "m = S m'". simpl. apply IHn'. apply S_not_eq in H. apply H.
Qed.

Theorem beq_nat_sym : forall (n m : nat), beq_nat n m = beq_nat m n.
intros. destruct (beq_nat n m) eqn: eq_n_m.
Case "n = m". apply beq_nat_true in eq_n_m. rewrite eq_n_m. apply beq_nat_refl.
Case "n =/= m". apply beq_nat_false in eq_n_m. symmetry. apply beq_nat_false2.
    unfold not. unfold not in eq_n_m. intro. apply eq_n_m. symmetry. apply H.
Qed.

Theorem beq_nat_trans : forall n m p : nat,
beq_nat n m = true -> beq_nat m p = true -> beq_nat n p = true.
intros. apply beq_nat_true in H. apply beq_nat_true in H0.
rewrite H, H0. symmetry; apply beq_nat_refl.
Qed.
*)

(* end hide *)

