(** * D1k: Arytmetyka Peano, część 2 *)

Require Import Recdef.

From Typonomikon Require Import D1b.

Module MyNat.

Export D1b.MyNat.

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

Lemma sub_le_0 :
  forall n m : nat,
    n <= m -> sub n m = 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      inversion H.
      apply IHn', le_S_n. assumption.
Qed.
(* end hide *)

Lemma sub_sub_r :
  forall n m : nat,
    n <= m -> sub n (sub n m) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      inversion H.
      rewrite sub_le_0.
        reflexivity.
        apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma sub_sub_r' :
  forall n m : nat,
    m <= n -> sub n (sub n m) = m.
(* begin hide *)
Proof.
  intros.
  rewrite !sub_sub'.
  now apply sub'_inv.
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

(** * Podzielność *)

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

Lemma binom_spec :
  forall n k : nat,
    k <= n -> mul (fac k) (mul (fac (sub' n k)) (binom n k)) = fac n.
(* begin hide *)
Proof.
  induction n as [| n']; [now inversion 1; subst; cbn |].
  destruct k as [| k']; [now cbn; rewrite add_0_r, mul_1_r |].
  intros.
  cbn [sub'].
  rewrite pred_sub'_S.
  cbn [fac].
  replace (mul (mul (S k') _) _)
     with (mul (mul (S k') (binom (S n') (S k'))) (mul (fac k') (fac (sub' n' k')))).
  - rewrite binom_S_S.
    replace (mul (mul _ _) _)
       with (mul (S n') (mul (fac k') (mul (fac (sub' n' k')) (binom n' k')))).
    + rewrite IHn'; [easy |].
      now apply le_S_n.
    + rewrite <- !mul_assoc.
      f_equal.
      now rewrite (mul_comm (fac _)), <- !mul_assoc, mul_comm, <- !mul_assoc.
  - rewrite <- !mul_assoc.
    f_equal.
    now rewrite (mul_comm (binom _ _)), <- !mul_assoc, mul_comm, <- !mul_assoc.
Qed.
(* end hide *)

End MyNat.

(** * Dyskretny pierwiastek kwadratowy (TODO) *)

(** TODO: dyskretny pierwiastek kwadratowy *)

Require Import Lia Arith.

Fixpoint root (n : nat) :=
match n with
| 0 => 0
| S n' =>
    let r := root n' in
      if Nat.ltb n (S r * S r)
      then r
      else S r
end.

Compute root 50.

Lemma root_spec :
  forall (n : nat) (r := root n),
    r * r <= n < (S r) * (S r).
Proof.
  induction n as [| n']; [now cbn; lia |].
  destruct IHn' as [H1 H2].
  cbn [root].
  now destruct (Nat.ltb_spec (S n') (S (root n') * S (root n'))); lia.
Qed.

Lemma le_diag_inv :
  forall n m : nat,
    n * n <= m * m -> n <= m.
Proof.
  intros n m Hle.
  apply Decidable.not_not; [admit |].
  intros Hlt.
  rewrite <- Nat.lt_nge in Hlt.
  assert (m * m < n * n).
  {
    now apply Nat.square_lt_mono_nonneg; [lia |].
  }
  lia.
Admitted.

Lemma lt_diag_inv :
  forall n m : nat,
    n * n < m * m -> n < m.
Proof.
  intros n m Hlt.
  apply Decidable.not_not; [admit |].
  intros Hle.
  rewrite <- Nat.le_ngt in Hle.
  assert (m * m <= n * n).
  {
    now apply Nat.square_le_mono_nonneg; [lia |].
  }
  lia.
Admitted.

Lemma root_spec' :
  forall (n : nat) (r := root (n * n)),
    r = n.
Proof.
  intros n r.
  pose proof (Hspec := root_spec (n * n)).
  assert (Hle : r <= n) by apply le_diag_inv, Hspec.
  assert (Hlt : n < S r) by apply lt_diag_inv, Hspec.
  lia.
Qed.

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
    + now rewrite Hzero.
    + rewrite <- Hzero at 1.
      now apply Hincreasing; lia.
  - destruct (Nat.ltb_spec (S y') (f (S (g y')))).
    + split; [| easy].
      now destruct IHy'; lia.
    + split; [easy |].
      destruct IHy'.
      assert (f (S (g y')) < f (S (S (g y')))) by (apply Hincreasing; lia).
      now lia.
Qed.

(** Uwaga: komenda [Function] nie upraszcza powyższego dowodu ani trochę. *)

(* end hide *)

End reverse.