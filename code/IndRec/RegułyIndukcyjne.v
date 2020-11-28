Require Import Coq.Program.Wf Arith NPeano Div2 Lia List.
Import ListNotations.

Fixpoint nat_ind_2 (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
    (H : forall n : nat, P n -> P (S (S n))) (n : nat) : P n :=
match n with
    | 0 => H0
    | 1 => H1
    | S (S n') => H n' (nat_ind_2 P H0 H1 H n')
end.

Lemma expand :
  forall (P : nat -> Prop) (n k : nat),
    ~ n <= k -> P (k + (n - k)) -> P n.
Proof.
  intros. replace n with (k + (n - k)).
    assumption.
    lia.
Defined.

Program Fixpoint nat_ind_k (k : nat) (P : nat -> Prop)
    (H : forall k' : nat, k' <= k -> P k')
    (H' : forall n : nat, P n -> P (S k + n))
    (n : nat) {measure n} : P n :=
match le_dec n k with
    | left n_le_k => H n n_le_k
    | right n_gt_k =>
        expand P n k n_gt_k (H' (n - S k) (nat_ind_k k P H H' (n - S k)))
end.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

Fixpoint even_ind' (P : nat -> Prop) (H0 : P 0)
    (HSS : forall n : nat, even n -> P n -> P (S (S n)))
    (n : nat) (Heven : even n) : P n.
Proof.
  destruct n as [| [| n']].
    assumption.
    inversion Heven.
    inversion Heven; subst. apply HSS.
      assumption.
      apply (even_ind' P H0 HSS n' H1).
Defined.

Program Fixpoint nat_ind_k' (k : nat) (Hk : k <> 0) (P : nat -> Prop)
    (H : forall k' : nat, k' <= k -> P k')
    (H' : forall n : nat, P n -> P (k + n))
    (n : nat) {measure n} : P n :=
match le_dec n k with
    | left n_le_k => H n n_le_k
    | right n_gt_k =>
        expand P n k n_gt_k (H' (n - k) (nat_ind_k' k Hk P H H' (n - k)))
end.
Next Obligation. lia. Defined.

Fixpoint nat_ind_8
  {P : nat -> Type}
  (P0 : P 0)
  (P1 : P 1)
  (P2 : P 2)
  (P3 : P 3)
  (P4 : P 4)
  (P5 : P 5)
  (P6 : P 6)
  (P7 : P 7)
  (P8plus : forall n : nat, P n -> P (8 + n))
  (n : nat) : P n :=
match n with
  | 0 => P0
  | 1 => P1
  | 2 => P2
  | 3 => P3
  | 4 => P4
  | 5 => P5
  | 6 => P6
  | 7 => P7
  | S (S (S (S (S (S (S (S n'))))))) =>
      P8plus n' (nat_ind_8 P0 P1 P2 P3 P4 P5 P6 P7 P8plus n')
end.

Lemma above_7 : forall n : nat,
    exists i j : nat, 8 + n = 3 * i + 5 * j.
Proof.
  assert (Hk : 8 <> 0). lia.
  induction n as [| n'] using (nat_ind_k' 8 Hk).
    destruct n. exists 1, 1. auto. destruct n. exists 3, 0. auto.
      destruct n. exists 0, 2. auto. destruct n. exists 2, 1. auto.
      destruct n. exists 4, 0. auto. destruct n. exists 1, 2. auto.
      destruct n. exists 3, 1. auto. destruct n. exists 0, 3. auto.
      destruct n. exists 2, 2. auto. repeat (inversion H; clear H; clear H0;
      rename H1 into H).
    destruct IHn' as [i [j H]]. exists (S i), (S j). lia.
Restart.
  assert (Hk : 8 <> 0) by inversion 1.
  induction n as [| n'] using (nat_ind_k' 8 ltac:(inversion 1)).
    destruct n as [| [| [| [| [| [| [| [| [| n']]]]]]]]].
      exists 1, 1. cbn. reflexivity.
      exists 3, 0. cbn. reflexivity.
      exists 0, 2. cbn. reflexivity.
      exists 2, 1. cbn. reflexivity.
      exists 4, 0. cbn. reflexivity.
      exists 1, 2. cbn. reflexivity.
      exists 3, 1. cbn. reflexivity.
      exists 0, 3. cbn. reflexivity.
      exists 2, 2. cbn. reflexivity.
      lia.
    destruct IHn' as (i & j & IH).
      exists (S i), (S j). lia.
Restart.
  apply nat_ind_8.
    exists 1, 1. cbn. reflexivity.
    exists 3, 0. cbn. reflexivity.
    exists 0, 2. cbn. reflexivity.
    exists 2, 1. cbn. reflexivity.
    exists 4, 0. cbn. reflexivity.
    exists 1, 2. cbn. reflexivity.
    exists 3, 1. cbn. reflexivity.
    exists 0, 3. cbn. reflexivity.
    intros n' (i & j & IH). exists (S i), (S j). lia.
Qed.

Fixpoint fac (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => n * fac n'
end.

Fixpoint f (n : nat) : nat :=
match n with
    | 0 => 0 * fac 0
    | S n' => f n' + n * fac n
end.

Lemma pred_lemma : forall n m : nat,
    1 <= n -> pred (n + m) = pred n + m.
Proof.
  induction 1; cbn; trivial.
Qed.

Lemma fact_ge_1 : forall n : nat, 1 <= fac n.
Proof.
  induction n as [| n']; cbn.
    trivial.
    eapply le_trans. eauto. apply le_plus_l.
Qed.

Lemma f_fac : forall n : nat, f n = pred (fac (1 + n)).
Proof.
  induction n as [| n'].
    cbn. trivial.
    cbn in *. rewrite pred_lemma. rewrite IHn'. trivial.
    eapply le_trans.
      apply fact_ge_1.
      apply le_plus_l.
Qed.

Inductive pos : Set :=
    | HJ : pos
    | Z : pos -> pos
    | J : pos -> pos.

Inductive bin : Set :=
    | HZ : bin
    | HP : pos -> bin.

Definition five : bin := HP (J (Z HJ)).
Definition answer : bin := HP (Z (J (Z (J (Z HJ))))).

Fixpoint pos_to_nat (p : pos) : nat :=
match p with
    | HJ => 1
    | Z p' => 2 * pos_to_nat p'
    | J p' => 1 + 2 * pos_to_nat p'
end.

Definition bin_to_nat (b : bin) : nat :=
match b with
    | HZ => 0
    | HP p => pos_to_nat p
end.

Program Fixpoint divmod (n k : nat) (H : k <> 0) {measure n} : nat * nat :=
match n with
    | 0 => (0, 0)
    | _ => if leb n k
        then (0, n)
        else let (d, m) := divmod (n - k) k H in (S d, m)
end.
Next Obligation. lia. Qed.

Lemma two_not_0 : 2 <> 0.
Proof. inversion 1. Qed.

Fixpoint divmod2 (n : nat) : nat * nat :=
match n with
    | 0 => (0, 0)
    | 1 => (0, 1)
    | S (S n') => let (a, b) := divmod2 n' in (S a, b)
end.

Compute divmod2 155.

Compute bin_to_nat answer.
Compute bin_to_nat (HP (Z (J (Z (J (Z HJ)))))).

Definition injective {A B : Type} (f : A -> B) : Prop :=
    forall x x' : A, f x = f x' -> x = x'.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a = b.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
    injective f /\ surjective f.

Lemma pos_to_nat_neq_0 : forall p : pos,
    pos_to_nat p <> 0.
Proof.
  induction p as [| p' | p']; cbn; inversion 1.
  apply IHp'. destruct (pos_to_nat p').
    trivial.
    inversion H.
Qed.

Lemma pos_to_nat_inj : injective pos_to_nat.
Proof.
  red. induction x as [| p1 | p1]; induction x' as [| p2 | p2]; cbn in *.
    trivial.
    lia.
    inversion 1. assert (pos_to_nat p2 = 0). lia.
      destruct (pos_to_nat_neq_0 _ H0).
    lia.
    intros. f_equal. apply IHp1. lia.
    intros. cut False; lia.
    inversion 1. assert (pos_to_nat p1 = 0). lia.
      destruct (pos_to_nat_neq_0 _ H0).
    lia.
    inversion 1. f_equal. apply IHp1. lia.
Qed.

Hint Resolve pos_to_nat_inj : core.

Lemma bin_to_nat_inj : injective bin_to_nat.
Proof.
  red. destruct x, x'; cbn; intro.
    trivial.
    cut False. inversion 1. eapply pos_to_nat_neq_0. eauto.
    cut False. inversion 1. eapply pos_to_nat_neq_0. eauto.
    f_equal. apply pos_to_nat_inj. assumption.
Qed.

Fixpoint succ (p : pos) : pos :=
match p with
    | HJ => Z HJ
    | J p' => Z (succ p')
    | Z p' => J p'
end.

Lemma pos_to_nat_S : forall (p : pos),
    pos_to_nat (succ p) = S (pos_to_nat p).
Proof.
  induction p as [| p' | p']; cbn; trivial.
    rewrite IHp'. cbn. rewrite <- plus_n_Sm. trivial.
Qed.

Lemma bin_to_nat_sur : surjective bin_to_nat.
Proof.
  red. intro n. induction n as [| n'].
    exists HZ. cbn. trivial.
    destruct IHn' as [b H]. destruct b; cbn in H.
      exists (HP HJ). cbn. rewrite H. trivial.
      destruct p; cbn in H.
        exists (HP (Z HJ)). cbn. rewrite H. trivial.
        exists (HP (succ (Z p))). cbn. rewrite H. trivial.
        exists (HP (succ (J p))). cbn. rewrite pos_to_nat_S.
          cbn. f_equal. rewrite <- plus_n_Sm. assumption.
Qed.

Lemma bin_to_nat_bij : bijective bin_to_nat.
Proof.
  unfold bijective. split.
    apply bin_to_nat_inj.
    apply bin_to_nat_sur.
Qed.

Lemma div2_even_inv :
  forall n m : nat,
    n + n = m -> n = div2 m.
Proof.
  intros n m. generalize dependent n.
  induction m using nat_ind_2; cbn; intros.
    destruct n; inversion H. trivial.
    destruct n; inversion H.
      rewrite <- plus_n_Sm in H1. inversion H1.
    rewrite <- (IHm (pred n)); destruct n; inversion H; cbn; trivial.
      rewrite <- plus_n_Sm in H. inversion H. trivial.
Qed.

Lemma div2_odd_inv :
  forall n m : nat,
    S (n + n) = m -> n = div2 m.
Proof.
  intros n m. generalize dependent n.
  induction m using nat_ind_2; cbn; intros.
    inversion H.
    inversion H. destruct n; inversion H1; trivial.
    rewrite <- (IHm (pred n)).
      destruct n.
        inversion H.
        cbn. trivial.
      destruct n.
        inversion H.
        cbn in *. rewrite <- plus_n_Sm in H. inversion H. trivial. 
Qed.

Lemma nat_ind_bin
  (P : nat -> Prop) (H0 : P 0)
  (Hx2 : forall n : nat, P n -> P (2 * n))
  (Hx2p1 : forall n : nat, P n -> P (1 + 2 * n))
  (n : nat) : P n.
Proof.
  pose proof bin_to_nat_sur. red in H. destruct (H n) as [b H'].
  rewrite <- H'. destruct b as [| p].
    cbn. apply H0.
    generalize dependent n. induction p as [| p' | p']; intros.
      cbn. change 1 with (1 + 2 * 0). apply Hx2p1. assumption.
      cbn in *. apply Hx2. apply (IHp' (div2 n)).
        apply div2_even_inv. rewrite <- plus_n_O in H'. assumption.
      cbn in *. apply Hx2p1. apply (IHp' (div2 n)).
        apply div2_odd_inv. rewrite <- plus_n_O in H'. assumption.
Qed.

Lemma even_dec :
  forall n : nat,
    {k : nat & {n = 2 * k} + {n = 1 + 2 * k}}.
Proof.
  induction n as [| n'].
    exists 0. left. trivial.
    destruct IHn' as [k [H | H]].
      exists k. right. rewrite H. trivial.
      exists (S k). left. rewrite H. cbn. lia.
Defined.

Inductive Tree (A : Type) : Type :=
    | Empty : Tree A
    | Node : A -> list (Tree A) -> Tree A.

Arguments Empty {A}.
Arguments Node {A} _ _.

Print Tree_ind.

Fixpoint Tree_ind_full (A : Type)
    (P : Tree A -> Prop) (Q : list (Tree A) -> Prop)
    (HPQ : forall ltr : list (Tree A), Q ltr -> forall x : A, P (Node x ltr))
    (HPEmpty : P Empty)
    (HQNil : Q nil)
    (HQCons : forall (h : Tree A) (t : list (Tree A)),
        P h -> Q t -> Q (cons h t)) (t : Tree A) : P t.
Proof.
  destruct t as [| v forest].
    apply HPEmpty.
    apply HPQ. induction forest as [| t' forest'].
      apply HQNil; auto.
      apply HQCons; auto. apply Tree_ind_full with Q; eauto.
Defined.

Fixpoint size {A : Type} (t : Tree A) : nat :=
match t with
    | Empty => 0
    | Node v forest => 1 +
        (fix size' {A : Type} (forest : list (Tree A)) : nat :=
        match forest with
            | nil => 0
            | cons t forest' => size t + size' forest'
        end) _ forest
end.

Fixpoint size_f {A : Type} (t : Tree A) : nat :=
match t with
    | Empty => 0
    | Node _ forest => S (fold_right (fun t' s => size t' + s) 0 forest)
end.

Fixpoint flatten' {A : Type} (t : Tree A) : list A :=
match t with
    | Empty => []
    | Node v forest => v :: fold_right (fun h t => flatten' h ++ t) [] forest
end.

Lemma flatten_preserves_size :
    forall (A : Type) (t : Tree A), size t = length (flatten' t).
Proof.
  intro.
  induction t using Tree_ind_full with
      (Q := fun (ltr : list (Tree A)) =>
          forall v : A, size (Node v ltr) =
          S (length (fold_right (fun h t => flatten' h ++ t) [] ltr))).
    rewrite IHt. cbn. trivial.
    cbn. trivial.
    cbn. trivial.
    cbn. intro. f_equal. rewrite app_length.
      specialize (IHt0 v). inversion IHt0. rewrite H0.
      rewrite IHt. trivial.
Qed.

Section nat_ind_dbl_pred.

Variable P : nat -> Prop.

Hypothesis H1 : P 1.
Hypothesis Hdbl : forall n : nat, P n -> P (n + n).
Hypothesis Hpred : forall n : nat, P (S n) -> P n.

Lemma H0 : P 0.
Proof. apply Hpred. assumption. Qed.

Lemma Hplus : forall n m : nat, P (n + m) -> P m.
Proof.
  induction n as [| n']; cbn.
    trivial.
    intros. apply IHn'. apply Hpred. assumption.
Qed.

Lemma HS : forall n : nat, P n -> P (S n).
Proof.
  induction n as [| n']; intro.
    assumption.
    apply Hplus with n'. replace (n' + S (S n')) with (S n' + S n').
      apply Hdbl. assumption.
      rewrite (plus_comm n'). cbn. f_equal. rewrite plus_comm. trivial.
Qed.

Lemma nat_ind_dbl_pred : forall n : nat, P n.
Proof.
  induction n as [| n'].
    apply H0.
    apply HS. assumption.
Qed.

End nat_ind_dbl_pred.

Goal forall n : nat, 2 * n <= pow 2 n.
Proof.
  induction n as [| n'].
    cbn. lia.
    cbn [pow]. destruct n'; cbn in *; lia.
Qed.

Lemma pow2_lin :
  forall n : nat,
    n < pow 2 n.
Proof.
  induction n as [| n']; cbn.
    constructor.
    lia.
Qed.

Goal forall n : nat, 2 * n < pow 2 (S n).
Proof.
  intros. cbn [pow].
  apply mult_S_lt_compat_l.
  apply pow2_lin.
Qed.

Definition maxL := fold_right max 0.
Definition sumL := fold_right plus 0.

Lemma t : forall l : list nat, sumL l <= length l * maxL l.
Proof.
  induction l as [| h t]; cbn.
    trivial.
    apply Plus.plus_le_compat.
      apply Max.le_max_l.
      apply Le.le_trans with (length t * maxL t).
        assumption.
        apply mult_le_compat.
          apply le_n.
          apply Max.le_max_r.
Qed.