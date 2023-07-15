(** * D2c: Rekursja strukturalna i customowe reguły indukcji [TODO] *)

Require Import Coq.Program.Wf Arith NPeano Div2 Lia List.
Import ListNotations.

(** * Rekursja strukturalna (TODO) *)

(** * Customowe reguły indukcji dla liczb naturalnych (TODO) *)

Fixpoint nat_ind_2
  (P : nat -> Prop)
  (H0 : P 0) (H1 : P 1)
  (H : forall n : nat, P n -> P (S (S n)))
  (n : nat) : P n :=
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

Program Fixpoint nat_ind_k
  (k : nat) (P : nat -> Prop)
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

Inductive Even : nat -> Prop :=
| Even0 : Even 0
| EvenSS : forall n : nat, Even n -> Even (S (S n)).

Fixpoint Even_ind'
  (P : nat -> Prop)
  (H0 : P 0)
  (HSS : forall n : nat, Even n -> P n -> P (S (S n)))
  (n : nat) (HEven : Even n) : P n.
Proof.
  destruct n as [| [| n']].
    assumption.
    inversion HEven.
    inversion HEven; subst. apply HSS.
      assumption.
      apply (Even_ind' P H0 HSS n' H1).
Defined.

Program Fixpoint nat_ind_k'
  (k : nat) (Hk : k <> 0) (P : nat -> Prop)
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

Fixpoint wut (n : nat) : nat :=
match n with
| 0 => 0 * fac 0
| S n' => wut n' + n * fac n
end.

Lemma pred_lemma :
  forall n m : nat,
    1 <= n -> pred (n + m) = pred n + m.
Proof.
  induction 1; cbn; trivial.
Qed.

Lemma fact_ge_1 :
  forall n : nat, 1 <= fac n.
Proof.
  induction n as [| n']; cbn.
    trivial.
    eapply Nat.le_trans. eauto. apply Nat.le_add_r.
Qed.

Lemma wut_fac :
  forall n : nat, wut n = pred (fac (1 + n)).
Proof.
  induction n as [| n'].
    cbn. trivial.
    cbn in *. rewrite pred_lemma. rewrite IHn'. trivial.
    eapply Nat.le_trans.
      apply fact_ge_1.
      apply Nat.le_add_r.
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

Program Fixpoint divmod
  (n k : nat) (H : k <> 0) {measure n} : nat * nat :=
match n with
| 0 => (0, 0)
| _ =>
  if Nat.leb n k
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

Lemma pos_to_nat_neq_0 :
  forall p : pos,
    pos_to_nat p <> 0.
Proof.
  induction p as [| p' | p']; cbn; inversion 1.
  apply IHp'. destruct (pos_to_nat p').
    trivial.
    inversion H.
Qed.

Lemma pos_to_nat_inj :
  injective pos_to_nat.
Proof.
  red. induction x as [| p1 | p1]; induction x' as [| p2 | p2]; cbn in *.
    reflexivity.
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

#[global] Hint Resolve pos_to_nat_inj : core.

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

Lemma pos_to_nat_S :
  forall (p : pos),
    pos_to_nat (succ p) = S (pos_to_nat p).
Proof.
  induction p as [| p' | p']; cbn; trivial.
    rewrite IHp'. cbn. rewrite <- plus_n_Sm. reflexivity.
Qed.

Lemma bin_to_nat_sur :
  surjective bin_to_nat.
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

Lemma bin_to_nat_bij :
  bijective bin_to_nat.
Proof.
  unfold bijective. split.
    apply bin_to_nat_inj.
    apply bin_to_nat_sur.
Qed.

Lemma div2_Even_inv :
  forall n m : nat,
    n + n = m -> n = Nat.div2 m.
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
    S (n + n) = m -> n = Nat.div2 m.
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
      cbn in *. apply Hx2. apply (IHp' (Nat.div2 n)).
        apply div2_Even_inv. rewrite <- plus_n_O in H'. assumption.
      cbn in *. apply Hx2p1. apply (IHp' (Nat.div2 n)).
        apply div2_odd_inv. rewrite <- plus_n_O in H'. assumption.
Qed.

Lemma Even_dec :
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

Fixpoint Tree_ind_full
  (A : Type) (P : Tree A -> Prop) (Q : list (Tree A) -> Prop)
  (HPQ : forall ltr : list (Tree A), Q ltr -> forall x : A, P (Node x ltr))
  (HPEmpty : P Empty)
  (HQNil : Q nil)
  (HQCons : forall (h : Tree A) (t : list (Tree A)),
      P h -> Q t -> Q (cons h t))
  (t : Tree A) : P t.
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
| Node _ forest => S (fold_right (fun t' s => size_f t' + s) 0 forest)
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
    rewrite IHt. cbn. reflexivity.
    cbn. reflexivity.
    cbn. reflexivity.
    cbn. intro. f_equal. rewrite app_length.
      specialize (IHt0 v). inversion IHt0. rewrite H0.
      rewrite IHt. reflexivity.
Qed.

Section nat_ind_dbl_pred.

Variable P : nat -> Prop.

Hypothesis H1 : P 1.
Hypothesis Hdbl : forall n : nat, P n -> P (n + n).
Hypothesis Hpred : forall n : nat, P (S n) -> P n.

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
      rewrite (Nat.add_comm n'). cbn. f_equal. rewrite Nat.add_comm. trivial.
Qed.

Lemma nat_ind_dbl_pred : forall n : nat, P n.
Proof.
  induction n as [| n'].
    apply Hpred. assumption.
    apply HS. assumption.
Qed.

End nat_ind_dbl_pred.

Lemma le_mul2_pow2 :
  forall n : nat,
    2 * n <= Nat.pow 2 n.
Proof.
  induction n as [| n'].
    cbn. lia.
    cbn [Nat.pow]. destruct n'; cbn in *; lia.
Qed.

Lemma pow2_lin :
  forall n : nat,
    n < Nat.pow 2 n.
Proof.
  induction n as [| n']; cbn.
    constructor.
    lia.
Qed.

Lemma lt_mul2_pow2_S :
  forall n : nat,
    2 * n < Nat.pow 2 (S n).
Proof.
  intros. cbn [Nat.pow].
  apply Nat.mul_lt_mono_pos_l.
  - apply Nat.lt_0_succ.
  - apply pow2_lin.
Qed.

Definition maxL := fold_right max 0.
Definition sumL := fold_right plus 0.

Lemma whatt : forall l : list nat, sumL l <= length l * maxL l.
Proof.
  induction l as [| h t]; cbn.
    trivial.
    apply Nat.add_le_mono.
      apply Nat.le_max_l.
      apply Nat.le_trans with (length t * maxL t).
        assumption.
        apply Nat.mul_le_mono.
          apply le_n.
          apply Nat.le_max_r.
Qed.

Fixpoint nat_ind_4
  (P : nat -> Type)
  (P0 : P 0)
  (P1 : P 1)
  (P2 : P 2)
  (P3 : P 3)
  (P4 : forall n : nat, P n -> P (4 + n))
  (n : nat) : P n :=
match n with
| 0 => P0
| 1 => P1
| 2 => P2
| 3 => P3
| S (S (S (S n'))) => P4 n' (nat_ind_4 P P0 P1 P2 P3 P4 n')
end.

Lemma two_and_five :
  forall n : nat,
    exists i j : nat, 4 + n = 2 * i + 5 * j.
Proof.
  induction n using nat_ind_4.
    exists 2, 0. cbn. reflexivity.
    exists 0, 1. cbn. reflexivity.
    exists 3, 0. cbn. reflexivity.
    exists 1, 1. cbn. reflexivity.
    destruct IHn as (i & j & IH).
      exists (2 + i), j. rewrite IH. lia.
Qed.

(** * Customowe reguły indukcji na listach (TODO) *)

From Typonomikon Require Import D5a.

(** Wyjaśnienia nadejdą już wkrótce. *)

Fixpoint list_ind_2
  {A : Type} (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (Hcons2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
  (l : list A) : P l :=
match l with
| [] => Hnil
| [x] => Hsingl x
| x :: y :: l' => Hcons2 x y l' (list_ind_2 P Hnil Hsingl Hcons2 l')
end.

Lemma list_ind_rev :
  forall (A : Type) (P : list A -> Prop)
    (Hnil : P [])
    (Hsnoc : forall (h : A) (t : list A), P t -> P (snoc h t))
      (l : list A), P l.
(* begin hide *)
Proof.
  intros. cut (forall l : list A, P (rev l)); intro.
    specialize (H (rev l)). rewrite <- rev_rev. assumption.
    induction l0 as [| h t]; cbn.
      assumption.
      apply Hsnoc. assumption.
Qed.
(* end hide *)

Lemma list_ind_app_l :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l' ++ l))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    assumption.
    apply (IH _ [h]). assumption.
Qed.
(* end hide *)

Lemma list_ind_app_r :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t] using list_ind_rev; cbn.
    assumption.
    rewrite snoc_app_singl. apply (IH t [h]). assumption.
Qed.
(* end hide *)

Lemma list_ind_app :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (IH : forall l l' : list A, P l -> P l' -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    assumption.
    apply (IH [h] t); auto.
Qed.
(* end hide *)

Lemma list_app_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (l l1 l2 : list A), P l -> P (l1 ++ l ++ l2)) ->
      forall l : list A, P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply H.
    specialize (H0 t [h] [] IHt). rewrite app_nil_r in H0.
      cbn in H0. assumption.
Qed.
(* end hide *)

(** ** Funkcja [rot2] *)

Fixpoint rot2 {A : Type} (l : list A) : list A :=
match l with
| [] => []
| [x] => [x]
| x :: y :: t => y :: x :: rot2 t
end.

Lemma rot2_involution :
  forall (A : Type) (l : list A),
    rot2 (rot2 l) = l.
Proof.
  intro. apply list_ind_2; cbn; intros.
    1-2: reflexivity.
    rewrite H. reflexivity.
Qed.

Inductive Rot2 {A : Type} : list A -> list A -> Prop :=
| Rot2_nil : Rot2 [] []
| Rot2_singl : forall x : A, Rot2 [x] [x]
| Rot2_cons2 :
    forall (x y : A) (l l' : list A),
      Rot2 l l' -> Rot2 (x :: y :: l) (y :: x :: l').

Lemma Rot2_correct :
  forall (A : Type) (l : list A),
    Rot2 l (rot2 l).
Proof.
  intro. apply list_ind_2; cbn; constructor. assumption.
Qed.

Lemma Rot2_complete :
  forall (A : Type) (l l' : list A),
    Rot2 l l' -> rot2 l = l'.
Proof.
  induction 1; cbn.
    1-2: reflexivity.
    rewrite IHRot2. reflexivity.
Qed.