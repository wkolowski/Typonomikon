(** * D5c: Listy: relacje *)

From Typonomikon Require Export D5b.

(** * Relacje między listami *)

(* begin hide *)
(* TODO: zrób coś z tym (dziwna relacja [bool_le]) *)
Inductive bool_le : bool -> bool -> Prop :=
| ble_refl : forall b : bool, bool_le b b
| ble_false_true : bool_le false true.

(*
Definition bool_le (b1 b2 : bool) : Prop :=
match b1, b2 with
| false, _ => True
| true, false => False
| true, true => True
end.
*)
(* end hide *)

(** ** Listy jako termy *)

(** Zdefiniuj relację [Sublist]. Zdanie [Sublist l1 l2] zachodzi, gdy
    [l2] jest podtermem listy [l1], tzn. jej ogonem, ogonem ogona,
    ogonem ogona ogona etc.

    Przykład: *)

(** [Sublist [4; 5] [1; 2; 3; 4; 5]] zachodzi. *)

(** [Sublist [3; 4] [1; 2; 3; 4; 5]] nie zachodzi. *)

(* begin hide *)
Inductive Sublist {A : Type} : list A -> list A -> Prop :=
| Sublist_direct :
    forall (h : A) (t : list A), Sublist t (h :: t)
| Sublist_cons :
    forall (x : A) (l1 l2 : list A),
      Sublist l1 l2 -> Sublist l1 (x :: l2).
(* end hide *)

Lemma Sublist_length :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> length l1 < length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_n.
    apply Nat.lt_lt_succ_r. assumption.
Qed.
(* end hide *)

Lemma Sublist_cons_l :
  forall (A : Type) (x : A) (l : list A), ~ Sublist (x :: l) l.
(* begin hide *)
Proof.
  repeat intro. apply Sublist_length in H. cbn in H. lia.
Qed.
(* end hide *)

Lemma Sublist_cons_l' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Sublist (x :: l1) l2 -> Sublist l1 l2.
(* begin hide *)
Proof.
  intros until 1. revert l1 H.
  induction l2 as [| h t]; cbn; intros.
    inv H.
    inv H.
      do 2 constructor.
      constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Sublist_nil_cons :
  forall (A : Type) (x : A) (l : list A), Sublist [] (x :: l).
(* begin hide *)
Proof.
  intros A x l. revert x.
  induction l as [| h t]; cbn; constructor; apply IHt.
Qed.
(* end hide *)

Lemma Sublist_irrefl :
  forall (A : Type) (l : list A), ~ Sublist l l.
(* begin hide *)
Proof.
  repeat intro. apply Sublist_length in H. lia.
Qed.
(* end hide *)

Lemma Sublist_antisym :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> ~ Sublist l2 l1.
(* begin hide *)
Proof.
  repeat intro.
  apply Sublist_length in H.
  apply Sublist_length in H0.
  lia.
Qed.
(* end hide *)

Lemma Sublist_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Sublist l1 l2 -> Sublist l2 l3 -> Sublist l1 l3.
(* begin hide *)
Proof.
  intros until 1. revert l3.
  induction H; intros.
    apply Sublist_cons_l' in H. assumption.
    apply IHSublist. apply Sublist_cons_l' in H0. assumption.
Qed.
(* end hide *)

Lemma Sublist_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Sublist l1 l2 -> Sublist (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Sublist_snoc_inv :
  forall (A : Type) (x y : A) (l1 l2 : list A),
    Sublist (snoc x l1) (snoc y l2) -> Sublist l1 l2 /\ x = y.
(* begin hide *)
Proof.
  intros.
  remember (snoc x l1) as l1'.
  remember (snoc y l2) as l2'.
  revert l1 l2 Heql1' Heql2'.
  induction H; cbn; intros; subst.
    destruct l2 as [| h2 t2]; inv Heql2'.
      apply (f_equal isEmpty) in H1. rewrite isEmpty_snoc in H1. inv H1.
      apply snoc_inv in H1. destruct H1; subst. split; constructor.
    destruct l3 as [| h3 t3]; cbn in *.
      inv Heql2'. inv H.
      inv Heql2'. destruct (IHSublist _ _ eq_refl eq_refl); subst.
        split; constructor. assumption.
Qed.
(* end hide *)

Lemma Sublist_app_l :
  forall (A : Type) (l1 l2 : list A),
    l1 <> [] -> Sublist l2 (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    contradiction.
    destruct t as [| h' t']; cbn.
      constructor.
      constructor. apply IHt. inversion 1.
Qed.
(* end hide *)

Lemma Sublist_app_l' :
  forall (A : Type) (l1 l2 l3 : list A),
    Sublist l1 l2 -> Sublist l1 (l3 ++ l2).
(* begin hide *)
Proof.
  intros until 1. revert l1 l2 H.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Sublist_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Sublist l1 l2 -> Sublist (l1 ++ l3) (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; intros; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Sublist_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Sublist l1 l2 -> Sublist (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Sublist_join :
  forall (A : Type) (l1 l2 : list (list A)),
    ~ elem [] l2 -> Sublist l1 l2 -> Sublist (join l1) (join l2).
(* begin hide *)
Proof.
  induction 2; cbn.
    rewrite elem_cons' in H. destruct h.
      firstorder.
      apply Sublist_app_l. inversion 1.
    apply Sublist_app_l'. apply IHSublist.
      intro. apply H. right. assumption.
Qed.
(* end hide *)

Lemma Sublist_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Sublist (replicate n x) (replicate m x) <-> n < m.
(* begin hide *)
Proof.
  split.
    revert n. induction m as [| m']; cbn; intros.
      inv H.
      destruct n as [| n']; cbn in *.
        apply Nat.lt_0_succ.
        rewrite <- Nat.succ_lt_mono. apply IHm'. inv H.
          constructor.
          apply Sublist_cons_l' in H2. assumption.
    intro. assert (exists k : nat, m = n + S k).
      revert n H. induction m as [| m']; cbn; intros.
        inv H.
        destruct n as [| n'].
          exists m'. reflexivity.
          apply Nat.succ_lt_mono in H. destruct (IHm' _ H) as (k & IH). subst.
            exists k. rewrite <- ?plus_n_Sm. cbn. reflexivity.
      destruct H0 as (k & H'). subst.
        rewrite <- Nat.add_succ_comm, replicate_add_comm, replicate_plus.
          apply Sublist_app_l'. cbn. constructor.
Qed.
(* end hide *)

Lemma Sublist_replicate' :
  forall (A : Type) (n m : nat) (x y : A),
    Sublist (replicate n x) (replicate m y) <->
    n < m /\ (n <> 0 -> x = y).
(* begin hide *)
Proof.
  split.
    revert m x y. induction n as [| n'], m as [| m']; intros.
      inv H.
      split.
        apply Nat.lt_0_succ.
        intro. contradiction.
      inv H.
      rewrite <- ?snoc_replicate in H. apply Sublist_snoc_inv in H.
        destruct H. destruct (IHn' _ _ _ H); subst. split.
          now apply Nat.succ_lt_mono in H1.
          reflexivity.
    destruct 1. destruct n as [| n'].
      destruct m as [| m'].
        inv H.
        cbn. apply Sublist_nil_cons.
      specialize (H0 ltac:(inversion 1)). subst. rewrite Sublist_replicate.
        assumption.
Qed.
(* end hide *)

Lemma Sublist_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Sublist (iterate f n x) (iterate f m x) ->
      n = 0 \/ n = m \/ (n <= m /\ f x = x).
(* begin hide *)
Proof.
  intros.
  remember (iterate f n x) as l1.
  remember (iterate f m x) as l2.
  revert x n m Heql1 Heql2.
  induction H; intros.
    destruct n, m; cbn in *; inversion Heql2; subst.
      left. reflexivity.
      right. destruct m; cbn in *.
        inversion H1.
        inversion H1.
Admitted.
(* end hide *)

Lemma Sublist_tail :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 ->
    forall t1 t2 : list A, tail l1 = Some t1 -> tail l2 = Some t2 ->
      Sublist t1 t2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H0. destruct t2; inv H. constructor.
    inv H1. destruct l1; inv H0. inv H.
      do 2 constructor.
      cbn in *. constructor. apply IHSublist; reflexivity.
Qed.
(* end hide *)

Lemma Sublist_last :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> l1 = [] \/ last l1 = last l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    destruct t; cbn; [left | right]; reflexivity.
    destruct IHSublist; [left | right].
      assumption.
      rewrite H0. destruct l2; cbn.
        inv H.
        reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Sublist vs insert, remove, take *)
(* end hide *)

Lemma Sublist_spec :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 <->
    exists n : nat,
      n < length l2 /\ l1 = drop (S n) l2.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists 0. rewrite drop_0. split; [apply Nat.lt_0_succ | reflexivity].
      destruct IHSublist as (n & IH1 & IH2). subst.
        exists (S n). split.
          now apply Nat.succ_lt_mono in IH1.
          reflexivity.
    destruct 1 as (n & H1 & H2). subst. revert n H1.
      induction l2 as [| h t]; cbn; intros.
        inv H1.
        destruct t as [| h' t']; cbn in *.
          constructor.
          destruct n as [| n']; cbn in *.
            constructor.
            constructor. apply IHt. apply Nat.succ_lt_mono, H1.
Qed.
(* end hide *)

Lemma Sublist_drop_r :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall n : nat, Sublist (drop n l1) l2.
(* begin hide *)
Proof.
  induction 1; intros.
    revert n h. induction t as [| h' t']; cbn; intros.
      constructor.
      destruct n; cbn.
        constructor.
        constructor. apply IHt'.
    constructor. apply IHSublist.
Qed.
(* end hide *)

Lemma Sublist_drop :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall n : nat,
      n < length l2 -> Sublist (drop n l1) (drop n l2).
(* begin hide *)
Proof.
  intros. rewrite Sublist_spec in *. destruct H as (m & H1 & H2).
  subst. rewrite length_drop, ?drop_drop.
  revert n m H0 H1.
  induction l2 as [| h t]; cbn; intros.
    inv H0.
    destruct n as [| n'].
      rewrite Nat.add_0_r. cbn. exists m. split; [assumption | reflexivity].
      destruct m as [| m'].
        cbn. exists 0. split.
          lia.
          rewrite drop_drop, Nat.add_comm. cbn. reflexivity.
        apply Nat.succ_lt_mono in H0. apply Nat.succ_lt_mono in H1.
          destruct (IHt _ _ H0 H1) as (k & Hk1 & Hk2).
          exists (S k). split.
            2: {
              replace (drop (S m' + S n') t) with
                      (drop 1 (drop (S m' + n') t)).
                rewrite Hk2. rewrite ?drop_drop. f_equal. lia.
                rewrite drop_drop. f_equal. lia.
            }
            destruct (length t - n') eqn: Hlt.
              inv Hk1.
              destruct n as [| n''].
Abort.
(* end hide *)

Lemma Sublist_replace :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall (l1' l2' : list A) (n : nat) (x : A),
      replace l1 n x = Some l1' -> replace l2 (n + length l1) x = Some l2' ->
        Sublist l1' l2'.
(* begin hide *)
Proof.
  intros. rewrite Sublist_spec in *.
  destruct H as (m & Hm1 & Hm2). subst.
  rewrite replace_spec in *.
Abort.
(* end hide *)

Lemma Sublist_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list A),
    Sublist la1 la2 /\ Sublist lb1 lb2 /\
      ~ Sublist (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists bool, bool, [true], [false; false; true], [true], [false; true].
  cbn. firstorder.
    constructor. constructor.
    constructor.
    intro. inv H. inv H2. inv H1.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Sublist vs zipWith, unzip, unzipWith *)
(* end hide *)

Lemma Sublist_any_false :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 -> any p l2 = false -> any p l1 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (any p t); cbn.
      rewrite Bool.orb_true_r in H. inv H.
      reflexivity.
    destruct (p x); cbn in H0.
      inv H0.
      apply IHSublist, H0.
Qed.
(* end hide *)

Lemma Sublist_any_true :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 -> any p l1 = true -> any p l2 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    rewrite H, Bool.orb_true_r. reflexivity.
    rewrite (IHSublist H0), Bool.orb_true_r. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Sublist_all *)
(* end hide *)

Lemma Sublist_findLast :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 -> forall x : A,
      findLast p l1 = Some x -> findLast p l2 = Some x.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    rewrite H. reflexivity.
    rewrite (IHSublist _ H0). reflexivity.
Qed.
(* end hide *)

Lemma Sublist_removeLast :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 ->
      match removeLast p l1, removeLast p l2 with
      | None, None => True
      | None, Some (x, l2') => l1 = l2' \/ Sublist l1 l2'
      | x, None => False
      | Some (x, l1'), Some (y, l2') => x = y /\ Sublist l1' l2'
      end.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (removeLast p t) eqn: Heq.
      destruct p0. split; constructor.
      destruct (p h); cbn.
        left. reflexivity.
        trivial.
    destruct (removeLast p l1) eqn: Heq1.
      destruct p0. destruct (removeLast p l2) eqn: Heq2.
        destruct p0, IHSublist; subst. split.
          reflexivity.
          constructor. assumption.
        inv IHSublist.
      destruct (removeLast p l2) eqn: Heq2.
        destruct p0, IHSublist; subst.
          right. constructor.
          right. constructor. assumption.
        destruct (p x).
          right. assumption.
          trivial.
Qed.
(* end hide *)

Lemma Sublist_findIndex :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 -> forall n : nat,
      findIndex p l1 = Some n -> exists m : nat,
        findIndex p l2 = Some m.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (p h).
      exists 0. reflexivity.
      rewrite H. exists (S n). reflexivity.
    destruct (p x).
      exists 0. reflexivity.
      destruct (IHSublist _ H0) as (m & IH). rewrite IH.
        exists (S m). reflexivity.
Qed.
(* end hide *)

Lemma Sublist_filter :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  exists unit, (fun _ => false), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_findIndices :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (findIndices p l1) (findIndices p l2).
(* begin hide *)
Proof.
  exists unit, (fun _ => false), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_takeWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists unit, (fun _ => false), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_dropWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  exists unit, (fun _ => true), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_pmap :
  exists (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  exists unit, unit, (fun _ => None), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Sublist l1 l2 -> Sublist (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (intersperse x t); repeat constructor.
    destruct (intersperse x l2) eqn: Heq.
      inv IHSublist.
      do 2 constructor. assumption.
Qed.
(* end hide *)

Lemma Sublist_elem :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall x : A, elem x l1 -> elem x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. assumption.
    right. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_In :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall x : A, In x l1 -> In x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    right. assumption.
    right. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_NoDup :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> NoDup l2 -> NoDup l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. assumption.
    inv H0. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_Dup :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Dup l1 -> Dup l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    right. assumption.
    right. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_Rep :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Sublist l1 l2 -> forall n : nat, Rep x n l1 -> Rep x n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. assumption.
    constructor. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_Exists :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Sublist l1 l2 -> Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros; right; try apply IHSublist; assumption.
Qed.
(* end hide *)

Lemma Sublist_Forall :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Sublist l1 l2 -> Forall P l2 -> Forall P l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. assumption.
    inv H0. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. assumption.
    constructor. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtMost P n l2 -> AtMost P n l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
      assumption.
      apply AtMost_S. assumption.
    inv H0.
      apply IHSublist. assumption.
      apply AtMost_S, IHSublist, H3.
Qed.
(* end hide *)

(** ** Prefiksy *)

(** Zdefiniuj induktywną relację [Prefix]. Zdanie [Prefix l1 l2]
    zachodzi, gdy lista [l1] pokrywa się z początkowym fragmentem
    listy [l2] o dowolnej długości.

    Przykład: *)

(** [Prefix [1; 2] [1; 2; 3; 4; 5]] zachodzi. *)

(** [Prefix [1; 2] [1; 1; 2; 3; 5]] nie zachodzi. *)

(* begin hide*)
Inductive Prefix {A : Type} : list A -> list A -> Prop :=
| Prefix_nil : forall l : list A, Prefix [] l
| Prefix_cons :
    forall (x : A) (l1 l2 : list A),
      Prefix l1 l2 -> Prefix (x :: l1) (x :: l2).
(* end hide *)

Lemma Prefix_spec :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 <-> exists l3 : list A, l2 = l1 ++ l3.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists l. reflexivity.
      destruct IHPrefix as (l3 & IH). subst. exists l3. reflexivity.
    destruct 1 as (l3 & H). subst.
      induction l1 as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_refl :
  forall (A : Type) (l : list A), Prefix l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Prefix l1 l2 -> Prefix l2 l3 -> Prefix l1 l3.
(* begin hide *)
Proof.
  intros A l1 l2 l3 H. revert l3.
  induction H; intros.
    constructor.
    inv H0. constructor. apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_wasym :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix l2 l1 -> l1 = l2.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H. constructor.
    f_equal. apply IHPrefix. inv H0. assumption.
Qed.
(* end hide *)

Lemma Prefix_length :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> length l1 <= length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Nat.le_0_l.
    apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma Prefix_snoc :
  forall {A : Type} (l1 l2 : list A) (x : A),
    Prefix l1 l2 -> Prefix l1 (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_snoc' :
  exists (A : Type) (l1 l2 : list A),
    Prefix l1 l2 /\ exists x : A, ~ Prefix (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  exists bool, [true], [true; true]. split.
    repeat constructor.
    exists false. cbn. intro. inv H. inv H1.
Qed.
(* end hide *)

Lemma Prefix_app :
  forall (A : Type) (l1 l2 l3 : list A),
    Prefix l1 l2 -> Prefix (l3 ++ l1) (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Prefix_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Prefix l1 l2 -> Prefix l1 (l2 ++ l3).
(* begin hide *)
Proof.
  intros. rewrite Prefix_spec in *. destruct H as (l3' & H); subst.
  exists (l3' ++ l3). rewrite app_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Prefix_rev_l :
  forall (A : Type) (l : list A),
    Prefix (rev l) l -> l = rev l.
(* begin hide *)
Proof.
  intros. apply Prefix_spec in H. destruct H as (l3 & H).
  rewrite H at 1. apply (f_equal length) in H.
  rewrite length_app, length_rev, Nat.add_comm in H.
  destruct l3.
    rewrite app_nil_r. reflexivity.
    cbn in H. lia.
Qed.
(* end hide *)

Lemma Prefix_rev_r :
  forall (A : Type) (l : list A),
    Prefix l (rev l) -> l = rev l.
(* begin hide *)
Proof.
  intros. apply Prefix_spec in H. destruct H as (l3 & H).
  rewrite H at 1. apply (f_equal length) in H.
  rewrite length_app, length_rev, Nat.add_comm in H.
  destruct l3.
    rewrite app_nil_r. reflexivity.
    cbn in H. lia.
Qed.
(* end hide *)

Lemma Prefix_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Prefix l1 l2 -> Prefix (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    apply Prefix_app. assumption.
Qed.
(* end hide *)

Lemma Prefix_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Prefix (replicate n x) (replicate m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert m x. induction n as [| n']; cbn; intros.
      apply Nat.le_0_l.
      inv H. destruct m as [| m']; inv H3. apply le_n_S, (IHn' _ x H1).
    revert m x. induction n as [| n']; cbn; intros.
      constructor.
      destruct m as [| m'].
        inv H.
        cbn. constructor. apply IHn', le_S_n, H.
Qed.
(* end hide *)

Lemma Prefix_replicate_inv_l :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    Prefix l (replicate n x) ->
      exists m : nat, m <= n /\ l = replicate m x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    exists 0. cbn. split; [apply Nat.le_0_l | reflexivity].
    inv H. destruct n as [| n']; inv H3.
      destruct (IHt _ _ H1) as (m & IH1 & IH2); subst. exists (S m); split.
        apply le_n_S. assumption.
        cbn. reflexivity.
Qed.
(* end hide *)

Lemma Prefix_replicate_inv_r :
  exists (A : Type) (l : list A) (n : nat) (x : A),
    Prefix (replicate n x) l /\
      ~ exists m : nat, n <= m /\ l = replicate m x.
(* begin hide *)
Proof.
  exists bool, [true; false], 1, true. cbn. split.
    do 2 constructor.
    destruct 1 as (m & H1 & H2). destruct m as [| m'].
      inv H1.
      cbn in H2. inv H2. destruct m'; inv H0.
Qed.
(* end hide *)

Lemma Prefix_replicate' :
  forall (A : Type) (n : nat) (x y : A),
    Prefix (replicate n x) (replicate n y) <-> n = 0 \/ x = y.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; intros.
      left. reflexivity.
      right. inv H. reflexivity.
    destruct 1; subst; cbn.
      1-2: apply Prefix_refl.
Qed.
(* end hide *)

Lemma Prefix_replicate'' :
  forall (A : Type) (n m : nat) (x y : A),
    Prefix (replicate n x) (replicate m y) <->
    n = 0 \/ n <= m /\ x = y.
(* begin hide *)
Proof.
  split.
    revert m x y. induction n as [| n']; cbn; intros.
      left. reflexivity.
      inv H. destruct m as [| m']; inv H3.
        destruct (IHn' _ _ _ H1) as [H | [IH1 IH2]]; subst.
          right. split.
            apply le_n_S, Nat.le_0_l.
            reflexivity.
          right. split.
            apply le_n_S. assumption.
            reflexivity.
    intro. decompose [and or] H; clear H; subst.
      cbn. constructor.
      rewrite Prefix_replicate. assumption.
Qed.
(* end hide *)

Lemma Prefix_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Prefix (iterate f n x) (iterate f m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert m x. induction n as [| n']; cbn; intros.
      apply Nat.le_0_l.
      inv H. destruct m as [| m']; inv H3. apply le_n_S, (IHn' _ _ H1).
    revert m x. induction n as [| n']; cbn; intros.
      constructor.
      destruct m as [| m'].
        inv H.
        cbn. constructor. apply IHn', le_S_n, H.
Qed.
(* end hide *)

Lemma Prefix_insert :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall (n : nat) (x : A),
      n <= length l1 -> Prefix (insert l1 n x) (insert l2 n x).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct n; inv H. rewrite insert_0. do 2 constructor.
    destruct n as [| n'].
      do 2 constructor. specialize (IHPrefix _ x0 (Nat.le_0_l (length l1))).
        rewrite ?insert_0 in IHPrefix. inv IHPrefix. assumption.
      constructor. apply IHPrefix. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma Prefix_replace :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall (n : nat) (x : A),
      match replace l1 n x, replace l2 n x with
      | Some l1', Some l2' => Prefix l1' l2'
      | _, _ => True
      end.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    trivial.
    destruct n as [| n']; cbn.
      constructor. assumption.
      specialize (IHPrefix n' x0).
        destruct (replace l1 n' x0), (replace l2 n' x0).
          constructor. assumption.
          1-3: trivial.
Qed.
(* end hide *)

Lemma insert_length_ge :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    length l <= n -> insert l n x = snoc x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inv H.
      f_equal. apply IHt. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma Prefix_insert' :
  exists (A : Type) (l1 l2 : list A),
    Prefix l1 l2 /\
    exists (n : nat) (x : A),
      length l1 < n /\ ~ Prefix (insert l1 n x) (insert l2 n x).
(* begin hide *)
Proof.
  exists bool, [true], [true; true]. split.
    do 2 constructor.
    exists 2, false. cbn. split.
      apply le_n.
      intro. inv H. inv H1.
Qed.
(* end hide *)

Lemma Prefix_take_l :
  forall (A : Type) (l : list A) (n : nat), Prefix (take n l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct n as [| n']; cbn; constructor. apply IHt.
Qed.
(* end hide *)

Lemma Prefix_take :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall n : nat, Prefix (take n l1) (take n l2).
(* begin hide *)
Proof.
  induction 1; intros.
    rewrite take_nil. constructor.
    destruct n as [| n']; cbn; constructor. apply IHPrefix.
Qed.
(* end hide *)

Lemma Prefix_drop :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall n : nat, Prefix (drop n l1) (drop n l2).
(* begin hide *)
Proof.
  induction 1; intros.
    rewrite drop_nil. constructor.
    destruct n as [| n']; cbn.
      constructor. assumption.
      apply IHPrefix.
Qed.
(* end hide *)

Lemma Prefix_zip :
  forall (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Prefix la1 la2 -> Prefix lb1 lb2 ->
      Prefix (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  intros until 1. revert lb1 lb2. induction H; cbn; intros.
    constructor.
    inv H0; constructor. apply IHPrefix. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs unzip, zipWith, unzipWith *)
(* end hide *)

Lemma Prefix_any_false :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> any p l2 = false -> any p l1 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (any p l2).
      rewrite Bool.orb_true_r in H0. congruence.
      rewrite Bool.orb_false_r in H0. rewrite H0, IHPrefix; reflexivity.
Qed.
(* end hide *)

Lemma Prefix_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> any p l1 = true -> any p l2 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    congruence.
    destruct (any p l1).
      rewrite IHPrefix, Bool.orb_true_r; reflexivity.
      rewrite Bool.orb_false_r in H0. rewrite H0. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Prefix_all_false :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> all p l1 = false -> all p l2 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    congruence.
    destruct (all p l1).
      rewrite Bool.andb_true_r in H0. rewrite H0. cbn. reflexivity.
      rewrite IHPrefix, Bool.andb_false_r; reflexivity.
Qed.
(* end hide *)

Lemma Prefix_all_true :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> all p l2 = true -> all p l1 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (all p l2).
      rewrite Bool.andb_true_r in H0. rewrite H0, IHPrefix; reflexivity.
      rewrite Bool.andb_false_r in H0. congruence.
Qed.
(* end hide *)

Lemma Prefix_find_None :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> find p l2 = None -> find p l1 = None.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x).
      assumption.
      apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_find_Some :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> forall x : A,
      find p l1 = Some x -> find p l2 = Some x.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    destruct (p x).
      assumption.
      apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_findIndex_None :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> findIndex p l2 = None -> findIndex p l1 = None.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x).
      assumption.
      destruct (findIndex p l2).
        inv H0.
        rewrite IHPrefix; reflexivity.
Qed.
(* end hide *)

Lemma Prefix_findIndex_Some :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> forall i : nat,
      findIndex p l1 = Some i -> findIndex p l2 = Some i.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    destruct (p x).
      assumption.
      destruct (findIndex p l1); inv H0.
        rewrite (IHPrefix _ eq_refl). reflexivity.
Qed.
(* end hide *)

Lemma Prefix_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> count p l1 <= count p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Nat.le_0_l.
    destruct (p x); try apply le_n_S; assumption.
Qed.
(* end hide *)

Lemma Prefix_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_findIndices :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (findIndices p l1) (findIndices p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; apply Prefix_map; assumption.
Qed.
(* end hide *)

Lemma Prefix_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Prefix (takeWhile p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h); constructor. assumption.
Qed.
(* end hide *)

Lemma Prefix_takeWhile_pres :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_dropWhile :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs findLast, removeFirst i removeLast *)
(* end hide *)

Lemma Prefix_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (intersperse x l1), (intersperse x l2).
      apply Prefix_refl.
      do 2 constructor.
      inv IHPrefix.
      do 2 constructor. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs groupBy *)
(* end hide *)

Lemma Prefix_elem :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall x : A, elem x l1 -> elem x l2.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H.
    inv H0.
      constructor.
      constructor. apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_elem_conv :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall x : A, ~ elem x l2 -> ~ elem x l1.
(* begin hide *)
Proof.
  induction 1; intros.
    intro. inv H0.
    intro. apply H0. inv H1.
      constructor.
      assert (~ elem x0 l2).
        rewrite elem_cons' in H0. intro. apply H0. right. assumption.
        specialize (IHPrefix _ H1). contradiction.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs In *)
(* end hide *)

Lemma Prefix_NoDup :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> NoDup l2 -> NoDup l1.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    inv H0. constructor.
      intro. apply H3. apply Prefix_elem with l1; assumption.
      apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_Dup :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> Dup l1 -> Dup l2.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H.
    inv H0.
      constructor. apply Prefix_elem with l1; assumption.
      right. apply IHPrefix. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs Rep *)
(* end hide *)

Lemma Prefix_Exists :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Prefix l1 l2 -> Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H.
    inv H0.
      constructor. assumption.
      right. apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_Forall :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Prefix l1 l2 -> Forall P l2 -> Forall P l1.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    inv H0. constructor.
      assumption.
      apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. constructor.
    inv H0; constructor; try apply IHPrefix; assumption.
Qed.
(* end hide *)

Lemma Prefix_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtMost P n l2 -> AtMost P n l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    inv H0; constructor; try apply IHPrefix; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs Exactly - raczej nic z tego *)
(* end hide *)

Lemma Sublist_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true], [false; true]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Prefix_spec' :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 <-> exists n : nat, l1 = take n l2.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists 0. rewrite take_0. reflexivity.
      destruct IHPrefix as (n & IH). exists (S n). rewrite IH. reflexivity.
    destruct 1 as (n & H); subst. apply Prefix_take_l.
Qed.
(* end hide *)

(** ** Sufiksy *)

(** Zdefiniuj induktywną relację [Suffix]. Zdanie [Suffix l1 l2]
    zachodzi, gdy [l1] pokrywa się z końcowym fragmentem listy [l2]
    o dowolnej długości.

    Przykłady: *)

(** [Suffix [4; 5] [1; 2; 3; 4; 5]] zachodzi. *)

(** [Suffix [3; 4] [1; 2; 3; 4; 5]] nie zachodzi. *)

(* begin hide *)
Inductive Suffix {A : Type} : list A -> list A -> Prop :=
| Suffix_refl :
    forall l : list A, Suffix l l
| Suffix_cons :
    forall (x : A) (l1 l2 : list A),
      Suffix l1 l2 -> Suffix l1 (x :: l2).
(* end hide *)

Lemma Suffix_spec :
  forall (A : Type) (l1 l2 : list A),
    Suffix l1 l2 <-> exists l3 : list A, l2 = l3 ++ l1.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists []. cbn. reflexivity.
      destruct IHSuffix as (l3 & IH); subst.
        exists (x :: l3). reflexivity.
    destruct 1 as (l3 & H). subst.
      induction l3 as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Suffix_cons_inv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Suffix (x :: l1) l2 -> Suffix l1 l2.
(* begin hide *)
Proof.
  intros. apply Suffix_spec in H. destruct H as (l3 & H). subst.
  induction l3 as [| h t]; cbn.
    constructor. apply Suffix_refl.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Suffix_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Suffix l1 l2 -> Suffix l2 l3 -> Suffix l1 l3.
(* begin hide *)
Proof.
  intros A l1 l2 l3 H. revert l3.
  induction H; intros.
    assumption.
    apply IHSuffix. apply Suffix_cons_inv in H0. assumption.
Qed.
(* end hide *)

Lemma Suffix_wasym :
  forall (A : Type) (l1 l2 : list A),
    Suffix l1 l2 -> Suffix l2 l1 -> l1 = l2.
(* begin hide *)
Proof.
  intros.
  apply Suffix_spec in H. destruct H as (l1' & H1).
  apply Suffix_spec in H0. destruct H0 as (l2' & H2).
  subst. apply (f_equal length) in H2. rewrite ?length_app in H2.
  destruct l2', l1'; cbn in H2; try lia. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Suffix_nil_l :
  forall (A : Type) (l : list A), Suffix [] l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Suffix_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Suffix l1 l2 -> Suffix (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros; constructor; assumption.
Qed.
(* end hide *)

Lemma Suffix_Sublist :
  forall (A : Type) (l1 l2 : list A),
    Suffix l1 l2 <-> Sublist l1 l2 \/ l1 = l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      right. reflexivity.
      left. destruct IHSuffix; subst.
        apply Sublist_trans with l2.
          assumption.
          constructor.
        constructor.
    destruct 1; subst.
      induction H; constructor.
        apply Suffix_refl.
        assumption.
      apply Suffix_refl.
Qed.
(* end hide *)

Lemma Prefix_Suffix :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 <-> Suffix (rev l1) (rev l2).
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      apply Suffix_nil_l.
      rewrite <- ?snoc_app_singl. apply Suffix_snoc. assumption.
    assert (forall l1 l2 : list A, Suffix l1 l2 -> Prefix (rev l1) (rev l2)).
      induction 1; cbn.
        apply Prefix_refl.
        apply Prefix_snoc. assumption.
      intro. specialize (H _ _ H0). rewrite ?rev_rev in H. assumption.
Qed.
(* end hide *)

(** ** Listy jako ciągi *)

(** Zdefiniuj relację [Subseq]. Zdanie [Subseq l1 l2] zachodzi, gdy
    lista [l2] zawiera wszystkie elementy listy [l1] w takiej samej
    kolejności, w jakiej występują one w [l1], ale może też zawierać
    inne elementy.

    Przykłady: *)

(** [Subseq [1; 3; 5] [0; 1; 5; 2; 3; 4; 5]] zachodzi. *)

(** [Subseq [1; 3; 5] [3; 1; 5; 3; 6]] nie zachodzi. *)

(* begin hide *)
Inductive Subseq {A : Type} : list A -> list A -> Prop :=
| Subseq_nil :
    forall l : list A, Subseq [] l
| Subseq_cons :
    forall (x : A) (l1 l2 : list A),
      Subseq l1 l2 -> Subseq (x :: l1) (x :: l2)
| Subseq_skip :
    forall (x : A) (l1 l2 : list A),
      Subseq l1 l2 -> Subseq l1 (x :: l2).
(* end hide *)

Lemma Subseq_refl :
  forall (A : Type) (l : list A), Subseq l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_cons_inv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq (x :: l1) (x :: l2) -> Subseq l1 l2.
(* begin hide *)
Proof.
  intros A x l1 l2. revert l1.
  induction l2 as [| h1 t1]; cbn; intros.
    inv H.
      assumption.
      inv H2.
    inv H.
      assumption.
      inv H2.
        constructor. apply IHt1. constructor. assumption.
        constructor. apply IHt1. apply Subseq_skip. assumption.
Qed.
(* end hide *)

Lemma Subseq_cons_inv_l :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq (x :: l1) l2 -> Subseq l1 l2.
(* begin hide *)
Proof.
  intros. revert x l1 H.
  induction l2 as [| h1 t1]; cbn; intros; inv H.
    constructor. assumption.
    constructor. apply IHt1 with x. assumption.
Qed.
(* end hide *)

Lemma Subseq_isEmpty_l :
  forall (A : Type) (l1 l2 : list A),
    isEmpty l1 = true -> Subseq l1 l2.
(* begin hide *)
Proof.
  destruct l1; cbn; intros.
    constructor.
    congruence.
Qed.
(* end hide *)

Lemma Subseq_nil_r :
  forall (A : Type) (l : list A),
    Subseq l [] -> l = [].
(* begin hide *)
Proof.
  inversion 1. reflexivity.
Qed.
(* end hide *)

Lemma Subseq_length :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> length l1 <= length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Nat.le_0_l.
    apply le_n_S. assumption.
    apply le_S. assumption.
Qed.
(* end hide *)

Lemma Subseq_trans : 
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq l2 l3 -> Subseq l1 l3.
(* begin hide *)
Proof.
  intros A l1 l2 l3 H12 H23. revert l1 H12.
  induction H23; cbn; intros.
    inv H12. constructor.
    inv H12; constructor; apply IHSubseq; assumption.
    inv H12; constructor; apply IHSubseq; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_cons_l_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq (x :: l1) l2 ->
      exists l21 l22 : list A,
        l2 = l21 ++ x :: l22 /\ Subseq l1 l22.
(* begin hide *)
Proof.
  intros A x l1 l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inv H.
    inv H.
      exists [], t2. cbn. split; [reflexivity | assumption].
      destruct (IHt2 _ H2) as (l21 & l22 & IH1 & IH2); subst.
        exists (h2 :: l21), l22. cbn. split; [reflexivity | assumption].
Qed.
(* end hide *)

Lemma Subseq_wasym :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq l2 l1 -> l1 = l2.
(* begin hide *)
Proof.
  induction 1; intro.
    inv H. reflexivity.
    f_equal. apply IHSubseq. apply Subseq_cons_inv in H0. assumption.
    apply Subseq_cons_l_app in H0.
      destruct H0 as (l21 & l22 & H1 & H2). subst.
      apply Subseq_length in H.
      apply Subseq_length in H2.
      rewrite length_app in H. cbn in H. lia.
Qed.
(* end hide *)

Lemma Subseq_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq l1 (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_snoc' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn; repeat constructor. assumption.
    constructor. assumption.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_app_l :
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq l1 (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Subseq_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq l1 (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_app_l' :
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq (l3 ++ l1) (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Subseq_app_r' :
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq (l1 ++ l3) (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Subseq_app_l, Subseq_refl.
    1-2: constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_app_not_comm :
  exists (A : Type) (l1 l2 l3 : list A),
    Subseq l1 (l2 ++ l3) /\ ~ Subseq l1 (l3 ++ l2).
(* begin hide *)
Proof.
  exists bool, [true; false], [true], [false]. cbn. split.
    repeat constructor.
    intro. inv H. inv H2.
      inv H0.
      inv H1.
Qed.
(* end hide *)

Lemma Subseq_map : 
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Subseq l1 l2 -> Subseq (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    apply Subseq_app_l'. assumption.
    apply Subseq_app_l. assumption.
Qed.
(* end hide *)

Lemma Subseq_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Subseq (replicate n x) (replicate m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert m. induction n as [| n']; cbn; intros.
      apply Nat.le_0_l.
      destruct m as [| m']; cbn in H.
        inv H.
        apply le_n_S, IHn'. apply Subseq_cons_inv with x. assumption.
    induction 1.
      apply Subseq_refl.
      cbn. constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Subseq (iterate f n x) (iterate f m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert f m x. induction n as [| n']; cbn; intros.
      apply Nat.le_0_l.
      destruct m as [| m']; cbn in H.
        inv H.
        apply le_n_S, (IHn' f _ (f x)).
          apply Subseq_cons_inv with x. assumption.
    revert f m x. induction n as [| n']; cbn; intros.
      constructor.
      destruct m as [| m']; cbn.
        inv H.
        constructor. apply IHn', le_S_n. assumption.
Qed.
(* end hide *)

Lemma Subseq_tail :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall l1' l2' : list A,
      tail l1 = Some l1' -> tail l2 = Some l2' -> Subseq l1' l2'.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    inv H0; inv H1. assumption.
    inv H1. destruct l1; inv H0. apply Subseq_cons_inv_l in H. assumption.
Qed.
(* end hide *)

Lemma Subseq_uncons :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (h1 h2 : A) (t1 t2 : list A),
      uncons l1 = Some (h1, t1) -> uncons l2 = Some (h2, t2) ->
        h1 = h2 \/ Subseq l1 t2.
(* begin hide *)
Proof.
  intros. inv H; cbn in *.
    inv H0.
    inv H0; inv H1. left. reflexivity.
    inv H1. right. assumption.
Qed.
(* end hide *)

Lemma Subseq_init :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall l1' l2' : list A,
      init l1 = Some l1' -> init l2 = Some l2' -> Subseq l1' l2'.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    destruct (init l1) eqn: Heq1, (init l2) eqn: Heq2.
      inv H0; inv H1. constructor. apply IHSubseq; reflexivity.
      inv H0; inv H1. apply init_None in Heq2. subst. inv H.
        cbn in Heq1. inv Heq1.
      inv H0; inv H1. constructor.
      inv H0; inv H1. constructor.
    destruct (init l2) eqn: Heq2.
      inv H1. constructor. apply IHSubseq; trivial.
      inv H1. apply init_None in Heq2. subst. inv H. cbn in H0. inv H0.
Qed.
(* end hide *)

Lemma Subseq_unsnoc :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (h1 h2 : A) (t1 t2 : list A),
      unsnoc l1 = Some (h1, t1) -> unsnoc l2 = Some (h2, t2) ->
        h1 = h2 \/ Subseq l1 t2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    destruct (unsnoc l1) eqn: Heq1, (unsnoc l2) eqn: Heq2.
      destruct p, p0. inv H0; inv H1.
        destruct (IHSubseq _ _ _ _ eq_refl eq_refl).
          left. assumption.
          right. constructor. assumption.
      apply unsnoc_None in Heq2. subst. inv H. cbn in Heq1. inv Heq1.
      destruct p. inv H0; inv H1. apply unsnoc_None in Heq1; subst.
        right. constructor. apply Subseq_nil.
      inv H0; inv H1. left. reflexivity.
    destruct (unsnoc l2) eqn: Heq.
      destruct p. inv H1. destruct (IHSubseq _ _ _ _ H0 eq_refl).
        left. assumption.
        right. constructor. assumption.
      apply unsnoc_None in Heq. subst. inv H. right. apply Subseq_nil.
Qed.
(* end hide *)

Lemma Subseq_nth :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    Subseq l1 l2 -> nth n l1 = Some x ->
      exists m : nat, nth m l2 = Some x /\ n <= m.
(* begin hide *)
Proof.
  intros A l1 l2 n x H. revert n x.
  induction H; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in H0.
      inv H0. exists 0. cbn. split; [reflexivity | apply Nat.le_0_l].
      destruct (IHSubseq _ _ H0) as (m & IH1 & IH2).
        exists (S m). cbn. split.
          assumption.
          apply le_n_S. assumption.
    destruct (IHSubseq _ _ H0) as (m & IH1 & IH2).
      exists (S m). cbn. split.
        assumption.
        apply le_S. assumption.
Qed.
(* end hide *)

Lemma Subseq_insert :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    Subseq l1 l2 -> Subseq l1 (insert l2 n x).
(* begin hide *)
Proof.
  intros A l1 l2 n x H. revert n x.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n'].
      do 2 constructor. assumption.
      constructor. apply IHSubseq.
    destruct n as [| n']; repeat constructor; trivial.
Qed.
(* end hide *)

Lemma Subseq_replace :
  forall (A : Type) (l1 l1' l2 : list A) (n : nat) (x : A),
    Subseq l1 l2 -> replace l1 n x = Some l1' ->
      exists (m : nat) (l2' : list A),
        replace l2 m x = Some l2' /\ Subseq l1' l2'.
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma Subseq_remove' :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    Subseq l1 l2 -> Subseq (remove' n l1) l2.
(* begin hide *)
Proof.
  intros A l1 l2 n H. revert n.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n']; cbn.
      constructor. assumption.
      rewrite remove'_S_cons. constructor. apply IHSubseq.
    constructor. apply IHSubseq.
Qed.
(* end hide *)

Lemma Subseq_take :
  forall (A : Type) (l : list A) (n : nat),
    Subseq (take n l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply Subseq_refl.
    destruct n as [| n']; constructor. apply IHt.
Qed.
(* end hide *)

Lemma Subseq_drop :
  forall (A : Type) (l : list A) (n : nat),
    Subseq (drop n l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply Subseq_refl.
    destruct n as [| n']; constructor.
      apply Subseq_refl.
      apply IHt.
Qed.
(* end hide *)

Lemma Subseq_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Subseq la1 la2 /\ Subseq lb1 lb2 /\
      ~ Subseq (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists bool, bool, [true], [true; false], [false], [true; false].
  firstorder.
    do 2 constructor.
    do 3 constructor.
    cbn. intro. inv H. inv H2. inv H1.
Qed.
(* end hide *)

Lemma Subseq_all :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> bool_le (all p l2) (all p l1).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (all p l); constructor.
    destruct (p x); cbn; [assumption | constructor].
    destruct (p x); cbn.
      assumption.
      destruct (all p l1); constructor.
Qed.
(* end hide *)

Lemma Subseq_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> bool_le (any p l1) (any p l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (any p l); constructor.
    destruct (p x); cbn; [constructor | assumption].
    destruct (p x); cbn.
      destruct (any p l1); constructor.
      assumption.
Qed.
(* end hide *)

Lemma Subseq_all' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> all p l2 = true -> all p l1 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x); cbn in *.
      apply IHSubseq. assumption.
      congruence.
    destruct (p x); cbn in *.
      apply IHSubseq. assumption.
      congruence.
Qed.
(* end hide *)

Lemma Subseq_any' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> any p l2 = false -> any p l1 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x); cbn in *.
      congruence.
      apply IHSubseq. assumption.
    destruct (p x); cbn in *.
      congruence.
      apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_findIndex :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A) (n m : nat),
    Subseq l1 l2 /\ findIndex p l1 = Some n /\
    findIndex p l2 = Some m /\ m < n.
(* begin hide *)
Proof.
  exists bool, id, [false; true], [true; false; true; false], 1, 0.
  cbn. firstorder. repeat constructor.
Qed.
(* end hide *)

Lemma Subseq_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> count p l1 <= count p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Nat.le_0_l.
    destruct (p x); try apply le_n_S; assumption.
    destruct (p x); try apply le_S; assumption.
Qed.
(* end hide *)

Lemma Subseq_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_filter' :
  forall (A : Type) (p : A -> bool) (l : list A),
    Subseq (filter p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Subseq (takeWhile p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_takeWhile' :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Subseq (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists bool, id, [true], [false; true]. cbn. split.
    repeat constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Subseq_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Subseq (dropWhile p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor.
      assumption.
      apply Subseq_refl.
Qed.
(* end hide *)

Lemma Subseq_dropWhile' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
    destruct (p x); try constructor.
      assumption.
      apply Subseq_trans with (dropWhile p l2).
        assumption.
        apply Subseq_dropWhile.
Qed.
(* end hide *)

Lemma Subseq_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); try constructor; assumption.
    destruct (f x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_map_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (map Some (pmap f l1)) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); cbn; constructor; assumption.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (intersperse x l1) eqn: Heq1, (intersperse x l2) eqn: Heq2.
      do 2 constructor.
      do 2 constructor.
      inv IHSubseq.
      do 2 constructor. assumption.
    destruct (intersperse x l2).
      inv IHSubseq. constructor.
      do 2 constructor. assumption.
Qed.
(* end hide *)

(* begin hide *)

(* TODO: intercalate, Subseq_spec i inne dla Subseq *)

Fixpoint intercalate {A : Type} (l : list A) (ll : list (list A)) : list A :=
match l, ll with
| [], _ => join ll
| _, [] => l
| h :: t, l :: ls => h :: l ++ intercalate t ls
end.

Lemma Subseq_spec :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 ->
      exists ll : list (list A),
        l2 = intercalate l1 ll.
Proof.
  induction 1; cbn.
    exists (map (fun x => [x]) l). admit.
    destruct IHSubseq as (ll & IH). subst.
      exists ([] :: ll). cbn. reflexivity.
    destruct IHSubseq as (ll & IH). subst. destruct ll as [| hl tl].
      destruct l1; cbn in *.
        exists [[x]]. cbn. reflexivity.
        exists [[x]]. cbn. destruct l1; cbn.
Abort.

(*
bind

unzip
zipWith
unzipWith

find i findLast
removeFirst i removeLast
findIndices
*)
(* end hide *)

Lemma Subseq_elem :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 ->
      forall x : A, elem x l1 -> elem x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    inv H0; [left | right]. apply IHSubseq. assumption.
    right. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_In :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 ->
      forall x : A, In x l1 -> In x l2.
(* begin hide *)
Proof.
  induction 1; firstorder.
Qed.
(* end hide *)

Lemma Subseq_NoDup :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> NoDup l2 -> NoDup l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    inv H0. constructor.
      intro. apply H3. apply Subseq_elem with l1; assumption.
      apply IHSubseq. assumption.
    inv H0. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_Dup :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> Dup l1 -> Dup l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    inv H0.
      left. apply Subseq_elem with l1; assumption.
      right. apply IHSubseq. assumption.
    right. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_Rep :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (x : A) (n : nat),
      Rep x n l1 -> Rep x n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. constructor.
    inv H0; constructor; apply IHSubseq; assumption.
    constructor. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_Exists :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Subseq l1 l2 -> Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    rewrite Exists_cons in *. firstorder.
    right. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_Forall :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Subseq l1 l2 -> Forall P l2 -> Forall P l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    inv H0. constructor; try apply IHSubseq; assumption.
    inv H0. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. constructor.
    inv H0; constructor; try apply IHSubseq; assumption.
    constructor. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtMost P n l2 -> AtMost P n l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    inv H0.
      constructor; try apply IHSubseq; assumption.
      apply AM_skip. apply IHSubseq. assumption.
    inv H0.
      apply IHSubseq. assumption.
      apply AtMost_S. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Sublist_Subseq :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Subseq l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor. apply Subseq_refl.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_Sublist :
  exists (A : Type) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Sublist l1 l2.
(* begin hide *)
Proof.
  exists unit, [], []. split.
    constructor.
    inversion 1.
Qed.
(* end hide *)

Lemma Prefix_Subseq :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> Subseq l1 l2.
(* begin hide *)
Proof.
  induction 1; constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true], [false; true]. split.
    do 3 constructor.
    intro. inv H.
Qed.
(* end hide *)

(** ** Zawieranie *)

(** Zdefiniuj (niekoniecznie induktywnie) relację [Incl]. Zdanie
    [Incl l1 l2] zachodzi, gdy lista [l2] zawiera wszystkie te
    elementy, które zawiera lista [l1], ale nie musi koniecznie
    zawierać tyle samo sztuk każdego elementu.

    Przykłady: *)

(** [Incl [1; 1; 2; 2; 3; 3] [3; 4; 5; 1; 9; 0; 2]] zachodzi. *)

(** [Incl [1; 1; 2; 2; 3; 3] [2; 3; 4; 5]] nie zachodzi. *)

(* begin hide *)
Definition Incl {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 -> elem x l2.
(* end hide *)

Lemma Incl_nil :
  forall (A : Type) (l : list A), Incl [] l.
(* begin hide *)
Proof.
  unfold Incl; intros. inversion H.
Qed.
(* end hide *)

Lemma Incl_nil_inv :
  forall (A : Type) (l : list A),
    Incl l [] -> l = [].
(* begin hide *)
Proof.
  unfold Incl; intros. destruct l as [| h t].
    reflexivity.
    specialize (H h ltac:(left)). inversion H.
Qed.
(* end hide *)

Lemma Incl_cons :
  forall (A : Type) (h : A) (t1 t2 : list A),
    Incl t1 t2 -> Incl (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  unfold Incl; intros.
  inversion H0; subst; clear H0.
    left.
    right. apply H, H3.
Qed.
(* end hide *)

Lemma Incl_cons' :
  forall (A : Type) (h : A) (t : list A),
    Incl t (h :: t).
(* begin hide *)
Proof.
  inversion 1; subst.
    right. left.
    do 2 right. assumption.
Qed.
(* end hide *)

Lemma Incl_cons'' :
  forall (A : Type) (h : A) (t l : list A),
    Incl l t -> Incl l (h :: t).
(* begin hide *)
Proof.
  unfold Incl; intros. right. apply H, H0.
Qed.
(* end hide *)

Lemma Incl_cons_conv :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Incl (x :: l1) (x :: l2) /\ ~ Incl l1 l2.
(* begin hide *)
Proof.
  exists unit, tt, [tt], []. unfold Incl. split; intros.
    inv H.
      constructor.
      assumption.
    intro. specialize (H tt ltac:(left)). inv H.
Qed.
(* end hide *)

Lemma Incl_refl :
  forall (A : Type) (l : list A), Incl l l.
(* begin hide *)
Proof.
  unfold Incl. trivial.
Qed.
(* end hide *)

Lemma Incl_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Incl l1 l2 -> Incl l2 l3 -> Incl l1 l3.
(* begin hide *)
Proof.
  unfold Incl; intros. apply H0, H, H1.
Qed.
(* end hide *)

Lemma Incl_length :
  forall (A : Type) (l1 l2 : list A),
    ~ Dup l1 -> Incl l1 l2 -> length l1 <= length l2.
(* begin hide *)
(* TODO: Incl_length *)
Proof.
  unfold Incl. induction l1 as [| h1 t1]; cbn; intros.
    apply Nat.le_0_l.
    destruct l2 as [| h2 t2].
      specialize (H0 h1 ltac:(left)). inv H0.
      cbn. apply le_n_S, IHt1.
        intro. apply H. right. assumption.
        intros. specialize (H0 x ltac:(right; assumption)). inv H0.
Abort.
(* end hide *)

Lemma Incl_snoc :
  forall (A : Type) (x : A) (l : list A),
    Incl l (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply Incl_nil.
    apply Incl_cons. assumption.
Qed.
(* end hide *)

Lemma Incl_singl_snoc :
  forall (A : Type) (x : A) (l : list A),
    Incl [x] (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply Incl_refl.
    apply Incl_cons''. assumption.
Qed.
(* end hide *)

Lemma Incl_snoc_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Incl l1 l2 -> Incl (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    apply Incl_singl_snoc.
    unfold Incl in *. intros x' H'. inversion H'; subst.
      rewrite elem_snoc. left. apply H. left.
      apply IHt.
        intros. apply H. right. assumption.
        assumption.
Qed.
(* end hide *)

Lemma Incl_app_rl :
  forall (A : Type) (l l1 l2 : list A),
    Incl l l2 -> Incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_app_r, H, H0.
Qed.
(* end hide *)

Lemma Incl_app_rr :
  forall (A : Type) (l l1 l2 : list A),
    Incl l l1 -> Incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_app_l, H, H0.
Qed.
(* end hide *)

Lemma Incl_app_l :
  forall (A : Type) (l1 l2 l3 : list A),
    Incl (l1 ++ l2) l3 <-> Incl l1 l3 /\ Incl l2 l3.
(* begin hide *)
Proof.
  unfold Incl; repeat split; intros.
    apply H. rewrite elem_app. left. assumption.
    apply H. rewrite elem_app. right. assumption.
    rewrite elem_app in H0. destruct H, H0.
      apply H. assumption.
      apply H1. assumption.
Qed.
(* end hide *)

Lemma Incl_app_sym :
  forall (A : Type) (l1 l2 l : list A),
    Incl (l1 ++ l2) l -> Incl (l2 ++ l1) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply H. rewrite elem_app in *.
  destruct H0; [right | left]; assumption.
Qed.
(* end hide *)

Lemma Incl_rev :
  forall (A : Type) (l : list A), Incl (rev l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. rewrite <- elem_rev. assumption.
Qed.
(* end hide *)

Lemma Incl_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Incl l1 l2 -> Incl (map f l1) (map f l2).
(* begin hide *)
Proof.
  unfold Incl; intros. rewrite elem_map_conv in *.
  destruct H0 as [x' [H1 H2]]. exists x'. split.
    assumption.
    apply H, H2.
Qed.
(* end hide *)

Lemma Incl_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Incl l1 l2 -> Incl (join l1) (join l2).
(* begin hide *)
Proof.
  unfold Incl; intros.
  apply elem_join in H0. destruct H0 as (l & H1 & H2).
  apply elem_join. exists l. split.
    assumption.
    apply H. assumption.
Qed.
(* end hide *)

Lemma Incl_elem_join :
  forall (A : Type) (ll : list (list A)) (l : list A),
    elem l ll -> Incl l (join ll).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_join. exists l. split; assumption.
Qed.
(* end hide *)

Lemma Incl_replicate :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    elem x l -> Incl (replicate n x) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_replicate in H0.
  destruct H0. subst. assumption.
Qed.
(* end hide *)

Lemma Incl_replicate' :
  forall (A : Type) (n m : nat) (x : A),
    n <> 0 -> Incl (replicate m x) (replicate n x).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_replicate in H0.
  destruct H0. subst. apply elem_replicate. split; trivial.
Qed.
(* end hide *)

Lemma Incl_nth :
  forall (A : Type) (l1 l2 : list A),
    Incl l1 l2 <->
    forall (n1 : nat) (x : A), nth n1 l1 = Some x ->
      exists n2 : nat, nth n2 l2 = Some x.
(* begin hide *)
Proof.
  unfold Incl; split; intros.
    rewrite <- iff_elem_nth. apply H. rewrite iff_elem_nth.
      exists n1. assumption.
    rewrite iff_elem_nth in *. destruct H0 as (n & H0).
      apply H with n. assumption.
Qed.
(* end hide *)

Lemma Incl_remove :
  forall (A : Type) (l : list A) (n : nat),
    match remove n l with
    | None => True
    | Some (_, l') => Incl l' l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      apply Incl_cons'.
      specialize (IHt n'). destruct (remove n' t).
        destruct p. apply Incl_cons, IHt.
        trivial.
Qed.
(* end hide *)

Lemma Incl_take :
  forall (A : Type) (l : list A) (n : nat),
    Incl (take n l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_take in H. assumption.
Qed.
(* end hide *)

Lemma Incl_drop :
  forall (A : Type) (l : list A) (n : nat),
    Incl (drop n l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_drop in H. assumption.
Qed.
(* end hide *)

Lemma Incl_insert :
  forall (A : Type) (l1 l2 : list A) (n m : nat) (x : A),
    Incl l1 l2 -> Incl (insert l1 n x) (insert l2 m x).
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite elem_insert in *. firstorder.
Qed.
(* end hide *)

Lemma Incl_replace :
  forall (A : Type) (l1 l1' l2 : list A) (n : nat) (x : A),
    Incl l1 l2 -> replace l1 n x = Some l1' ->
      exists (m : nat) (l2' : list A),
        replace l2 m x = Some l2' /\ Incl l1' l2'.
(* begin hide *)
Proof.
  unfold Incl. induction l1 as [| h1 t1]; cbn; intros.
    inv H0.
    destruct n as [| n']; cbn in *.
      inv H0. exists 0.
Abort.
(* end hide *)

Lemma Incl_splitAt :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
    | None => True
    | Some (l1, _, l2) => Incl l1 l /\ Incl l2 l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      split.
        apply Incl_nil.
        apply Incl_cons'.
      specialize (IHt n'). destruct (splitAt n' t).
        destruct p, p. destruct IHt as (IH1 & IH2). split.
          apply Incl_cons, IH1.
          apply Incl_cons'', IH2.
        assumption.
Qed.
(* end hide *)

Lemma Incl_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl (filter p l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_filter in H. destruct H. assumption.
Qed.
(* end hide *)

Lemma Incl_filter_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl l (filter p l) <-> filter p l = l.
(* begin hide *)
Proof.
  unfold Incl. split.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      case_eq (p h); intros; rewrite H0 in *.
        rewrite IHt.
          reflexivity.
          intros. specialize (H x ltac:(right; assumption)).
            inversion H; subst; clear H.
              rewrite elem_filter. split; assumption.
              assumption.
        specialize (H h ltac:(left)). rewrite elem_filter in H.
          destruct H. congruence.
    intros -> *. trivial.
Qed.
(* end hide *)

Lemma Incl_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl (takeWhile p l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_takeWhile in H. destruct H. assumption.
Qed.
(* end hide *)

(* begin hide *)
Lemma Incl_takeWhile_conv_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl l (takeWhile p l) -> all p l = true.
Proof.
  unfold Incl. intros.
  assert (forall x : A, elem x l -> p x = true).
    intros. destruct (elem_takeWhile _ _ _ _ (H _ H0)). assumption.
    clear H. induction l as [| h t]; cbn.
      reflexivity.
      destruct (p h) eqn: Hph; cbn.
        apply IHt. intros. apply H0. right. assumption.
        rewrite <- Hph, H0.
          reflexivity.
          left.
Qed.
(* end hide *)

Lemma Incl_takeWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl l (takeWhile p l) <-> takeWhile p l = l.
(* begin hide *)
Proof.
  split; intros.
    apply all_takeWhile'. apply Incl_takeWhile_conv_aux, H.
    rewrite H. apply Incl_refl.
Qed.
(* end hide *)

Lemma Incl_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl (dropWhile p l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_dropWhile in H. assumption.
Qed.
(* end hide *)

Lemma Incl_span :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      Incl b l /\ elem x l /\ Incl e l.
(* begin hide *)
Proof.
  intros. apply span_spec in H. subst. repeat split.
    apply Incl_app_rr, Incl_refl.
    rewrite elem_app. right. left.
    apply Incl_app_rl. constructor. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Incl vs span i Sublist, palindromy *)
(* end hide *)

Lemma Incl_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    Incl (map Some (pmap f l)) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply Incl_refl.
    destruct (f h); cbn; rewrite ?IHt.
      apply Incl_cons. assumption.
      apply Incl_cons''. assumption.
Qed.
(* end hide *)

Lemma Incl_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Incl l1 (intersperse x l2) -> Incl l1 (x :: l2).
(* begin hide *)
Proof.
  unfold Incl; intros.
  specialize (H _ H0). rewrite elem_intersperse in H.
  decompose [and or] H; subst; [right | left]; assumption.
Qed.
(* end hide *)

Lemma Incl_intersperse_conv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    2 <= length l2 -> Incl l1 (x :: l2) -> Incl l1 (intersperse x l2).
(* begin hide *)
Proof.
  unfold Incl; intros.
  specialize (H0 _ H1). rewrite elem_intersperse.
  inversion H0; subst; firstorder.
Qed.
(* end hide *)

Lemma groupBy_elem_incl :
  forall (A : Type) (p : A -> A -> bool) (l g : list A),
    elem g (groupBy p l) -> Incl g l.
(* begin hide *)
Proof.
  intros. revert g H. functional induction @groupBy A p l; intros;
  try rewrite ?e0 in IHl0.
    inversion H.
    inversion H; subst; clear H.
      gb.
      inversion H2.
    gb.
    inversion H; subst; clear H.
      apply Incl_cons, IHl0. left.
      apply Incl_cons'', IHl0. right. assumption.
    inversion H; subst; clear H.
      apply Incl_cons, Incl_nil.
      apply Incl_cons'', IHl0. assumption.
Qed.
(* end hide *)

Lemma Incl_In :
  forall (A : Type) (l1 l2 : list A),
    Incl l1 l2 -> forall x : A, In x l1 -> In x l2.
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite In_elem in *. apply H, H0.
Qed.
(* end hide *)

Lemma Incl_NoDup :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ NoDup l2 /\ ~ NoDup l1.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. repeat split.
    unfold Incl. intros. destruct x. constructor.
    repeat constructor. inversion 1.
    intro. inv H. apply H2. constructor.
Qed.
(* end hide *)

Lemma Incl_Dup :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ Dup l1 /\ ~ Dup l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. repeat split.
    unfold Incl. intros. destruct x. constructor.
    repeat constructor.
    intro. inv H; inv H1.
Qed.
(* end hide *)

Lemma Incl_Rep :
  exists (A : Type) (x : A) (n : nat) (l1 l2 : list A),
    Incl l1 l2 /\ Rep x n l1 /\ ~ Rep x n l2.
(* begin hide *)
Proof.
  exists unit, tt, 2, [tt; tt], [tt]. repeat split.
    unfold Incl. destruct x. constructor.
    repeat constructor.
    intro. inv H; inv H2.
Qed.
(* end hide *)

Lemma Incl_Exists :
  forall (A : Type) (l1 l2 : list A),
    Incl l1 l2 -> forall P : A -> Prop,
      Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite Exists_spec in *.
  destruct H0 as (x & H1 & H2). exists x. split.
    apply H. assumption.
    assumption.
Qed.
(* end hide *)

Lemma Incl_Forall :
  forall (A : Type) (l1 l2 : list A),
    Incl l1 l2 -> forall P : A -> Prop,
      Forall P l2 -> Forall P l1.
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite Forall_spec in *. intros. apply H0, H, H1.
Qed.
(* end hide *)

Lemma Incl_AtLeast :
  exists (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Incl l1 l2 /\ AtLeast P n l1 /\ ~ AtLeast P n l2.
(* begin hide *)
Proof.
  exists unit, (fun _ => True), 2, [tt; tt], [tt]. repeat split.
    unfold Incl. destruct x. constructor.
    repeat constructor.
    intro. inv H.
      inv H4.
      inv H2.
Qed.
(* end hide *)

Lemma Incl_Exactly :
  exists (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Incl l1 l2 /\ Exactly P n l1 /\ ~ Exactly P n l2.
(* begin hide *)
Proof.
  exists unit, (fun _ => True), 2, [tt; tt], [tt]. repeat split.
    unfold Incl. destruct x. constructor.
    repeat constructor.
    intro. inv H.
      inv H4.
      contradiction.
Qed.
(* end hide *)

Lemma Incl_AtMost :
  exists (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Incl l1 l2 /\ AtMost P n l2 /\ ~ AtMost P n l1.
(* begin hide *)
Proof.
  exists unit, (fun _ => True), 1, [tt; tt], [tt]. repeat split.
    unfold Incl. destruct x. constructor.
    apply AM_skip. constructor.
    intro. inv H.
      contradiction.
      inv H2. contradiction.
Qed.
(* end hide *)

Lemma Sublist_Incl :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  intros. unfold Incl. apply Sublist_elem. assumption.
Qed.
(* end hide *)

Lemma Incl_Sublist :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ ~ Sublist l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. split.
    unfold Incl. destruct x. constructor.
    intro. inv H. inv H2.
Qed.
(* end hide *)

Lemma Prefix_Incl :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  intros. unfold Incl. apply Prefix_elem. assumption.
Qed.
(* end hide *)

Lemma Incl_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true; true], [true]. split.
    unfold Incl. intros. inv H.
      constructor.
      assumption.
    intro. inv H. inv H1.
Qed.
(* end hide *)

Lemma Subseq_Incl :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  intros. unfold Incl. apply Subseq_elem. assumption.
Qed.
(* end hide *)

Lemma Incl_Subseq :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ ~ Subseq l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. split.
    unfold Incl. destruct x. constructor.
    intro. inv H.
      inv H1.
      inv H2.
Qed.
(* end hide *)

(** ** Listy jako zbiory *)

(** Zdefiniuj relację [SetEquiv]. Zdanie [SetEquiv l1 l2] zachodzi,
    gdy listy [l1] i [l2] mają te same elementy, choć niekoniecznie
    w tej samej kolejności czy ilości.

    Przykłady: *)

(** [SetEquiv [1; 1; 2] [2; 2; 1]] zachodzi. *)

(** [SetEquiv [1; 2; 3; 3] [2; 2; 3; 3; 4]] nie zachodzi. *)

(* begin hide *)
Definition SetEquiv {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 <-> elem x l2.
(* end hide *)

Lemma SetEquiv_Incl :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <-> Incl l1 l2 /\ Incl l2 l1.
(* begin hide *)
Proof.
  unfold SetEquiv, Incl. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_refl :
  forall (A : Type) (l : list A), SetEquiv l l.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_sym :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <-> SetEquiv l2 l1.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    SetEquiv l1 l2 -> SetEquiv l2 l3 -> SetEquiv l1 l3.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_nil_l :
  forall (A : Type) (l : list A),
    SetEquiv [] l -> l = [].
(* begin hide *)
Proof.
  unfold SetEquiv. destruct l as [| h t]; intros.
    reflexivity.
    assert (elem h []).
      rewrite H. left.
      inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_nil_r :
  forall (A : Type) (l : list A),
    SetEquiv l [] -> l = [].
(* begin hide *)
Proof.
  intros. apply SetEquiv_nil_l. rewrite SetEquiv_sym. assumption.
Qed.
(* end hide *)

Lemma SetEquiv_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_cons'. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_cons_conv :
  exists (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv (x :: l1) (x :: l2) /\ ~ SetEquiv l1 l2.
(* begin hide *)
Proof.
  exists unit, tt, [tt], []. unfold SetEquiv. firstorder.
    destruct x. constructor.
    destruct x. constructor.
    intro. assert (elem tt []).
      rewrite <- H. constructor.
      inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_cons' :
  exists (A : Type) (x : A) (l : list A),
    ~ SetEquiv l (x :: l).
(* begin hide *)
Proof.
  exists unit, tt, []. unfold SetEquiv. intro.
  assert (elem tt []).
    rewrite H. constructor.
    inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_snoc_cons :
  forall (A : Type) (x : A) (l : list A),
    SetEquiv (snoc x l) (x :: l).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite elem_snoc, elem_cons'. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_snoc. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_comm :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv (l1 ++ l2) (l2 ++ l1).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_l :
  forall (A : Type) (l1 l2 l : list A),
    SetEquiv l1 l2 -> SetEquiv (l ++ l1) (l ++ l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_r :
  forall (A : Type) (l1 l2 l : list A),
    SetEquiv l1 l2 -> SetEquiv (l1 ++ l) (l2 ++ l).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_rev :
  forall (A : Type) (l : list A), SetEquiv (rev l) l.
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite elem_rev. reflexivity.
Qed.
(* end hide *)

Lemma SetEquiv_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (map f l1) (map f l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_map_conv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_join :
  forall (A : Type) (l1 l2 : list (list A)),
    SetEquiv l1 l2 -> SetEquiv (join l1) (join l2).
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl in *. destruct H. split.
    apply Incl_join. assumption.
    apply Incl_join. assumption.
Qed.
(* end hide *)

Lemma SetEquiv_replicate :
  forall (A : Type) (n : nat) (x : A),
    SetEquiv (replicate n x) (if isZero n then [] else [x]).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. destruct n; cbn.
    reflexivity.
    rewrite elem_cons', elem_replicate. split; intros.
      decompose [and or] H; subst; constructor.
      inv H.
        left. reflexivity.
        inv H2.
Qed.
(* end hide *)

Lemma SetEquiv_replicate' :
  forall (A : Type) (n m : nat) (x : A),
    m <> 0 -> n <> 0 -> SetEquiv (replicate m x) (replicate n x).
(* begin hide *)
Proof.
  intros. eapply SetEquiv_trans.
    apply SetEquiv_replicate.
    apply SetEquiv_sym. eapply SetEquiv_trans.
      apply SetEquiv_replicate.
      destruct n, m; try contradiction; cbn. apply SetEquiv_refl.
Qed.
(* end hide *)

Lemma SetEquiv_nth :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <->
    (forall n : nat, exists m : nat, nth n l1 = nth m l2) /\
    (forall n : nat, exists m : nat, nth m l1 = nth n l2).
(* begin hide *)
(* TODO : SetEquiv_nth *)
Proof.
  split; intros.
    rewrite SetEquiv_Incl in H. destruct H.
      rewrite Incl_nth in H. rewrite Incl_nth in H0.
      split; intros.
        destruct (nth n l1) eqn: Heq1.
          destruct (H _ _ Heq1) as (m & H'). exists m. symmetry. assumption.
          exists (length l2). rewrite nth_length_ge; reflexivity.
        destruct (nth n l2) eqn: Heq1.
          destruct (H0 _ _ Heq1) as (m & H'). exists m. assumption.
          exists (length l1). rewrite nth_length_ge; reflexivity.
    destruct H. rewrite SetEquiv_Incl. split.
      rewrite Incl_nth. intros. destruct (H n1) as (n2 & Hn2).
        exists n2. rewrite <- Hn2. assumption.
      rewrite Incl_nth. intros. destruct (H0 n1) as (n2 & Hn2).
        exists n2. rewrite Hn2. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Lemma SetEquiv_remove :
  exists (A : Type) (l1 l1' l2 l2' : list A) (n1 n2 : nat),
    remove match remove n l with
    | None => True
    | Some (_, l') => SetEquiv l' l
    end.
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      apply SetEquiv_cons'.
      specialize (IHt n'). destruct (remove n' t).
        destruct p. apply SetEquiv_cons, IHt.
        trivial.
Qed.*)
(* end hide *)

Lemma SetEquiv_take :
  forall (A : Type) (l : list A) (n : nat),
    SetEquiv (take n l) l <-> Incl (drop n l) (take n l).
(* begin hide *)
Proof.
  split; intros.
    rewrite SetEquiv_Incl in H. destruct H. apply Incl_trans with l.
      apply Incl_drop.
      apply H0.
    rewrite SetEquiv_Incl. split.
      apply Incl_take.
      rewrite <- (app_take_drop _ l n) at 1. rewrite Incl_app_l. split.
        apply Incl_refl.
        assumption.
Qed.
(* end hide *)

Lemma SetEquiv_drop :
  forall (A : Type) (n : nat) (l : list A),
    SetEquiv (drop n l) l <-> Incl (take n l) (drop n l).
(* begin hide *)
Proof.
  split; intros.
    rewrite SetEquiv_Incl in H. destruct H. apply Incl_trans with l.
      apply Incl_take.
      apply H0.
    rewrite SetEquiv_Incl. split.
      apply Incl_drop.
      rewrite <- (app_take_drop _ l n) at 1. rewrite Incl_app_l. split.
        assumption.
        apply Incl_refl.
Qed.
(* end hide *)

Lemma SetEquiv_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (filter p l) l <-> all p l = true.
(* begin hide *)
Proof.
  split.
    intros. rewrite SetEquiv_Incl in H. destruct H.
      rewrite Incl_filter_conv in H0. rewrite <- H0, all_filter.
        reflexivity.
    induction l as [| h t]; cbn; intros.
      apply SetEquiv_refl.
      destruct (p h) eqn: Hph; cbn in *.
        apply SetEquiv_cons, IHt, H.
        congruence.
Qed.
(* end hide *)

Lemma SetEquiv_filter' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  unfold SetEquiv; split; intros.
    rewrite elem_filter in *. firstorder.
    rewrite elem_filter in *. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (takeWhile p l) l <-> all p l = true.
(* begin hide *)
Proof.
  split.
    intros. rewrite SetEquiv_Incl in H. destruct H.
      rewrite Incl_takeWhile_conv in H0. rewrite <- H0, all_takeWhile.
        reflexivity.
    induction l as [| h t]; cbn; intros.
      apply SetEquiv_refl.
      destruct (p h) eqn: Hph; cbn in *.
        apply SetEquiv_cons, IHt, H.
        congruence.
Qed.
(* end hide *)

Lemma SetEquiv_dropWhile :
  exists (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (dropWhile p l) l /\ any p l = true.
(* begin hide *)
Proof.
  exists bool, id, [true; false; true; false]. cbn. split.
    unfold SetEquiv. firstorder; destruct x; repeat constructor.
    reflexivity.
Qed.
(* end hide *)

Lemma SetEquiv_pmap :
  exists (A B : Type) (f : A -> option B) (l : list A),
    ~ SetEquiv (map Some (pmap f l)) (map f l).
(* begin hide *)
Proof.
  exists bool, unit, (fun b : bool => if b then Some tt else None),
         [true; false].
    cbn. unfold SetEquiv. intro. assert (elem None [Some tt]).
      rewrite H. repeat constructor.
      inv H0. inv H3.
Qed.
(* end hide *)

Lemma SetEquiv_intersperse :
  forall (A : Type) (x : A) (l : list A),
    2 <= length l -> SetEquiv (intersperse x l) (x :: l).
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl. split.
    apply Incl_intersperse. apply Incl_refl.
    apply Incl_intersperse_conv.
      assumption.
      apply Incl_refl.
Qed.
(* end hide *)

Lemma SetEquiv_intersperse_conv :
  forall (A : Type) (x : A) (l : list A),
    SetEquiv (intersperse x l) (x :: l) ->
      elem x l \/ 2 <= length l.
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl in H. destruct H.
  destruct l as [| h1 [| h2 t]]; cbn in *.
    specialize (H0 _ ltac:(left)). inv H0.
    specialize (H0 _ ltac:(left)). inv H0.
      left. constructor.
      inv H3.
    right. apply le_n_S, le_n_S, Nat.le_0_l.
Qed.
(* end hide *)

(* begin hide *)
Ltac se := repeat (cbn in *;
match goal with
| H : SetEquiv [] _ |- _ => apply SetEquiv_nil_l in H; inv H
| H : SetEquiv _ [] |- _ => apply SetEquiv_nil_r in H; inv H
| H : ?P |- ?P => assumption
| |- SetEquiv [] [] => apply SetEquiv_refl
end).
(* end hide *)

Lemma SetEquiv_singl :
  forall (A : Type) (l : list A) (x : A),
    SetEquiv [x] l -> forall y : A, elem y l -> y = x.
(* begin hide *)
Proof.
  intros. apply SetEquiv_Incl in H. destruct H. clear H.
  unfold Incl in H1. specialize (H1 _ H0). inv H1.
    reflexivity.
    inv H3.
Qed.
(* end hide *)

Lemma SetEquiv_pres_intersperse :
  exists (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 /\ ~ SetEquiv (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  exists bool, false, [true], [true; true]. cbn. split.
    unfold SetEquiv. firstorder.
      inv H.
        repeat constructor.
        inv H2.
      repeat (inv H; [repeat constructor | rename H2 into H]). inv H.
    intro. assert (elem false [true]).
      unfold SetEquiv in H. rewrite H. repeat constructor.
      inv H0. inv H3.
Qed.
(* end hide *)

(** ** Listy jako multizbiory *)

Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.

(** Zdefiniuj induktywną relację [Permutation]. Zdanie
    [Permutation l1 l2] zachodzi, gdy listy [l1] i [l2] mają te same
    elementy w tej samej ilości sztuk, ale niekoniecznie w tej samej
    kolejności.

    Przykłady: *)

(** [Permutation [1; 5; 1; 4; 3] [4; 1; 1; 5; 3]] zachodzi. *)

(** [Permutation [0; 0; 2; 6; 7] [7; 0; 2; 0; 6; 0]] nie zachodzi. *)

(** Uwaga: to zadanie jest dużo trudniejsze od reszty zadań dotyczących
    relacji między listami. Jeżeli masz problem z rozwiązaniem, spróbuj
    poszukać gotowca w bibliotece standardowej Coqa. *)

(* begin hide *)
Inductive Permutation {A : Type} : list A -> list A -> Prop :=
| perm_nil : Permutation [] []
| perm_skip : forall (x : A) (l l' : list A),
    Permutation l l' -> Permutation (x :: l) (x :: l')
| perm_swap : forall (x y : A) (l : list A),
    Permutation (y :: x :: l) (x :: y :: l)
| perm_trans : forall l l' l'' : list A,
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

#[global] Hint Constructors Permutation : core.
(* end hide *)

Lemma Permutation_refl :
  forall (A : Type) (l : list A),
    Permutation l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; auto.
Defined.
(* end hide *)

Lemma Permutation_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3.
(* begin hide *)
Proof.
  intros. eapply perm_trans; eauto.
Qed.
(* end hide *)

Lemma Permutation_sym :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation l2 l1.
(* begin hide *)
Proof.
  induction 1; auto. eapply Permutation_trans; eauto.
Qed.
(* end hide *)

#[export]
Instance Permutation_Equivalence:
  forall A : Type, RelationClasses.Equivalence (Permutation (A := A)).
(* begin hide *)
Proof.
  split; red.
    apply Permutation_refl.
    apply Permutation_sym.
    apply Permutation_trans.
Defined.
(* end hide *)

Lemma Permutation_isEmpty :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> isEmpty l1 = isEmpty l2.
(* begin hide *)
Proof.
  induction 1; cbn; congruence.
Qed.
(* end hide *)

Lemma Permutation_nil_l :
  forall (A : Type) (l : list A),
    Permutation [] l -> l = [].
(* begin hide *)
Proof.
  intros. apply Permutation_isEmpty in H. cbn in H.
  destruct l; inv H. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_nil_r :
  forall (A : Type) (l : list A),
    Permutation l [] -> l = [].
(* begin hide *)
Proof.
  intros. apply Permutation_isEmpty in H. cbn in H.
  destruct l; inv H. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_nil_cons_l :
  forall (A : Type) (l : list A) (x : A),
    ~ Permutation [] (x :: l).
(* begin hide *)
Proof.
  intros; intro. apply Permutation_nil_l in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_nil_cons_r :
  forall (A : Type) (l : list A) (x : A),
    ~ Permutation (x :: l) [].
(* begin hide *)
Proof.
  intros; intro. apply Permutation_nil_r in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_nil_app_cons_l :
  forall (A : Type) (l l' : list A) (x : A),
    ~ Permutation [] (l ++ x :: l').
(* begin hide *)
Proof.
  intros; intro. apply (Permutation_isEmpty) in H.
  rewrite isEmpty_app in H. destruct l; inv H.
Qed.
(* end hide *)

#[export]
Instance Permutation_cons :
  forall A : Type,
    Proper (eq ==> @Permutation A ==> @Permutation A) (@cons A).
(* begin hide *)
Proof.
  unfold Proper, respectful. intros; subst; auto.
Defined.
(* end hide *)

Lemma Permutation_ind' :
  forall (A : Type) (P : list A -> list A -> Prop),
    P [] [] ->
    (forall x l l', Permutation l l' -> P l l' -> P (x :: l) (x :: l')) ->
    (forall x y l l', Permutation l l' -> P l l' ->
      P (y :: x :: l) (x :: y :: l')) ->
    (forall l l' l'', Permutation l l' -> P l l' -> Permutation l' l'' ->
      P l' l'' -> P l l'') ->
    forall l l', Permutation l l' -> P l l'.
(* begin hide *)
Proof.
  intros A P Hnil Hskip Hswap Htrans.
  induction 1.
    apply Hnil.
    apply Hskip; assumption.
    apply Hswap.
      reflexivity.
      induction l.
        assumption.
        apply Hskip.
          reflexivity.
          assumption.
    apply Htrans with l'; assumption.
Qed.
(* end hide *)

Inductive Elem {A : Type} (x : A) : list A -> list A -> Prop :=
| es_here :
    forall l : list A, Elem x l (x :: l)
| es_there :
    forall (y : A) (l1 l2 : list A),
      Elem x l1 l2 -> Elem x (y :: l1) (y :: l2).

Lemma Elem_spec :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Elem x l1 l2 -> exists l21 l22 : list A,
      l2 = l21 ++ x :: l22 /\ l1 = l21 ++ l22.
(* begin hide *)
Proof.
  induction 1.
    exists [], l. split; reflexivity.
    destruct IHElem as (l21 & l22 & IH1 & IH2); subst.
      exists (y :: l21), l22. split; reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Elem :
  forall (A : Type) (x : A) (l l' : list A),
    Elem x l l' -> Permutation l' (x :: l).
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    apply perm_trans with (y :: x :: l1); constructor; assumption.
Qed.
(* end hide *)

Lemma Elem_Permutation :
  forall (A : Type) (x : A) (l1 l1' : list A),
    Elem x l1 l1' -> forall l2' : list A,
      Permutation l1' l2' -> exists l2 : list A, Elem x l2 l2'.
(* begin hide *)
Proof.
  intros. revert x l1 H. induction H0; intros.
    inv H.
    inv H.
      eexists. constructor.
      destruct (IHPermutation _ _ H3) as (l2 & IH).
        exists (x :: l2). constructor. assumption.
    inv H.
      eexists. do 2 constructor.
      inv H2.
        eexists. constructor.
        eexists. do 2 constructor. eassumption.
    destruct (IHPermutation1 _ _ H) as (l2 & IH1).
      destruct (IHPermutation2 _ _ IH1) as (l2' & IH2).
        exists l2'. assumption.
Qed.
(* end hide *)

Lemma Permutation_Elems :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> forall (x : A) (l1' l2' : list A),
      Elem x l1' l1 -> Elem x l2' l2 ->
        Permutation l1' l2'.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H0.
    inv H0; inv H1.
      assumption.
      rewrite H. eapply Permutation_Elem. assumption.
      rewrite <- H. symmetry. apply Permutation_Elem. assumption.
      constructor. eapply IHPermutation; eassumption.
    repeat match goal with
    | H : Elem _ _ (_ :: _) |- _ => inv H
    | |- Permutation (?x :: _) (?x :: _) => constructor
    | H : ?G |- ?G => assumption
    | |- Permutation ?x ?x => reflexivity
    end.
      symmetry. apply Permutation_Elem. assumption.
      rewrite perm_swap. constructor. symmetry.
        apply Permutation_Elem. assumption.
      apply Permutation_Elem. assumption.
      rewrite perm_swap. constructor. apply Permutation_Elem. assumption.
      admit. (* Za mało indukcji *)
    destruct (@Elem_Permutation _ _ _ _ H1 _ H) as (l3 & IH).
      specialize (IHPermutation1 _ _ _ H1 IH).
      specialize (IHPermutation2 _ _ _ IH H2).
      rewrite IHPermutation1, <- IHPermutation2. reflexivity.
Restart.
  intro.
  apply (@Permutation_ind' _
    (fun l1 l2 => forall x l1' l2',
      Elem x l1' l1 -> Elem x l2' l2 -> Permutation l1' l2'));
  intros.
    inv H0.
    inv H1; inv H2.
      assumption.
      rewrite H. eapply Permutation_Elem. assumption.
      rewrite <- H. symmetry. apply Permutation_Elem. assumption.
      constructor. eapply H0; eassumption.
    repeat match goal with
    | H : Elem _ _ (_ :: _) |- _ => inv H
    | |- Permutation (?x :: _) (?x :: _) => constructor
    | H : ?G |- ?G => assumption
    end.
      rewrite <- H. symmetry. apply Permutation_Elem. assumption.
      rewrite perm_swap, <- H. constructor. symmetry.
        apply Permutation_Elem. assumption.
      rewrite H. apply Permutation_Elem. assumption.
      rewrite perm_swap, H. constructor. apply Permutation_Elem. assumption.
      rewrite perm_swap. do 2 constructor. eapply H0; eassumption.
    destruct (@Elem_Permutation _ _ _ _ H3 _ H) as (l3 & IH).
      specialize (H0 _ _ _ H3 IH). specialize (H2 _ _ _ IH H4).
      rewrite H0, <- H2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_cons_inv :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Permutation (x :: l1) (x :: l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros.
  apply Permutation_Elems with (x := x) (l1 := x :: l1) (l2 := x :: l2).
    assumption.
    1-2: constructor.
Qed.
(* end hide *)

(* begin hide *)
(*
Lemma Permutation_cons_aux :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation (x :: l1) l2 ->
      exists l21 l22 : list A, l2 = l21 ++ x :: l22.
Proof.
  intros. pose (@Permutation_In _ _ _ H x).
  assert (In x (x :: l1)).
    left. reflexivity.
    rewrite i in H0. apply In_spec. assumption.
Qed.
*)
(* end hide *)

Lemma Permutation_length :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> length l1 = length l2.
(* begin hide *)
Proof.
  induction 1; cbn; congruence.
Qed.
(* end hide *)

Lemma Permutation_length' :
  forall A : Type,
    Proper (@Permutation A ==> eq) (@length A).
(* begin hide *)
Proof.
  unfold Proper, respectful; intros.
  apply Permutation_length. assumption.
Qed.
(* end hide *)

Lemma Permutation_length_1:
  forall (A : Type) (l1 l2 : list A),
    length l1 = 1 -> Permutation l1 l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction 2; cbn in *.
    reflexivity.
    destruct l, l'; cbn in *.
      reflexivity.
      apply Permutation_nil_l in H0. inv H0.
      inv H.
      inv H.
    inv H.
    rewrite IHPermutation1, IHPermutation2.
      reflexivity.
      apply Permutation_length in H0_. rewrite <- H0_. assumption.
      assumption.
Qed.
(* end hide *)

Lemma Permutation_singl :
  forall (A : Type) (a b : A),
    Permutation [a] [b] -> a = b.
(* begin hide *)
Proof.
  intros. apply Permutation_length_1 in H.
    inv H. reflexivity.
    cbn. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_length_1_inv:
  forall (A : Type) (x : A) (l : list A),
    Permutation [x] l -> l = [x].
(* begin hide *)
Proof.
  destruct l as [| y [| z t]]; intros.
    symmetry in H. apply Permutation_nil_l in H. inversion H.
    apply Permutation_singl in H. rewrite H. reflexivity.
    apply Permutation_length in H. cbn in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; repeat constructor.
    assumption.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_cons_snoc :
  forall (A : Type) (l : list A) (x : A),
    Permutation (x :: l) (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite perm_swap. constructor. apply IHt.
Qed.
(* end hide *)

Lemma Permutation_cons_snoc' :
  forall (A : Type) (l : list A) (x : A),
    Permutation (x :: l) (l ++ [x]).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite perm_swap. constructor. apply IHt.
Qed.
(* end hide *)

Lemma Permutation_app_l :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation l1 l2 -> Permutation (l3 ++ l1) (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros; auto.
Qed.
(* end hide *)

Lemma Permutation_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation l1 l2 -> Permutation (l1 ++ l3) (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; cbn; intros; auto.
    apply Permutation_refl.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_app :
  forall (A : Type) (l1 l1' l2 l2' : list A),
    Permutation l1 l1' -> Permutation l2 l2' ->
      Permutation (l1 ++ l2) (l1' ++ l2').
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    assumption.
    constructor. apply IHPermutation. assumption.
    rewrite perm_swap. do 2 constructor. apply Permutation_app_l, H.
    rewrite (IHPermutation1 H1). apply Permutation_app_r. assumption.
Qed.
(* end hide *)

#[export]
Instance Permutation_app':
  forall A : Type,
    Proper (@Permutation A ==> @Permutation A ==> @Permutation A) (@app A).
(* begin hide *)
Proof.
  unfold Proper, respectful.
  intros. apply Permutation_app; assumption.
Defined.
(* end hide *)

Lemma Permutation_add_inside :
  forall (A : Type) (x : A) (l1 l2 l1' l2' : list A),
    Permutation l1 l1' -> Permutation l2 l2' ->
      Permutation (l1 ++ x :: l2) (l1' ++ x :: l2').
(* begin hide *)
Proof.
  intros. rewrite H, H0. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_cons_middle :
  forall (A : Type) (l1 l2 l3 : list A) (x : A),
    Permutation l1 (l2 ++ l3) -> Permutation (x :: l1) (l2 ++ x :: l3).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    apply Permutation_nil_l in H. destruct l2, l3; inv H.
      cbn. reflexivity.
    rewrite H. rewrite app_cons_r, <- app_cons_l. apply Permutation_app.
      apply Permutation_cons_snoc'.
      reflexivity.
Qed.
(* end hide *)

Lemma Permutation_middle :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Permutation (l1 ++ x :: l2) (x :: (l1 ++ l2)).
(* begin hide *)
Proof.
  intros. symmetry. apply Permutation_cons_middle. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_app_comm :
  forall (A : Type) (l1 l2 : list A),
    Permutation (l1 ++ l2) (l2 ++ l1).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    rewrite Permutation_cons_middle.
      reflexivity.
      apply IHt1.
Qed.
(* end hide *)

(* begin hide *)
(*
Lemma Permutation_app_inv :
  forall (A : Type) (l1 l2 l3 l4 : list A) (x : A),
    Permutation (l1 ++ x :: l2) (l3 ++ x :: l4) ->
    Permutation (l1 ++ l2) (l3 ++ l4).
Proof.
  intros. rewrite ?Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
*)
(* end hide *)

Lemma Permutation_app_inv_l :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation (l1 ++ l2) (l1 ++ l3) -> Permutation l2 l3.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    assumption.
    apply IHt. apply Permutation_cons_inv in H. assumption.
Qed.
(* end hide *)

Lemma Permutation_app_inv_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation (l1 ++ l3) (l2 ++ l3) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros.
  rewrite (Permutation_app_comm _ l1 l3) in H.
  rewrite (Permutation_app_comm _ l2 l3) in H.
  apply Permutation_app_inv_l in H. assumption.
Qed.
(* end hide *)

Lemma Permutation_rev :
  forall (A : Type) (l : list A),
    Permutation (rev l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    symmetry. rewrite <- Permutation_cons_snoc. constructor.
      symmetry. assumption.
Qed.
(* end hide *)

#[export]
Instance Permutation_rev' :
  forall A : Type,
    Proper (@Permutation A ==> @Permutation A) (@rev A).
(* begin hide *)
Proof.
  unfold Proper, respectful; intros.
  rewrite ?Permutation_rev. assumption.
Qed.
(* end hide *)

Lemma Permutation_map:
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; try constructor.
    assumption.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_map':
  forall (A B : Type) (f : A -> B),
    Morphisms.Proper
      (Morphisms.respectful (Permutation (A:=A)) (Permutation (A:=B)))
      (map f).
(* begin hide *)
Proof.
  unfold Proper, respectful. induction 1; cbn; try constructor.
    assumption.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Permutation l1 l2 -> Permutation (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    apply Permutation_app_l, IHPermutation.
    rewrite Permutation_app_comm, <- app_assoc.
      apply Permutation_app_l, Permutation_app_comm.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_join_rev :
  exists (A : Type) (l1 l2 : list (list A)),
    Permutation (join l1) (join l2) /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [[]]. cbn. split.
    reflexivity.
    intro. apply Permutation_length in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Permutation (replicate n x) (replicate m x) <-> n = m.
(* begin hide *)
Proof.
  split.
    revert m x. induction n as [| n']; cbn; intros.
      apply Permutation_length in H. destruct m; inversion H. reflexivity.
      destruct m as [| m'].
        apply Permutation_length in H; cbn in H. inv H.
        apply f_equal, (IHn' m' x), Permutation_cons_inv with x, H.
    intros ->. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(*
Lemma Permutation_cons_middle_inv :
  forall (A : Type) (l l1 l2 : list A) (x : A),
    Permutation (x :: l) (l1 ++ x :: l2) -> Permutation l (l1 ++ l2).
Proof.
  intros. rewrite Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
*)
(* end hide *)

Lemma Permutation_In :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> (forall x : A, In x l1 <-> In x l2).
(* begin hide *)
Proof.
  induction 1; cbn; firstorder.
Qed.
(* end hide *)

Lemma Permutation_in :
  forall (A : Type) (l l' : list A) (x : A),
    Permutation l l' -> In x l -> In x l'.
(* begin hide *)
Proof.
  induction 1; intros; cbn; auto.
    inversion H0; auto.
    inversion H; auto. inversion H0; auto.
Qed.
(* end hide *)

Lemma Permutation_in' :
  forall A : Type,
    Proper (eq ==> @Permutation A ==> iff) (@In A).
(* begin hide*)
Proof.
  unfold Proper, respectful; intros.
  subst. split; intro H; eapply Permutation_in; eauto.
  symmetry. assumption.
Qed.
(* end hide *)

Lemma Permutation_replicate' :
  forall (A : Type) (n : nat) (x y : A),
    Permutation (replicate n x) (replicate n y) <-> n = 0 \/ x = y.
(* begin hide *)
Proof.
  split.
    revert x y. induction n as [| n']; cbn; intros.
      left. reflexivity.
      right. assert (H' := @Permutation_in A _ _ x H ltac:(left; reflexivity)).
        inv H'. reflexivity.
        apply In_replicate in H0. destruct H0. symmetry. assumption.
    destruct 1; rewrite H; reflexivity.
Qed.
(* end hide *)

Lemma Permutation_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Permutation (iterate f n x) (iterate f m x) <-> n = m.
(* begin hide *)
Proof.
  split.
    revert f m x. induction n as [| n']; cbn; intros.
      apply Permutation_length in H. destruct m; inversion H. reflexivity.
      destruct m as [| m'].
        apply Permutation_length in H; cbn in H. inv H.
        apply f_equal, (IHn' f m' (f x)), Permutation_cons_inv with x, H.
    intros ->. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_iterate' :
  forall (A : Type) (f : A -> A) (n : nat) (x y : A),
    Permutation (iterate f n x) (iterate f n y) ->
      n = 0 \/ exists k : nat, k < n /\ iter f k y = x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    left. reflexivity.
    right. pose (H' := @Permutation_in A _ _ x H ltac:(left; reflexivity)).
      inv H'. exists 0. split.
        apply le_n_S, Nat.le_0_l.
        cbn. reflexivity.
      apply In_iterate in H0. destruct H0 as (k & H1 & H2).
        exists (S k). split.
          now apply Nat.succ_lt_mono in H1.
          cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Permutation_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    Permutation (insert l n x) (x :: l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite perm_swap. constructor. apply IHt.
Qed.
(* end hide *)

Lemma Permutation_take :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\
      exists n : nat, ~ Permutation (take n l1) (take n l2).
(* begin hide *)
Proof.
  exists bool, [true; false], [false; true]. split.
    constructor.
    exists 1. cbn. intro. apply Permutation_length_1 in H.
      congruence.
      reflexivity.
Qed.
(* end hide *)

Lemma Permutation_drop :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\
      exists n : nat, ~ Permutation (drop n l1) (drop n l2).
(* begin hide *)
Proof.
  exists bool, [true; false], [false; true]. split.
    constructor.
    exists 1. cbn. intro. apply Permutation_length_1 in H.
      congruence.
      reflexivity.
Qed.
(* end hide *)

Lemma Permutation_cycle :
  forall (A : Type) (n : nat) (l : list A),
    Permutation (cycle n l) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn'. rewrite Permutation_cons_snoc. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_filter_cycle :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    Permutation (filter p (cycle n l)) (filter p l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn', filter_snoc; cbn. destruct (p h).
        rewrite Permutation_cons_snoc. reflexivity.
        reflexivity.
Qed.
(* end hide *)

Lemma Permutation_length_2_inv:
  forall (A : Type) (x y : A) (l : list A),
    Permutation [x; y] l -> l = [x; y] \/ l = [y; x].
(* begin hide *)
Proof.
  intros.
  assert (H' := @Permutation_length _ _ _ H).
  destruct l as [| a [| b [| c t]]]; inv  H'.
  assert (H' := @Permutation_In _ _ _ H).
  assert (In x [a; b]).
    rewrite <- H'. left. reflexivity.
    cbn in H0. decompose [or] H0; clear H0; subst.
      left. apply Permutation_cons_inv, Permutation_singl in H. subst.
        reflexivity.
      rewrite (@Permutation_app_comm _ [a] [b]) in H. cbn in H.
        apply Permutation_cons_inv, Permutation_singl in H. subst.
          right. reflexivity.
      contradiction.
Qed.
(* end hide *)

Lemma Permutation_length_2:
  forall (A : Type) (x1 x2 y1 y2 : A),
    Permutation [x1; x2] [y1; y2] ->
      x1 = y1 /\ x2 = y2 \/ x1 = y2 /\ x2 = y1.
(* begin hide *)
Proof.
  intros. apply Permutation_length_2_inv in H.
  destruct H; inversion H; subst.
    left. split; reflexivity.
    right. split; reflexivity.
Qed.
(* end hide *)

Lemma Permutation_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Permutation la1 la2 /\ Permutation lb1 lb2 /\
      ~ Permutation (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists bool, bool,
    [true; false], [false; true], [false; true; false], [false; false; true].
  repeat split.
    apply perm_swap.
    do 2 constructor.
    cbn. intro. apply Permutation_length_2 in H. firstorder congruence.
Qed.
(* end hide *)

Lemma Permutation_zipWith :
  exists
    (A B C : Type) (f : A -> B -> C)
    (la1 la2 : list A) (lb1 lb2 : list B),
      Permutation la1 la2 /\
      Permutation lb1 lb2 /\
      ~ Permutation (zipWith f la1 lb1) (zipWith f la2 lb2).
(* begin hide *)
Proof.
  destruct (Permutation_zip)
    as (A & B & la1 & la2 & lb1 & lb2 & H1 & H2 & H3).
  exists A, B, (prod A B), pair, la1, la2, lb1, lb2. repeat split.
    1-2: assumption.
    rewrite ?zipWith_pair. assumption.
Qed.
(* end hide *)

Lemma Permutation_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> any p l1 = any p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. destruct (p x); reflexivity.
    destruct (p x), (p y); reflexivity.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_all :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> all p l1 = all p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. destruct (p x); reflexivity.
    destruct (p x), (p y); reflexivity.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1; cbn; try destruct (p x); try destruct (p y); congruence.
Qed.
(* end hide *)

Lemma Permutation_count_replicate_filter :
  forall (A : Type) (p : A -> bool) (l b e : list A) (x : A),
    span p l = Some (b, x, e) ->
      Permutation l (replicate (count p l) x ++ b ++ e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      cbn. inv H. constructor. apply IHt.
Abort.
(* end hide *)

Lemma Permutation_count_conv :
  forall (A : Type) (l1 l2 : list A),
    (forall p : A -> bool, count p l1 = count p l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma Permutation_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    destruct (p x); rewrite IHPermutation; reflexivity.
    destruct (p x), (p y); try constructor; reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_takeWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 /\
    ~ Permutation (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists bool, id, [true; false], [false; true]. cbn. split.
    constructor.
    intro. apply Permutation_nil_r in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_dropWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 /\
    ~ Permutation (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  exists bool, id, [true; false], [false; true]. cbn. split.
    constructor.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_span :
  forall (A : Type) (p : A -> bool) (l b e : list A) (x : A),
    span p l = Some (b, x, e) -> Permutation l (b ++ x :: e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. cbn. reflexivity.
      destruct (span p t) eqn: Heq.
        destruct p0, p0. inv H. cbn. constructor. apply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma Permutation_removeFirst :
  forall (A : Type) (p : A -> bool) (l l' : list A) (x : A),
    removeFirst p l = Some (x, l') -> Permutation l (x :: l').
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. reflexivity.
      destruct (removeFirst p t) eqn: Heq.
        destruct p0. inv H. rewrite perm_swap. constructor. apply IHt.
          reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma Permutation_intersperse_replicate :
  forall (A : Type) (x : A) (l : list A),
    Permutation (intersperse x l) (replicate (length l - 1) x ++ l).
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn.
    reflexivity.
    destruct t; cbn in *.
      reflexivity.
      destruct (intersperse x t); inv e0.
    rewrite Nat.sub_0_r. destruct t; cbn in *.
      inv e0.
      destruct (intersperse x t); inv e0; rewrite Nat.sub_0_r in *.
        rewrite perm_swap. constructor.
          rewrite <- Permutation_cons_middle.
            constructor. apply IHl0.
            reflexivity.
        rewrite perm_swap. constructor. rewrite Permutation_app_comm in *.
          cbn in *. do 2 constructor. apply Permutation_cons_inv in IHl0.
            assumption.
Qed.
(* end hide *)

Lemma Permutation_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation (intersperse x l1) (intersperse x l2) <->
    Permutation l1 l2.
(* begin hide *)
Proof.
  split; intros.
    assert (length l1 = length l2).
      destruct (length l1 =? length l2) eqn: Heq.
        apply Nat.eqb_eq in Heq. assumption.
        rewrite Nat.eqb_neq in Heq. apply Permutation_length in H.
          rewrite ?length_intersperse in H. lia.
      rewrite ?Permutation_intersperse_replicate, H0 in H.
        apply Permutation_app_inv_l in H. assumption.
    assert (length l1 = length l2).
      apply Permutation_length. assumption.
      rewrite ?Permutation_intersperse_replicate, H0.
        apply Permutation_app_l. assumption.
Qed.
(* end hide *)

Lemma Permutation_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    destruct (f x); rewrite IHPermutation; reflexivity.
    destruct (f x), (f y); try constructor; reflexivity.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_elem :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall x : A, elem x l1 <-> elem x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?elem_cons', IHPermutation. reflexivity.
    rewrite ?elem_cons'. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_replicate'' :
  forall (A : Type) (n m : nat) (x y : A),
    Permutation (replicate n x) (replicate m y) <->
    n = m /\ (n <> 0 -> m <> 0 -> x = y).
(* begin hide *)
Proof.
  split.
    revert m x y. induction n as [| n']; cbn; intros.
      apply Permutation_nil_l in H. destruct m; inv H. split.
        reflexivity.
        contradiction.
      destruct m as [| m']; cbn in H.
        apply Permutation_nil_r in H. inv H.
        assert (x = y).
          assert (elem x (y :: replicate m' y)).
            rewrite <- Permutation_elem. 2: eassumption. left.
            rewrite elem_cons', elem_replicate in H0. firstorder.
          subst. apply Permutation_cons_inv in H.
            destruct (IHn' _ _ _ H). subst. split; reflexivity.
    destruct 1. subst. rewrite Permutation_replicate'. destruct m as [| m'].
      left. reflexivity.
      right. apply H0; inversion 1.
Qed.
(* end hide *)

Lemma NoDup_Permutation:
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 -> NoDup l2 ->
      (forall x : A, In x l1 <-> In x l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    inversion H0; subst.
      reflexivity.
      assert False.
        rewrite (H1 h). left. reflexivity.
        contradiction.
    destruct l2 as [| h2 t2]; cbn; intros.
      specialize (H1 h1). destruct H1. destruct H1. left. reflexivity.
      inversion H; inversion H0; subst; clear H H0.
        destruct (H1 h1). destruct H.
          left. reflexivity.
          subst. constructor. apply IHt1.
            1-2: assumption.
            split; intro.
              assert (In x (h2 :: t2)).
                rewrite <- H1. right. assumption.
                destruct H2.
                  subst. rewrite In_elem in *. contradiction.
                  assumption.
              assert (In x (h2 :: t1)).
                cbn. rewrite H1. right. assumption.
                destruct H2; subst.
                  rewrite In_elem in *. contradiction.
                  assumption.
          apply In_spec in H. destruct H as (l1 & l2 & HIn); subst.
            rewrite Permutation_middle. rewrite perm_swap. constructor.
            apply IHt1.
              assumption.
              constructor.
                intro. apply H8. apply elem_app_or in H.
                  apply elem_or_app. destruct H.
                    left. assumption.
                    do 2 right. assumption.
                rewrite NoDup_app_comm in H9. inversion H9.
                  rewrite NoDup_app_comm. assumption.
              split; intro.
                assert (In x (h2 :: l1 ++ h1 :: l2)).
                  rewrite <- H1. right. assumption.
                  inversion H2; subst.
                    left. reflexivity.
                    apply In_app_or in H3. destruct H3.
                      right. apply In_or_app. left. assumption.
                      inversion H3; subst.
                        rewrite In_elem in *. contradiction.
                        right. apply In_or_app. right. assumption.
                assert (In x (h2 :: l1 ++ h1 :: l2)).
                  cbn in H. destruct H.
                    subst. left. reflexivity.
                    apply In_app_or in H. destruct H.
                      right. apply In_or_app. left. assumption.
                      right. apply In_or_app. do 2 right. assumption.
                  specialize (H1 x). rewrite <- H1 in H2. destruct H2.
                    subst. destruct H.
                      subst. contradiction H8. apply elem_or_app.
                        right. left.
                      apply In_app_or in H. destruct H.
                        rewrite NoDup_app_comm in H9. inversion H9.
                          subst. contradiction H6. apply elem_or_app.
                            right. rewrite <- In_elem. assumption.
                        rewrite NoDup_app_comm in H9. inversion H9.
                          subst. contradiction H6. apply elem_or_app.
                            left. rewrite <- In_elem. assumption.
                    assumption.
Qed.
(* end hide *)

Lemma NoDup_Permutation_bis:
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> length l2 <= length l1 ->
      Incl l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros A l1 l2 H. revert l2.
  induction H; cbn; intros.
    destruct l2; inv H0. reflexivity.
    destruct l2 as [| h2 t2]; inv H1; unfold Incl in H3.
      specialize (H3 _ ltac:(left)). inv H3.
      assert (H' := H3 _ ltac:(left)). inv H'.
        constructor. apply IHNoDup.
          assumption.
          apply le_S_n. cbn in H2. assumption.
          unfold Incl. intros. assert (elem x (h2 :: t2)).
            apply H3. right. assumption.
            inv H4.
              contradiction.
              assumption.
        assert (exists l1 l2 : list A, t2 = l1 ++ h :: l2).
          apply elem_spec. assumption.
          destruct H1 as (l1 & l2 & Heq). subst.
            rewrite <- Permutation_cons_middle.
              rewrite perm_swap. constructor. apply (IHNoDup (h2 :: l1 ++ l2)).
                constructor.
                  intro. apply H6. rewrite elem_app, ?elem_cons' in *.
                    firstorder.
                rewrite NoDup_app_comm in H7. inv H7.
                  rewrite NoDup_app_comm. assumption.
                cbn in *. rewrite length_app in *. cbn in *. lia.
                unfold Incl. intros.
                  specialize (H3 x ltac:(right; assumption)).
                    repeat (rewrite ?elem_cons', ?elem_app in *).
                      decompose [and or] H3; clear H3.
                        subst. left. reflexivity.
                        right. left. assumption.
                        subst. contradiction.
                        do 2 right. assumption.
                reflexivity.
Qed.
(* end hide *)

Lemma Permutation_NoDup:
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> NoDup l1 -> NoDup l2.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    inv H0. constructor.
      rewrite <- In_elem in *. intro. apply H3. eapply Permutation_in.
        symmetry. eassumption.
        assumption.
      apply IHPermutation. assumption.
    inv H. inv H3. constructor.
      intro. inv H.
        apply H2. left.
        contradiction.
      constructor.
        intro. apply H2. right. assumption.
        assumption.
    apply IHPermutation2, IHPermutation1, H1.
Qed.
(* end hide *)

Lemma Permutation_NoDup':
  forall A : Type,
    Morphisms.Proper
      (Morphisms.respectful (Permutation (A:=A)) iff)
      (NoDup (A:=A)).
(* begin hide *)
Proof.
  unfold Proper, respectful. split; intro.
    eapply Permutation_NoDup; eauto.
    eapply Permutation_NoDup.
      symmetry. all: eassumption.
Qed.
(* end hide *)

Lemma Permutation_Dup :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Dup l1 <-> Dup l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    assert (H' := @Permutation_elem _ _ _ H).
      rewrite ?Dup_cons, ?IHPermutation, H'. reflexivity.
    rewrite ?Dup_cons, ?elem_cons'. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Rep :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall (x : A) (n : nat), Rep x n l1 <-> Rep x n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?Rep_cons, ?IHPermutation. reflexivity.
    rewrite ?Rep_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Exists :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall P : A -> Prop, Exists P l1 <-> Exists P l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?Exists_cons, IHPermutation. reflexivity.
    rewrite ?Exists_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Exists_conv :
  exists (A : Type) (l1 l2 : list A),
    (forall P : A -> Prop, Exists P l1 <-> Exists P l2) /\
    ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt], [tt; tt]. split.
    intro. rewrite ?Exists_cons. firstorder.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_Forall :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall P : A -> Prop, Forall P l1 <-> Forall P l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?Forall_cons, IHPermutation. reflexivity.
    rewrite ?Forall_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat), AtLeast P n l1 <-> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?AtLeast_cons, ?IHPermutation. reflexivity.
    rewrite ?AtLeast_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Exactly :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat), Exactly P n l1 <-> Exactly P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite !Exactly_0_cons, IHPermutation. reflexivity.
      rewrite !Exactly_S_cons, !IHPermutation. reflexivity.
    destruct n as [| [| n']].
      rewrite !Exactly_0_cons. firstorder.
      rewrite !Exactly_S_cons, !Exactly_0_cons. firstorder.
      rewrite !Exactly_S_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat), AtMost P n l1 <-> AtMost P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      rewrite ?AtMost_0, IHPermutation. reflexivity.
      rewrite ?AtMost_S_cons, ?IHPermutation. reflexivity.
    destruct n as [| [| n']]; cbn.
      rewrite ?AtMost_0. firstorder.
      rewrite !AtMost_S_cons, !AtMost_0. firstorder.
      rewrite !AtMost_S_cons. firstorder.
      rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Sublist :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\ ~ Sublist l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    constructor.
    intro. inv H. inv H2. inv H1.
Qed.
(* end hide *)

Lemma Sublist_Permutation :
  exists (A : Type) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [tt]. split.
    constructor.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Prefix_Permutation :
  exists (A : Type) (l1 l2 : list A),
    Prefix l1 l2 /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [tt]. split.
    constructor.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_Subseq :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\ ~ Subseq l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    constructor.
    intro. inv H. inv H2.
      inv H0.
      inv H1.
Qed.
(* end hide *)

Lemma Subseq_Permutation :
  exists (A : Type) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [tt]. split.
    constructor.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_Incl :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite Permutation_elem.
    eassumption.
    symmetry. assumption.
Qed.
(* end hide *)

Lemma Permutation_SetEquiv :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl. split.
    apply Permutation_Incl. assumption.
    apply Permutation_Incl. symmetry. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Permutation vs różne rzeczy

nth

remove

splitAt

unzip

unzipWith
head, tail i uncons
last, init i unsnoc


find i findLast
removeFirst i removeLast
findIndex

findIndices

Poza tym permutacje mają inny styl (można używać symmetry etc).
*)
(* end hide *)

(** ** Listy jako cykle *)

(** Zdefiniuj induktywną relację [Cycle]. Zdanie [Cycle l1 l2] zachodzi,
    gdy listy [l1] i [l2] reprezentują ten sam cykl. Intuicyjnie możesz
    sobie wyobrazić elementy [l1] ułożone po kolei wzdłuż okręgu tak, że
    ostatni element sąsiaduje z pierwszym. Jeżeli da się teraz przekręcić
    ten okrąg tak, żeby uzyskać listę [l2], to znaczy, że [Cycle l1 l2]
    zachodzi.

    Przykłady: *)

(** [Cycle [1; 2; 3; 4; 5] [4; 5; 1; 2; 3]] zachodzi. *)

(** [Cycle [1; 2; 3] [2; 1; 3]] nie zachodzi. *)

(* begin hide *)
Inductive Cycle {A : Type} : list A -> list A -> Prop :=
| Cycle_refl : forall l : list A, Cycle l l
| Cycle_cyc :
    forall (x : A) (l1 l2 : list A),
      Cycle l1 (snoc x l2) -> Cycle l1 (x :: l2).
(* end hide *)

Lemma lt_plus_S :
  forall n m : nat,
    n < m -> exists k : nat, m = S (n + k).
(* begin hide *)
Proof.
  intros n m. revert n.
  induction m as [| m']; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      exists m'. reflexivity.
      apply Nat.succ_lt_mono in H. destruct (IHm' _ H) as (k & ->).
        exists k. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_spec :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 <->
    exists n : nat, n <= length l1 /\ l1 = drop n l2 ++ take n l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      exists 0. rewrite drop_0, take_0, app_nil_r. split.
        apply Nat.le_0_l.
        reflexivity.
      destruct IHCycle as (n & IH1 & IH2). subst.
        destruct (Nat.leb_spec0 n (length l2)).
          rewrite drop_snoc, take_snoc; try assumption.
            exists (S n). cbn. rewrite app_snoc_l. split.
              rewrite <- (@app_take_drop _ l2 n) in l.
                rewrite length_app in *. cbn. lia.
              reflexivity.
          assert (exists k : nat, n = S (length l2 + k)).
            apply lt_plus_S. lia.
            destruct H0 as (k & Hk). subst. rewrite drop_length'.
              rewrite take_length'.
                exists 1. cbn. rewrite drop_0, take_0. split.
                  rewrite length_snoc. lia.
                  apply snoc_app_singl.
                rewrite length_snoc. lia.
              rewrite length_snoc. lia.
    destruct 1 as (n & Hle & H); subst.
      revert l2 Hle. induction n as [| n']; intros.
        rewrite drop_0, take_0, app_nil_r. constructor.
        destruct l2 as [| h t]; cbn.
          constructor.
          destruct (Nat.leb_spec0 (length t) n').
            rewrite drop_length', take_length'.
              constructor.
              1-2: assumption.
            specialize (IHn' (snoc h t)). rewrite drop_snoc in IHn'.
              rewrite take_snoc in IHn'.
                constructor. rewrite app_snoc_l in IHn'. cbn in Hle.
                  apply IHn'. lia.
                lia.
              lia.
Qed.
(* end hide *)

Lemma Cycle_isEmpty :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> isEmpty l1 = isEmpty l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    cbn in *. rewrite isEmpty_snoc in *. assumption.
Qed.
(* end hide *)

Lemma Cycle_nil_l :
  forall (A : Type) (l : list A),
    Cycle [] l -> l = [].
(* begin hide *)
Proof.
  intros. apply Cycle_isEmpty in H. destruct l; inv H. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_nil_r :
  forall (A : Type) (l : list A),
    Cycle l [] -> l = [].
(* begin hide *)
Proof.
  intros. apply Cycle_isEmpty in H. destruct l; inv H. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_length :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> length l1 = length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite length_snoc in IHCycle. assumption.
Qed.
(* end hide *)

Lemma Cycle_cons :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  exists nat, 0, [1; 2; 3], [3; 1; 2]. split.
    constructor. cbn. constructor.
    intro. apply Cycle_spec in H. destruct H as (n & H1 & H2).
      destruct n as [| [| [| [| n']]]]; cbn in H2; inv H2.
Qed.
(* end hide *)

Lemma Cycle_cons_inv :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Cycle  (x :: l1) (x :: l2) /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists nat, 3, [2; 3; 1], [1; 3; 2]. split.
    constructor. cbn. constructor. cbn. constructor.
    intro. apply Cycle_spec in H. destruct H as (n & H1 & H2).
      destruct n as [| [| [| n']]]; inv H2.
Qed.
(* end hide *)

Lemma Cycle_snoc :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  exists nat, 0, [1; 2; 3], [3; 1; 2]. split.
    constructor. cbn. constructor.
    intro. apply Cycle_spec in H. destruct H as (n & H1 & H2).
      destruct n as [| [| [| [| n']]]]; cbn in H2; inv H2.
Qed.
(* end hide *)

Lemma Cycle_sym :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle l2 l1.
(* begin hide *)
Proof.
  intros. rewrite Cycle_spec in *. destruct H as (n & H1 & H2). subst.
  destruct (Nat.leb_spec0 (length l2) n);
  eexists; rewrite drop_app, take_app, drop_drop, take_take, length_drop.
    instantiate (1 := 0). rewrite ?Nat.add_0_r. cbn.
      rewrite Nat.min_0_r, ?take_0, drop_0, ?app_nil_r.
        rewrite drop_length', take_length'; try assumption. split.
          apply Nat.le_0_l.
          reflexivity.
    instantiate (1 := length l2 - n). rewrite Nat.add_comm, Nat.sub_add, drop_length.
      cbn. replace (length l2 - n - (length l2 - n)) with 0.
      rewrite drop_0, take_drop, Nat.add_comm, Nat.sub_add, take_length.
      rewrite Nat.min_0_r, take_0, app_nil_r, app_take_drop. split.
        2: reflexivity.
        all: lia.
Qed.
(* end hide *)

Lemma Cycle_snoc_cons :
  forall (A : Type) (x : A) (l : list A),
    Cycle  (snoc x l) (x :: l).
(* begin hide *)
Proof.
  repeat constructor.
Qed.
(* end hide *)

Lemma Cycle_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Cycle  (x :: l) (snoc x l).
(* begin hide *)
Proof.
  intros. apply Cycle_sym. apply Cycle_snoc_cons.
Qed.
(* end hide *)

Lemma Cycle_cons_snoc' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Cycle l1 (x :: l2) -> Cycle l1 (snoc x l2).
(* begin hide *)
Proof.
  intros. inv H.
    apply Cycle_cons_snoc.
    assumption.
Qed.
(* end hide *)

Lemma Cycle_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Cycle l1 l2 -> Cycle l2 l3 -> Cycle l1 l3.
(* begin hide *)
Proof.
  intros until 1. revert l3.
  induction H; intros.
    assumption.
    apply IHCycle. apply Cycle_sym. apply Cycle_cons_snoc'.
      apply Cycle_sym. assumption.
Qed.
(* end hide *)

Lemma Cycle_app :
  forall (A : Type) (l1 l2 l3 : list A),
    Cycle l1 (l2 ++ l3) -> Cycle l1 (l3 ++ l2).
(* begin hide *)
Proof.
  intros A l1 l2 l3. revert l1 l2.
  induction l3 as [| h t]; cbn; intros.
    rewrite app_nil_r in *. assumption.
    specialize (IHt l1 (snoc h l2)). constructor. rewrite snoc_app.
      apply IHt. rewrite snoc_app_singl, <- app_assoc. cbn. assumption.
Qed.
(* end hide *)

Lemma Cycle_rev :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle (rev l1) (rev l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    apply Cycle_cons_snoc'. rewrite rev_snoc in IHCycle. assumption.
Qed.
(* end hide *)

Lemma Cycle_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor.
    rewrite map_snoc in IHCycle. assumption.
Qed.
(* end hide *)

Lemma Cycle_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Cycle l1 l2 -> Cycle (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    rewrite join_snoc in IHCycle. apply Cycle_app. assumption. 
Qed.
(* end hide *)

Lemma Cycle_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Cycle (replicate n x) (replicate m x) <-> n = m.
(* begin hide *)
Proof.
  split; intros.
    apply Cycle_length in H. rewrite ?length_replicate in H. assumption.
    subst. constructor.
Qed.
(* end hide *)

Lemma Cycle_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Cycle (iterate f n x) (iterate f m x) <-> n = m.
(* begin hide *)
Proof.
  split; intro.
    apply Cycle_length in H. rewrite ?length_iterate in H. assumption.
    subst. constructor.
Qed.
(* end hide *)

Lemma Cycle_iterate' :
  forall (A : Type) (f : A -> A) (n m : nat) (x y : A),
    Cycle (iterate f n x) (iterate f m y) <-> n = m.
(* begin hide *)
Proof.
  split; intro.
    apply Cycle_length in H. rewrite ?length_iterate in H. assumption.
    subst. induction m as [| m']; cbn.
      constructor.
      constructor.
Abort.
(* end hide *)

(* begin hide *)
(* TODO: Cycle vs head, tail, etc. *)
(* end hide *)

Lemma Cycle_nth :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (n : nat) (x : A),
      nth n l1 = Some x -> exists m : nat, nth m l2 = Some x.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    exists n. assumption.
    destruct (IHCycle _ _ H0) as (m & IH).
      destruct (Nat.leb_spec0 (S m) (length l2)).
        rewrite nth_snoc_lt in IH.
          exists (S m). assumption.
          assumption.
        destruct (Nat.eqb_spec m (length l2)).
          exists 0. rewrite e, nth_snoc_eq in IH.
            assumption.
            reflexivity.
          rewrite nth_length_ge in IH.
            inv IH.
            rewrite length_snoc. lia.
Qed.
(* end hide *)

Lemma Cycle_cycle :
  forall (A : Type) (n : nat) (l : list A),
    Cycle (cycle n l) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    intro. apply Cycle_refl.
    destruct l as [| h t]; cbn.
      constructor.
      eapply Cycle_trans.
        apply IHn'.
        constructor. apply Cycle_refl.
Qed.
(* end hide *)

Lemma cycle_Cycle :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> exists n : nat, cycle n l1 = l2.
(* begin hide *)
Proof.
  induction 1.
    exists 0. cbn. reflexivity.
    destruct IHCycle as [n IH]. exists (n + length l2).
      apply (f_equal (cycle (length l2))) in IH.
      rewrite cycle_cycle in IH.
      rewrite IH, (plus_n_O (length l2)).
      rewrite snoc_app_singl, cycle_length_app. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_insert :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (n : nat) (x : A),
      exists m : nat, Cycle (insert l1 n x) (insert l2 m x) .
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    exists n. constructor.
    destruct (IHCycle n x0) as (m & IH). rewrite insert_snoc in IH.
      destruct (m <=? length l2) eqn: Hle.
        exists (S m). constructor. assumption.
        exists 1. rewrite insert_0. do 2 (constructor; cbn). assumption.
Qed.
(* end hide *)

Lemma Cycle_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Cycle la1 la2 /\ Cycle lb1 lb2 /\ ~ Cycle (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists
    bool, bool,
    [true; false], [false; true],
    [false; true; true], [true; true; false].
  repeat split.
    constructor. cbn. constructor.
    constructor. cbn. constructor. cbn. constructor.
    cbn. intro. assert (H' := Cycle_nth _ _ _ H 0 _ eq_refl).
      destruct H' as (m & H'). destruct m as [| [| m']]; inv H'.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Cycle vs zipW, unzip, unzipW *)
(* end hide *)

Lemma Cycle_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 -> any p l1 = any p l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite IHCycle, any_snoc, Bool.orb_comm. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_all :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 -> all p l1 = all p l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite IHCycle, all_snoc, Bool.andb_comm. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_find :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A) (x : A),
    Cycle l1 l2 /\ find p l1 = Some x /\ find p l2 <> Some x.
(* begin hide *)
Proof.
  exists bool, (fun _ => true), [true; false], [false; true], true.
  repeat split.
    constructor. cbn. constructor.
    cbn. inversion 1.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Cycle vs findLast, removeFirst, removeLast *)
(* end hide *)

Lemma Cycle_findIndex :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A) (n : nat),
    Cycle l1 l2 /\ findIndex p l1 = Some n /\ findIndex p l2 <> Some n.
(* begin hide *)
Proof.
  exists bool, (fun b => b), [true; false], [false; true], 0.
  repeat split.
    constructor. cbn. constructor.
    cbn. inversion 1.
Qed.
(* end hide *)

Lemma Cycle_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite IHCycle, count_snoc.
      destruct (p x); rewrite Nat.add_comm; reflexivity.
Qed.
(* end hide *)

Lemma Cycle_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    cbn. rewrite filter_snoc in IHCycle. destruct (p x).
      constructor. assumption.
      assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Cycle vs findIndices *)
(* end hide *)

Lemma Cycle_takeWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists bool, (fun b => b), [true; false], [false; true].
  repeat split.
    constructor. cbn. constructor.
    cbn. inversion 1.
Qed.
(* end hide *)

Lemma Cycle_dropWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  exists bool, (fun b => b), [true; false], [false; true].
  repeat split.
    constructor. cbn. constructor.
    cbn. intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    rewrite pmap_snoc in IHCycle. destruct (f x).
      constructor. assumption.
      assumption.
Qed.
(* end hide *)

Lemma Cycle_intersperse :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  exists nat, 0, [1; 2], [2; 1]. split.
    do 2 constructor.
    cbn. intro. apply Cycle_spec in H. destruct H as (n & H1 & H2).
      destruct n as [| [| [| n']]]; inv H2.
Qed.
(* end hide *)

Lemma Cycle_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite Permutation_cons_snoc. assumption.
Qed.
(* end hide *)

Lemma Cycle_elem :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall x : A, elem x l1 <-> elem x l2.
(* begin hide *)
Proof.
  intros. apply Permutation_elem, Cycle_Permutation. assumption.
Qed.
(* end hide *)

Lemma Cycle_replicate' :
  forall (A : Type) (n m : nat) (x y : A),
    Cycle (replicate n x) (replicate m y) <->
    n = m /\ (n <> 0 -> m <> 0 -> x = y).
(* begin hide *)
Proof.
  split; intros.
    apply Cycle_Permutation, Permutation_replicate'' in H. assumption.
    destruct H. subst. destruct m as [| m']; cbn.
      constructor.
      specialize (H0 ltac:(inversion 1) ltac:(inversion 1)). subst.
        constructor.
Qed.
(* end hide *)

Lemma Cycle_In :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall x : A, In x l1 <-> In x l2.
(* begin hide *)
Proof.
  intros. apply Permutation_In, Cycle_Permutation, H.
Qed.
(* end hide *)

Lemma Cycle_NoDup :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> NoDup l1 -> NoDup l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_NoDup, Cycle_Permutation, H.
Qed.
(* end hide *)

Lemma Cycle_Dup :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Dup l1 -> Dup l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Dup, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Rep :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (x : A) (n : nat),
      Rep x n l1 -> Rep x n l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Rep, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Exists :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Cycle l1 l2 -> Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Exists, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Forall :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Cycle l1 l2 -> Forall P l1 -> Forall P l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Forall, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_AtLeast, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Exactly :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (P : A -> Prop) (n : nat),
      Exactly P n l1 -> Exactly P n l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Exactly, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtMost P n l1 -> AtMost P n l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_AtMost, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Sublist :
  exists (A : Type) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Sublist l1 l2.
(* begin hide *)
Proof.
  exists unit, [], []. split.
    constructor.
    inversion 1.
Qed.
(* end hide *)

Lemma Sublist_Cycle :
  exists (A : Type) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [tt]. split.
    constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    do 2 constructor.
    inversion 1.
Qed.
(* end hide *)

Lemma Prefix_Cycle :
  exists (A : Type) (l1 l2 : list A),
    Prefix l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists bool, [], [false]. split.
    constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_Subseq :
  exists (A : Type) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Subseq l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    do 2 constructor.
    intro. inv H. inv H2.
      inv H0.
      inv H1.
Qed.
(* end hide *)

Lemma Subseq_Cycle :
  exists (A : Type) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists bool, [], [false]. split.
    constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_Incl :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  induction 1.
    apply Incl_refl.
    unfold Incl in *. intros. specialize (IHCycle _ H0).
      rewrite elem_snoc in IHCycle. destruct IHCycle.
        right. assumption.
        subst. left.
Qed.
(* end hide *)

Lemma Incl_Cycle :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. split.
    unfold Incl. destruct x. constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_SetEquiv :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl. split; apply Cycle_Incl.
    assumption.
    apply Cycle_sym. assumption.
Qed.
(* end hide *)

Lemma SetEquiv_Cycle :
  exists (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. split.
    rewrite SetEquiv_Incl; unfold Incl. split; destruct x; constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

(** ** Partycje list (TODO) *)

Module Partition.

Definition Partition
  {A : Type} (ll : list (list A)) (l : list A) : Prop :=
    Permutation (join ll) l.

Lemma Partition_rev :
  forall {A : Type} (ll : list (list A)) (l : list A),
    Partition ll l -> Partition (rev (map rev ll)) (rev l).
Proof.
  unfold Partition. intros.
  rewrite <- rev_join, !Permutation_rev.
  assumption.
Qed.

End Partition.

Module OPartition.

Record OPartition
  {A : Type} (ll : list (list A)) (l : list A) : Prop :=
{
  nonempty : forall l' : list A, elem l' ll -> l' <> [];
  all : join ll = l;
}.

End OPartition.

Module IPartition.

Inductive IPartition {A : Type} : list (list A) -> list A -> Prop :=
| IP_nil : IPartition [] []
| IP_cons :
    forall {ll : list (list A)} {l1 l2 : list A},
      l1 <> [] -> IPartition ll l2 ->
        IPartition (l1 :: ll) (l1 ++ l2).

Lemma IPartition_spec :
  forall {A : Type} {ll : list (list A)} {l : list A},
    IPartition ll l -> join ll = l.
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHIPartition. reflexivity.
Qed.

Lemma IPartition_spec_conv :
  forall {A : Type} (ll : list (list A)) (l : list A),
    (forall l' : list A, elem l' ll -> l' <> []) ->
      join ll = l -> IPartition ll l.
Proof.
  induction ll as [| hh tt]; cbn; intros; subst.
    constructor.
    constructor.
      apply H. constructor.
      apply IHtt.
        intros. apply H. constructor. assumption.
        reflexivity.
Qed.

Lemma IPartition_app :
  forall {A : Type} (ll1 ll2 : list (list A)) (l1 l2 : list A),
    IPartition ll1 l1 -> IPartition ll2 l2 ->
      IPartition (ll1 ++ ll2) (l1 ++ l2).
Proof.
  intros until 1. revert ll2 l2.
  induction H; cbn; intros.
    assumption.
    rewrite <- app_assoc. constructor.
      assumption.
      apply IHIPartition. assumption.
Qed.

Lemma IPartition_rev :
  forall {A : Type} (ll : list (list A)) (l : list A),
    IPartition ll l -> IPartition (map rev (rev ll)) (rev l).
Proof.
  induction 1; cbn.
    constructor.
    rewrite map_snoc, rev_app, snoc_app_singl. apply IPartition_app.
      assumption.
      rewrite <- app_nil_r. constructor.
        intro. apply H. destruct l1.
          reflexivity.
          apply (f_equal length) in H1. rewrite length_rev in H1.
            cbn in H1. inv H1.
        constructor.
Qed.

Lemma IPartition_map :
  forall {A B : Type} {ll : list (list A)} {l : list A},
    IPartition ll l ->
      forall f : A -> B, IPartition (map (map f) ll) (map f l).
Proof.
  induction 1; cbn; intros.
    constructor.
    rewrite map_app. constructor.
      intro. apply H. destruct l1.
        reflexivity.
        inv H1.
      apply IHIPartition.
Qed.

End IPartition.