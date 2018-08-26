Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

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

(** ** Listy jako termy *)

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
    apply lt_S. assumption.
Qed.
(* end hide *)

Lemma Sublist_cons_l :
  forall (A : Type) (x : A) (l : list A), ~ Sublist (x :: l) l.
(* begin hide *)
Proof.
  repeat intro. apply Sublist_length in H. cbn in H. omega.
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
  repeat intro. apply Sublist_length in H. omega.
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
  omega.
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
        apply lt_n_S. apply IHm'. inv H.
          constructor.
          apply Sublist_cons_l' in H2. assumption.
    intro. assert (exists k : nat, m = n + S k).
      revert n H. induction m as [| m']; cbn; intros.
        inv H.
        destruct n as [| n'].
          exists m'. reflexivity.
          destruct (IHm' _ (lt_S_n _ _ H)) as (k & IH). subst.
            exists k. rewrite <- ?plus_n_Sm. cbn. reflexivity.
      destruct H0 as (k & H'). subst.
        rewrite <- Nat.add_succ_comm, replicate_plus_comm, replicate_plus.
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
          apply lt_n_S. assumption.
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
    Sublist (iterate f n x) (iterate f m x) -> False.
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma Sublist_iterate' :
  forall (A : Type) (f : A -> A) (n m : nat) (x y : A),
    Sublist (iterate f n x) (iterate f m y) -> False.
(* begin hide *)
Proof.
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

(* TODO: insert, remove, take *)

Lemma Sublist_drop :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    Sublist l1 l2 -> n < length l1 -> Sublist (drop n l1) (drop n l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct n as [| n']; cbn.
      rewrite drop_0. constructor.
      destruct t; cbn.
        inv H.
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

(* TODO: zipWith, unzip, unzipWith *)

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

(* TODO: Sublist_all *)

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
Abort.
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

Inductive Prefix {A : Type} : list A -> list A -> Prop :=
    | Prefix_nil : forall l : list A, Prefix [] l
    | Prefix_cons :
        forall (x : A) (l1 l2 : list A),
          Prefix l1 l2 -> Prefix (x :: l1) (x :: l2).

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

(* TODO: null *)

Lemma Prefix_length :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> length l1 <= length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma Prefix_snoc :
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
  rewrite length_app, length_rev, plus_comm in H.
  destruct l3.
    rewrite app_nil_r. reflexivity.
    cbn in H. omega.
Qed.
(* end hide *)

Lemma Prefix_rev_r :
  forall (A : Type) (l : list A),
    Prefix l (rev l) -> l = rev l.
(* begin hide *)
Proof.
  intros. apply Prefix_spec in H. destruct H as (l3 & H).
  rewrite H at 1. apply (f_equal length) in H.
  rewrite length_app, length_rev, plus_comm in H.
  destruct l3.
    rewrite app_nil_r. reflexivity.
    cbn in H. omega.
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
      apply le_0_n.
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
    exists 0. cbn. split; [apply le_0_n | reflexivity].
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
            apply le_n_S, le_0_n.
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
      apply le_0_n.
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
      do 2 constructor. specialize (IHPrefix _ x0 (le_0_n (length l1))).
        rewrite ?insert_0 in IHPrefix. inv IHPrefix. assumption.
      constructor. apply IHPrefix. apply le_S_n. assumption.
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

(* TODO: unzip, zipWith, unzipWith *)

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
    apply le_0_n.
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

(* TODO: findLast, removeFirst i removeLast *)

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

(* TODO: groupBy *)

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

(* TODO: In *)

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

(* TODO: Rep *)

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

(* TODO: Exactly - raczej nic z tego *)

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

Inductive Suffix {A : Type} : list A -> list A -> Prop :=
    | Suffix_refl :
        forall l : list A, Suffix l l
    | Suffix_cons :
        forall (x : A) (l1 l2 : list A),
          Suffix l1 l2 -> Suffix l1 (x :: l2).

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
  destruct l2', l1'; cbn in H2; try omega. cbn. reflexivity.
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
        apply Prefix_app_r. assumption.
      intro. specialize (H _ _ H0). rewrite ?rev_inv in H. assumption.
Qed.
(* end hide *)

(** ** Listy jako ciągi *)

Inductive Subseq {A : Type} : list A -> list A -> Prop :=
    | Subseq_nil :
        forall l : list A, Subseq [] l
    | Subseq_cons :
        forall (x : A) (l1 l2 : list A),
          Subseq l1 l2 -> Subseq (x :: l1) (x :: l2)
    | Subseq_skip :
        forall (x : A) (l1 l2 : list A),
          Subseq l1 l2 -> Subseq l1 (x :: l2).

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
    apply le_0_n.
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
      exists l21 l22 : list A, l2 = l21 ++ x :: l22 /\ Subseq l1 l22.
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
      rewrite length_app in H. cbn in H. omega.
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
      apply le_0_n.
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
      apply le_0_n.
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
      inv H0. exists 0. cbn. split; [reflexivity | apply le_0_n].
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
    apply le_0_n.
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

(* TODO:
bind

unzip
zipWith
unzipWith

find i findLast
removeFirst i removeLast
findIndices
*)

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

Definition Incl {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 -> elem x l2.

(** Przyjrzyjmy się powyższej definicji. Intuicyjnie można ją rozumieć tak,
    że [Incl l1 l2] zachodzi, gdy każdy element listy [l1] choć raz występuje
    też na liście [l2]. Udowodnij, że relacja ta ma poniższe właściwości. *)

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

Lemma Incl_app_l :
  forall (A : Type) (l l1 l2 : list A),
    Incl l l1 -> Incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_app_l, H, H0.
Qed.
(* end hide *)

Lemma Incl_app_r :
  forall (A : Type) (l l1 l2 : list A),
    Incl l l2 -> Incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_app_r, H, H0.
Qed.
(* end hide *)

Lemma Incl_app_l_conv :
  forall (A : Type) (l1 l2 : list A),
    Incl (l1 ++ l2) l1 -> Incl l2 l1.
(* begin hide *)
Proof.
  unfold Incl; intros. apply H, elem_app_r, H0.
Qed.
(* end hide *)

Lemma Incl_app_r_conv :
  forall (A : Type) (l1 l2 : list A),
    Incl (l1 ++ l2) l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  unfold Incl; intros. apply H, elem_app_l, H0.
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
    apply Incl_app_l, Incl_refl.
    rewrite elem_app. right. left.
    apply Incl_app_r. constructor. assumption.
Qed.
(* end hide *)

(* TODO: span i Sublist, palindromy *)

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

(** ** Zbiorowa równoważność *)

Definition SetEquiv {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 <-> elem x l2.

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

(* TODO *) Lemma SetEquiv_nth :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <->
    forall n : nat, exists m : nat, nth n l1 = nth m l2.
(* begin hide *)
Proof.
  split; revert l2.
    induction l1 as [| h1 t1]; cbn; intros.
      apply SetEquiv_nil_l in H. subst. exists 42. cbn. reflexivity.
      destruct l2 as [| h2 t2].
        apply SetEquiv_nil_r in H. inv H.
        destruct n as [| n']; cbn.
          exists 0.
Abort.
(* end hide *)

(*Lemma SetEquiv_remove :
  exists (A : Type) (l1 l1' l2 l2' : list A) (n1 n2 : nat),
    remove match remove n l with
        | None => True
        | Some (_, l') => SetEquiv l' l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      apply SetEquiv_cons'.
      specialize (IHt n'). destruct (remove n' t).
        destruct p. apply SetEquiv_cons, IHt.
        trivial.
Qed.
(* end hide *)
*)

(* TODO *) Lemma SetEquiv_take :
  forall (A : Type) (l : list A) (n : nat),
    SetEquiv (take n l) l <-> Incl (drop n l) (take n l).
(* begin hide *)
Proof.
  split; revert n.
    induction l as [| h t]; cbn; intros.
      apply Incl_refl.
      destruct n as [| n']; cbn in *.
        apply SetEquiv_nil_l in H. inv H.
        apply Incl_cons''. apply IHt.
Abort.
(* end hide *)

(* TODO *) Lemma SetEquiv_drop :
  forall (A : Type) (n : nat) (l : list A),
    SetEquiv (drop n l) l <-> Incl (take n l) (drop n l).
(* begin hide *)
Proof.
Abort.
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
    right. apply le_n_S, le_n_S, le_0_n.
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

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    | perm_nil : Permutation [] []
    | perm_skip : forall (x : A) (l l' : list A),
        Permutation l l' -> Permutation (x :: l) (x :: l')
    | perm_swap : forall (x y : A) (l : list A),
        Permutation (y :: x :: l) (x :: y :: l)
    | perm_trans : forall l l' l'' : list A,
        Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Hint Constructors Permutation.

Lemma Permutation_refl :
  forall (A : Type) (l : list A),
    Permutation l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; auto.
Defined.
(* end hide *)

Lemma Permutation_trans :
  forall (A : Type) (l l' l'' : list A),
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.
(* begin hide *)
Proof.
  intros. eapply perm_trans; eauto.
Qed.
(* end hide *)

Lemma Permutation_sym :
  forall (A : Type) (l l' : list A), Permutation l l' -> Permutation l' l.
(* begin hide *)
Proof.
  induction 1; auto. eapply Permutation_trans; eauto.
Qed.
(* end hide *)

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

(*
Lemma Permutation_cons_aux :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation (x :: l1) l2 ->
      exists l21 l22 : list A, l2 = l21 ++ x :: l22.
(* begin hide *)
Proof.
  intros. pose (@Permutation_In _ _ _ H x).
  assert (In x (x :: l1)).
    left. reflexivity.
    rewrite i in H0. apply In_spec. assumption.
Qed.
(* end hide *)
*)

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

(*
Lemma Permutation_app_inv :
  forall (A : Type) (l1 l2 l3 l4 : list A) (x : A),
    Permutation (l1 ++ x :: l2) (l3 ++ x :: l4) ->
    Permutation (l1 ++ l2) (l3 ++ l4).
(* begin hide *)
Proof.
  intros. rewrite ?Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
(* end hide *)
*)

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
    symmetry. rewrite <- Permutation_cons_snoc'. constructor.
      symmetry. assumption.
Qed.
(* end hide *)

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

(*
Lemma Permutation_cons_middle_inv :
  forall (A : Type) (l l1 l2 : list A) (x : A),
    Permutation (x :: l) (l1 ++ x :: l2) -> Permutation l (l1 ++ l2).
(* begin hide *)
Proof.
  intros. rewrite Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
(* end hide *)
*)

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

(* TODO: iterate *)

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
        apply le_n_S, le_0_n.
        cbn. reflexivity.
      apply In_iterate in H0. destruct H0 as (k & H1 & H2).
        exists (S k). split.
          apply lt_n_S. assumption.
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
  exists A, B, _, pair, la1, la2, lb1, lb2. repeat split.
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
    rewrite <- minus_n_O. destruct t; cbn in *.
      inv e0.
      destruct (intersperse x t); inv e0; rewrite <- minus_n_O in *.
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
          rewrite ?length_intersperse in H. omega.
      rewrite ?Permutation_intersperse_replicate, H0 in H.
        apply Permutation_app_inv_l in H. assumption.
    assert (length l1 = length l2).
      apply Permutation_length. assumption.
      rewrite ?Permutation_intersperse_replicate, H0.
        apply Permutation_app_l. assumption.
Qed.

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
                cbn in *. rewrite length_app in *. cbn in *. omega.
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
    rewrite ?Forall_cons', IHPermutation. reflexivity.
    rewrite ?Forall_cons'. firstorder.
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

(* TODO: permutacje mają inny styl (można używać symmetry etc.) *)

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

(* TODO:

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
*)

(** * Niestandardowe reguły indukcyjne *)

(** Wyjaśnienia nadejdą już wkrótce. *)

Fixpoint list_ind_2
  (A : Type) (P : list A -> Prop)
  (H0 : P [])
  (H1 : forall x : A, P [x])
  (H2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
    (l : list A) : P l.
(* begin hide *)
Proof.
  destruct l as [| x [| y l]]; cbn; auto.
  apply H2. apply list_ind_2; auto.
Qed.
(* end hide *)

Lemma list_ind_rev :
  forall (A : Type) (P : list A -> Prop)
    (Hnil : P [])
    (Hsnoc : forall (h : A) (t : list A), P t -> P (t ++ [h]))
      (l : list A), P l.
(* begin hide *)
Proof.
  intros. cut (forall l : list A, P (rev l)); intro.
    specialize (H (rev l)). rewrite <- rev_inv. assumption.
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
    apply (IH t [h]). assumption.
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

(** ** Palindromy *)

(** Palindrom to słowo, które czyta się tak samo od przodu jak i od tyłu.

    Zdefiniuj induktywny predykat [Palindrome], które odpowiada powyższemu
    pojęciu palindromu, ale dla list elementów dowolnego typu, a nie tylko
    słów. *)

(* begin hide *)
Inductive Palindrome {A : Type} : list A -> Prop :=
    | Palindrome_nil : Palindrome []
    | Palindrome_singl :
        forall x : A, Palindrome [x]
    | Palindrome_1 :
        forall (x : A) (l : list A),
          Palindrome l -> Palindrome (x :: l ++ [x]).
(* end hide *)

(* begin hide *)

Lemma Palindrome_inv :
  forall (A : Type) (x : A) (l : list A),
    Palindrome (x :: l ++ [x]) -> Palindrome l.
(* begin hide *)
Proof.
  intros. inv H.
    apply (f_equal length) in H2. rewrite length_app in H2.
      cbn in H2. rewrite <- plus_n_Sm in H2. inv H2.
    apply app_inv_r in H2. subst. assumption.
Qed.
(* end hide *)

Lemma Palindrome_inv_2 :
  forall (A : Type) (x y : A),
    Palindrome [x; y] -> x = y.
(* begin hide *)
Proof.
  intros. inv H. apply (f_equal last) in H2.
  rewrite last_app in H2. inv H2. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_inv_3 :
  forall (A : Type) (x y : A) (l : list A),
    Palindrome (x :: l ++ [y]) -> x = y.
(* begin hide *)
Proof.
  intros. inv H.
    apply (f_equal isEmpty) in H2. rewrite isEmpty_app in H2.
      destruct l; inv H2.
    apply (f_equal last) in H2. rewrite ?last_app in H2. inv H2.
      reflexivity.
Qed.
(* end hide *)

Lemma nat_ind_2 :
  forall P : nat -> Prop,
    P 0 -> P 1 -> (forall n : nat, P n -> P (S (S n))) ->
      forall n : nat, P n.
(* begin hide *)
Proof.
  fix IH 5. destruct n as [| [| n']].
    1-2: assumption.
    apply H1, IH; assumption.
Qed.
(* end hide *)

Lemma Palindrome_length :
  forall (A : Type) (x : A) (n : nat),
    exists l : list A, Palindrome l /\ n <= length l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    exists []. split; constructor.
    destruct IHn' as (l & IH1 & IH2).
      exists (x :: l ++ [x]). split.
        constructor. assumption.
        cbn. rewrite length_app. cbn. omega.
Restart.
  induction n as [| | n'] using nat_ind_2.
    exists []. split; constructor.
    exists [x]. split; constructor.
    destruct IHn' as (l & IH1 & IH2). exists (x :: l ++ [x]). split.
      constructor. assumption.
      cbn. rewrite length_app. cbn. omega.
Qed.
(* end hide *)

Lemma Palindrome_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (x :: snoc x l).
(* begin hide *)
Proof.
  intros. rewrite snoc_app_singl. constructor. assumption.
Qed.
(* end hide *)

Lemma Palindrome_app :
  forall (A : Type) (l1 l2 : list A),
    Palindrome l1 -> Palindrome l2 -> Palindrome (l1 ++ l2 ++ rev l1).
(* begin hide *)
Proof.
  intros A l1 l2 H. revert l2.
  induction H; cbn; intros.
    rewrite app_nil_r. assumption.
    constructor. assumption.
    replace _ with
        (Palindrome (x :: (l ++ ([x] ++ l2 ++ [x]) ++ rev l) ++ [x])).
      constructor. apply IHPalindrome. cbn. constructor. assumption.
      rewrite rev_app, !app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_app' :
  forall (A : Type) (l1 l2 : list A),
    Palindrome l2 -> Palindrome (l1 ++ l2 ++ rev l1).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite app_nil_r. assumption.
    replace _ with (Palindrome (h1 :: (t1 ++ l2 ++ rev t1) ++ [h1])).
      constructor. apply IHt1. assumption.
      rewrite ?app_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_rev :
  forall (A : Type) (l : list A),
    Palindrome l <-> Palindrome (rev l).
(* begin hide *)
Proof.
  assert (forall (A : Type) (l : list A),
            Palindrome l -> Palindrome (rev l)).
    induction 1; cbn.
      1-2: constructor.
      rewrite rev_app. cbn. constructor. assumption.
    split; intro.
      apply H. assumption.
      rewrite <- rev_inv. apply H. assumption.
Qed.
(* end hide *)

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Lemma lengthOrder_wf :
  forall A : Type, well_founded (@lengthOrder A).
(* begin hide *)
Proof.
  unfold well_founded. induction a as [| h t]; cbn.
    constructor. intros. inv H.
    inv IHt. constructor. intros. constructor. intros. apply H.
      cbn in *. unfold lengthOrder in *. cbn in *. omega.
Qed.
(* end hide *)

(* TODO: spec bez używania indukcji dobrze ufundowanej *)

Lemma Palindrome_spec :
  forall (A : Type) (l : list A),
    Palindrome l <-> l = rev l.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      1-2: reflexivity.
      rewrite rev_app, <- IHPalindrome; cbn. reflexivity.
    revert l.
    eapply
    (@well_founded_ind _
      _ (@lengthOrder_wf A)
      (fun l : list A => l = rev l -> Palindrome l) _) .
Unshelve.
  unfold lengthOrder.
  destruct x as [| h t]; cbn; intros.
    constructor.
    destruct (rev t) eqn: Heq.
      inv H0. constructor.
      rewrite H0. inv H0. constructor. apply H.
        rewrite length_app. apply le_n_S. cbn.
          rewrite <- plus_n_Sm, <- plus_n_O. apply le_S, le_n.
        rewrite rev_app in Heq. cbn in Heq. inv Heq.
          rewrite H1. symmetry. assumption.
Qed.
(* end hide *)

Lemma Palindrome_spec' :
  forall (A : Type) (l : list A),
    Palindrome l -> exists l1 l2 : list A,
      l = l1 ++ l2 ++ rev l1 /\ length l2 <= 1.
(* begin hide *)
Proof.
  induction 1; cbn.
    exists [], []. cbn. split; [reflexivity | apply le_0_n].
    exists [], [x]. cbn. split; [reflexivity | apply le_n].
    destruct IHPalindrome as (l1 & l2 & IH1 & IH2). subst.
      exists (x :: l1), l2. cbn. split.
        rewrite ?app_assoc. reflexivity.
        assumption.
Qed.
(* end hide *)

Lemma Palindrome_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    Palindrome l -> Palindrome (map f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    1-2: constructor.
    rewrite map_app. cbn. constructor. assumption.
Qed.
(* end hide *)

Lemma replicate_S :
  forall (A : Type) (n : nat) (x : A),
    replicate (S n) x = x :: replicate n x.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma Palindrome_replicate :
  forall (A : Type) (n : nat) (x : A),
    Palindrome (replicate n x).
(* begin hide *)
Proof.
  induction n as [| | n'] using nat_ind_2; intros.
    constructor.
    constructor.
    rewrite replicate_S, <- rev_replicate. cbn. constructor.
      rewrite rev_replicate. apply IHn'.
Qed.
(* end hide *)

Lemma Palindrome_cons_replicate :
  forall (A : Type) (n : nat) (x y : A),
    Palindrome (x :: replicate n y) -> n = 0 \/ x = y.
(* begin hide *)
Proof.
  destruct n as [| n']; intros.
    left. reflexivity.
    right. rewrite <- snoc_replicate, snoc_app_singl in H.
      apply Palindrome_inv_3 in H. assumption.
Qed.
(* end hide *)

Lemma Palindrome_iterate :
  forall (A : Type) (f : A -> A),
    (forall (n : nat) (x : A), Palindrome (iterate f n x)) ->
      forall x : A, f x = x.
(* begin hide *)
Proof.
  intros. specialize (H 2 x). cbn in H. inv H. destruct l; inv H2.
    rewrite <- ?H0. reflexivity.
    apply (f_equal isEmpty) in H3. rewrite isEmpty_app in H3.
      destruct l; inv H3.
Qed.
(* end hide *)

Lemma nth_rev :
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> nth n (rev l) = nth (length l - S n) l.
(* begin hide *)
Proof.
Admitted.
(* begin hide *)

Lemma Palindrome_nth :
  forall (A : Type) (l : list A),
    Palindrome l -> forall n : nat,
      n < length l -> nth n l = nth (length l - S n) l.
(* begin hide *)
Proof.
  intros. apply Palindrome_spec in H.
  rewrite H at 1. apply nth_rev. assumption.
Qed.
(* end hide *)

Lemma Palindrome_drop :
  forall (A : Type) (l : list A),
    (forall n : nat, Palindrome (drop n l)) ->
      l = [] \/ exists (n : nat) (x : A), l = replicate n x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. reflexivity.
    right. destruct IHt.
      intro. specialize (H (S n)). cbn in H. assumption.
      subst. exists 1, h. cbn. reflexivity.
      destruct H0 as (n & x & IH). subst. exists (S n), h. cbn.
        specialize (H 0). cbn in H. apply Palindrome_cons_replicate in H.
          destruct H; subst; cbn; reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_take :
  forall (A : Type) (l : list A),
    (forall n : nat, Palindrome (take n l)) ->
      l = [] \/ exists (n : nat) (x : A), l = replicate n x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. reflexivity.
    right.
Admitted.
(* end hide *)

Lemma Palindrome_zip :
  exists (A B : Type) (la : list A) (lb : list B),
    Palindrome la /\ Palindrome lb /\ ~ Palindrome (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool, [true; true], [false; true; false].
  cbn. repeat split.
    apply (Palindrome_1 true []). constructor.
    apply (Palindrome_1 false [true]). constructor.
    intro. apply Palindrome_inv_2 in H. inv H.
Qed.
(* end hide *)

(* TODO: unzip, zipWith, unzipWith *)

Lemma Palindrome_find_findLast :
  forall (A : Type) (p : A -> bool) (l : list A),
    Palindrome l -> find p l = findLast p l.
(* begin hide *)
Proof.
  intros. rewrite find_findLast. apply Palindrome_spec in H.
  rewrite <- H. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    Palindrome l -> Palindrome (pmap f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); constructor.
    destruct (f x) eqn: Heq; cbn.
      rewrite pmap_app. cbn. rewrite Heq. constructor. assumption.
      rewrite pmap_app. cbn. rewrite Heq, app_nil_r. assumption.
Qed.
(* end hide *)

Lemma Palindrome_intersperse :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (intersperse x l).
(* begin hide *)
Proof.
  intros. rewrite Palindrome_spec in *.
  rewrite <- intersperse_rev, <- H. reflexivity.
Qed.
(* end hide *)

(* TODO: groupBy *)

Lemma Palindrome_Dup :
  forall (A : Type) (l : list A),
    Palindrome l -> length l <= 1 \/ Dup l.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    left. apply le_0_n.
    left. apply le_n.
    right. constructor. rewrite elem_app. right. left.
Qed.
(* end hide *)

(* TODO: Incl, Sublist, subseq *)

(*
Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)
*)

Lemma Sublist_Palindrome :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Palindrome l1 -> Palindrome l2 -> l1 = [].
(* begin hide *)
Proof.
  induction 1; intros.
Abort.
(* end hide *)

Lemma Prefix_Palindrome :
  forall (A : Type) (l : list A),
    Prefix (rev l) l <-> Palindrome l.
(* begin hide *)
Proof.
  split; intro.
    apply Prefix_rev_l in H. rewrite Palindrome_spec. assumption.
    apply Palindrome_spec in H. rewrite <- H. apply Prefix_refl.
Qed.
(* end hide *)

(* TODO
Lemma Subseq_rev_l :
  forall (A : Type) (l : list A),
    Subseq (rev l) l <-> Palindrome l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      constructor.
    Focus 2. induction 1; cbn.
      1-2: apply Subseq_refl.
      rewrite rev_app. cbn. constructor. apply Subseq_app_r'. assumption.
Abort.
(* end hide *)

Lemma Subseq_rev_r :
  forall (A : Type) (l : list A),
    Subseq l (rev l) <-> Palindrome l.
(* begin hide *)
Proof.
  split.
    Focus 2. induction 1; cbn.
      1-2: apply Subseq_refl.
      rewrite rev_app. cbn. constructor. apply Subseq_app_r'. assumption.
Abort.
(* end hide *)
*)