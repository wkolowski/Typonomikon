Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

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

Require Import Palindrome.

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

Require Import List_subseq.

Lemma sublist_Prefix :
  exists (A : Type) (l1 l2 : list A),
    sublist l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true], [false; true]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma incl_Prefix :
  exists (A : Type) (l1 l2 : list A),
    incl l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true; true], [true]. split.
    unfold incl. intros. inv H.
      constructor.
      assumption.
    intro. inv H. inv H1.
Qed.
(* end hide *)

Lemma Prefix_subseq :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> subseq l1 l2.
(* begin hide *)
Proof.
  induction 1; constructor. assumption.
Qed.
(* end hide *)

Lemma subseq_Prefix :
  exists (A : Type) (l1 l2 : list A),
    subseq l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true], [false; true]. split.
    do 3 constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Prefix_incl :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> incl l1 l2.
(* begin hide *)
Proof.
  intros. unfold incl. apply Prefix_elem. assumption.
Qed.
(* end hide *)

(* TODO: Exactly - raczej nic z tego *)

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

Lemma Suffix_sublist :
  forall (A : Type) (l1 l2 : list A),
    Suffix l1 l2 <-> sublist l1 l2 \/ l1 = l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      right. reflexivity.
      left. destruct IHSuffix; subst.
        apply sublist_trans with l2.
          assumption.
          constructor.
        constructor.
    destruct 1; subst.
      induction H.
        constructor. apply Suffix_refl.
        apply Suffix_trans with l2; assumption.
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