Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

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
(*  induction 2.
    inv H. reflexivity.
    f_equal. apply IHSubseq. apply Subseq_cons_inv in H. assumption.
    apply Subseq_cons_l_app in H. destruct H as (l21 & l22 & H1 & H2).
      subst.
*)
(*  induction 1; intros.
    inv H. reflexivity.
    apply Subseq_cons_inv in H0. rewrite (IHSubseq H0). reflexivity.
    inv H0.
    apply Subseq_cons_l_app in H0. destruct H0 as (l21 & l22 & H1 & H2).
      subst.
inv H0.
      inv H.
        apply IHSubseq.
      f_equal. apply IH
Qed.*)
Abort.
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
  forall (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Subseq la1 la2 -> Subseq lb1 lb2 ->
      Subseq (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  intros until 1. revert lb1 lb2.
  induction H; cbn; intros.
    constructor.
    induction H0; constructor.
      apply IHSubseq. assumption.
      destruct l0.
Abort.
(* end hide *)

Inductive bool_le : bool -> bool -> Prop :=
    | ble_refl : forall b : bool, bool_le b b
    | ble_false_true : bool_le false true.

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

(* TODO:
bind
head, tail i uncons
last, init i unsnoc
zip
unzip
zipWith
unzipWith
find i findLast
removeFirst i removeLast
findIndices
*)

(*Lemma Subseq_ 
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> .
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)
*)