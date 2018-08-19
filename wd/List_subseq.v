Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Inductive subseq {A : Type} : list A -> list A -> Prop :=
    | subseq_nil :
        forall l : list A, subseq [] l
    | subseq_cons :
        forall (x : A) (l1 l2 : list A),
          subseq l1 l2 -> subseq (x :: l1) (x :: l2)
    | subseq_skip :
        forall (x : A) (l1 l2 : list A),
          subseq l1 l2 -> subseq l1 (x :: l2).

Lemma subseq_refl :
  forall (A : Type) (l : list A), subseq l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_trans : 
  forall (A : Type) (l1 l2 l3 : list A),
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
(* begin hide *)
Proof.
  intros A l1 l2 l3 H12 H23. revert l1 H12.
  induction H23; cbn; intros.
    inv H12. constructor.
    inv H12; constructor; apply IHsubseq; assumption.
    inv H12; constructor; apply IHsubseq; constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_cons_inv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    subseq (x :: l1) (x :: l2) -> subseq l1 l2.
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
        constructor. apply IHt1. apply subseq_skip. assumption.
Qed.
(* end hide *)

Lemma subseq_cons_l_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    subseq (x :: l1) l2 ->
      exists l21 l22 : list A, l2 = l21 ++ x :: l22 /\ subseq l1 l22.
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

Lemma subseq_wasym :
  forall (A : Type) (l1 l2 : list A),
    subseq l1 l2 -> subseq l2 l1 -> l1 = l2.
(* begin hide *)
Proof.
(*  induction 2.
    inv H. reflexivity.
    f_equal. apply IHsubseq. apply subseq_cons_inv in H. assumption.
    apply subseq_cons_l_app in H. destruct H as (l21 & l22 & H1 & H2).
      subst.
*)
(*  induction 1; intros.
    inv H. reflexivity.
    apply subseq_cons_inv in H0. rewrite (IHsubseq H0). reflexivity.
    inv H0.
    apply subseq_cons_l_app in H0. destruct H0 as (l21 & l22 & H1 & H2).
      subst.
inv H0.
      inv H.
        apply IHsubseq.
      f_equal. apply IH
Qed.*)
Abort.
(* end hide *)

Lemma subseq_isEmpty_l :
  forall (A : Type) (l1 l2 : list A),
    isEmpty l1 = true -> subseq l1 l2.
(* begin hide *)
Proof.
  destruct l1; cbn; intros.
    constructor.
    congruence.
Qed.
(* end hide *)

Lemma subseq_nil_r :
  forall (A : Type) (l : list A),
    subseq l [] -> l = [].
(* begin hide *)
Proof.
  inversion 1. reflexivity.
Qed.
(* end hide *)

Lemma subseq_length :
  forall (A : Type) (l1 l2 : list A),
    subseq l1 l2 -> length l1 <= length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    apply le_n_S. assumption.
    apply le_S. assumption.
Qed.
(* end hide *)

Lemma subseq_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    subseq l1 l2 -> subseq l1 (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_snoc' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    subseq l1 l2 -> subseq (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn; repeat constructor. assumption.
    constructor. assumption.
    constructor. assumption.
Qed.
(* end hide *)

Lemma subseq_app_l :
  forall (A : Type) (l1 l2 l3 : list A),
    subseq l1 l2 -> subseq l1 (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma subseq_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_app_l' :
  forall (A : Type) (l1 l2 l3 : list A),
    subseq l1 l2 -> subseq (l3 ++ l1) (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma subseq_app_r' :
  forall (A : Type) (l1 l2 l3 : list A),
    subseq l1 l2 -> subseq (l1 ++ l3) (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply subseq_app_l, subseq_refl.
    1-2: constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_app_not_comm :
  exists (A : Type) (l1 l2 l3 : list A),
    subseq l1 (l2 ++ l3) /\ ~ subseq l1 (l3 ++ l2).
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
Lemma subseq_rev_l :
  forall (A : Type) (l : list A),
    subseq (rev l) l <-> Palindrome l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      constructor.
    Focus 2. induction 1; cbn.
      1-2: apply subseq_refl.
      rewrite rev_app. cbn. constructor. apply subseq_app_r'. assumption.
Abort.
(* end hide *)

Lemma subseq_rev_r :
  forall (A : Type) (l : list A),
    subseq l (rev l) <-> Palindrome l.
(* begin hide *)
Proof.
  split.
    Focus 2. induction 1; cbn.
      1-2: apply subseq_refl.
      rewrite rev_app. cbn. constructor. apply subseq_app_r'. assumption.
Abort.
(* end hide *)
*)

Lemma subseq_map : 
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    subseq l1 l2 -> subseq (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_join :
  forall (A : Type) (l1 l2 : list (list A)),
    subseq l1 l2 -> subseq (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    apply subseq_app_l'. assumption.
    apply subseq_app_l. assumption.
Qed.
(* end hide *)

Lemma subseq_replicate :
  forall (A : Type) (n m : nat) (x : A),
    subseq (replicate n x) (replicate m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert m. induction n as [| n']; cbn; intros.
      apply le_0_n.
      destruct m as [| m']; cbn in H.
        inv H.
        apply le_n_S, IHn'. apply subseq_cons_inv with x. assumption.
    induction 1.
      apply subseq_refl.
      cbn. constructor. assumption.
Qed.
(* end hide *)

Lemma subseq_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    subseq (iterate f n x) (iterate f m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert f m x. induction n as [| n']; cbn; intros.
      apply le_0_n.
      destruct m as [| m']; cbn in H.
        inv H.
        apply le_n_S, (IHn' f _ (f x)).
          apply subseq_cons_inv with x. assumption.
    revert f m x. induction n as [| n']; cbn; intros.
      constructor.
      destruct m as [| m']; cbn.
        inv H.
        constructor. apply IHn', le_S_n. assumption.
Qed.
(* end hide *)

Lemma subseq_nth :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    subseq l1 l2 -> nth n l1 = Some x ->
      exists m : nat, nth m l2 = Some x /\ n <= m.
(* begin hide *)
Proof.
  intros A l1 l2 n x H. revert n x.
  induction H; cbn; intros.
    rewrite nth_nil in H. congruence.
    destruct n as [| n']; cbn in H0.
      inv H0. exists 0. cbn. split; [reflexivity | apply le_0_n].
      destruct (IHsubseq _ _ H0) as (m & IH1 & IH2).
        exists (S m). cbn. split.
          assumption.
          apply le_n_S. assumption.
    destruct (IHsubseq _ _ H0) as (m & IH1 & IH2).
      exists (S m). cbn. split.
        assumption.
        apply le_S. assumption.
Qed.
(* end hide *)

Lemma subseq_insert :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    subseq l1 l2 -> subseq l1 (insert l2 n x).
(* begin hide *)
Proof.
  intros A l1 l2 n x H. revert n x.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n'].
      do 2 constructor. assumption.
      constructor. apply IHsubseq.
    destruct n as [| n']; repeat constructor; trivial.
Qed.
(* end hide *)

Lemma subseq_remove' :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    subseq l1 l2 -> subseq (remove' n l1) l2.
(* begin hide *)
Proof.
  intros A l1 l2 n H. revert n.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n']; cbn.
      constructor. assumption.
      rewrite remove'_S_cons. constructor. apply IHsubseq.
    constructor. apply IHsubseq.
Qed.
(* end hide *)

Lemma subseq_take :
  forall (A : Type) (n : nat) (l : list A),
    subseq (take n l) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    constructor.
    destruct l as [| h t]; cbn; constructor. apply IHn'.
Qed.
(* end hide *)

Lemma subseq_drop :
  forall (A : Type) (n : nat) (l : list A),
    subseq (drop n l) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    apply subseq_refl.
    destruct l; constructor. apply IHn'.
Qed.
(* end hide *)

Lemma subseq_zip :
  forall (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    subseq la1 la2 -> subseq lb1 lb2 ->
      subseq (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  intros until 1. revert lb1 lb2.
  induction H; cbn; intros.
    constructor.
    induction H0; constructor.
      apply IHsubseq. assumption.
      destruct l0.
Abort.
(* end hide *)

Inductive bool_le : bool -> bool -> Prop :=
    | ble_refl : forall b : bool, bool_le b b
    | ble_false_true : bool_le false true.

Lemma subseq_all :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    subseq l1 l2 -> bool_le (all p l2) (all p l1).
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

Lemma subseq_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    subseq l1 l2 -> bool_le (any p l1) (any p l2).
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

Lemma subseq_all' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    subseq l1 l2 -> all p l2 = true -> all p l1 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x); cbn in *.
      apply IHsubseq. assumption.
      congruence.
    destruct (p x); cbn in *.
      apply IHsubseq. assumption.
      congruence.
Qed.
(* end hide *)

Lemma subseq_any' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    subseq l1 l2 -> any p l2 = false -> any p l1 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x); cbn in *.
      congruence.
      apply IHsubseq. assumption.
    destruct (p x); cbn in *.
      congruence.
      apply IHsubseq. assumption.
Qed.
(* end hide *)

Lemma subseq_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    subseq l1 l2 -> count p l1 <= count p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    destruct (p x); try apply le_n_S; assumption.
    destruct (p x); try apply le_S; assumption.
Qed.
(* end hide *)

Lemma subseq_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    subseq l1 l2 -> subseq (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_filter' :
  forall (A : Type) (p : A -> bool) (l : list A),
    subseq (filter p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    subseq (takeWhile p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor. assumption.
Qed.
(* end hide *)

Lemma subseq_takeWhile' :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    subseq l1 l2 /\ ~ subseq (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists bool, id, [true], [false; true]. cbn. split.
    repeat constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma subseq_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    subseq (dropWhile p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor.
      assumption.
      apply subseq_refl.
Qed.
(* end hide *)

Lemma subseq_dropWhile' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    subseq l1 l2 -> subseq (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
    destruct (p x); try constructor.
      assumption.
      apply subseq_trans with (dropWhile p l2).
        assumption.
        apply subseq_dropWhile.
Qed.
(* end hide *)

Lemma subseq_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    subseq l1 l2 -> subseq (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); try constructor; assumption.
    destruct (f x); try constructor; assumption.
Qed.
(* end hide *)

Lemma subseq_map_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    subseq l1 l2 -> subseq (map Some (pmap f l1)) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); cbn; constructor; assumption.
    constructor. assumption.
Qed.
(* end hide *)

Lemma subseq_findIndex :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A) (n m : nat),
    subseq l1 l2 /\ findIndex p l1 = Some n /\
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

(*Lemma subseq_ 
  forall (A : Type) (l1 l2 : list A),
    subseq l1 l2 -> .
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)
*)