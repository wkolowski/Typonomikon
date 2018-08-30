Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(*Require Import CoqBookPL.wd.Option.*)

Lemma replace_any :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      any p l = true -> p x = true -> any p l' = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H; cbn in *. rewrite H1. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. cbn. destruct (p h); cbn in *.
          reflexivity.
          apply (IHt _ _ _ Heq H0 H1).
        inv H.
Qed.
(* end hide *)

Require Import Bool.

Lemma replace_any' :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      any p l' = any p (take n l) || p x || any p (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H; cbn in *. rewrite drop_0. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H; cbn.
        rewrite (IHt _ _ _ Heq). rewrite ?Bool.orb_assoc. reflexivity.
Qed.
(* end hide *)

Lemma replace_all :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      all p l = true -> p x = true -> all p l' = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H; cbn in *. rewrite H1. cbn. destruct (p h); cbn in H0.
        assumption.
        congruence.
      destruct (replace t n' x) eqn: Heq; inv H; cbn.
        destruct (p h); cbn in *.
          apply (IHt _ _ _ Heq H0 H1).
          assumption.
Qed.
(* end hide *)

Lemma replace_all' :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      all p l' = all p (take n l) && p x && all p (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H; cbn in *. rewrite drop_0. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H; cbn.
        rewrite (IHt _ _ _ Heq), ?Bool.andb_assoc. reflexivity.
Qed.
(* end hide *)

(*
Lemma replace_findIndex :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      findIndex p l' 
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)
*)

Lemma replace_count :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      count p l' = count p (take n l) + count p [x] + count p (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. destruct (p x); rewrite drop_0; reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. cbn. rewrite (IHt _ _ _ Heq). cbn.
          destruct (p h), (p x); cbn; reflexivity.
        inv H. 
Qed.
(* end hide *)

Lemma replace_filter :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      filter p l' =
      filter p (take n l) ++ filter p [x] ++ filter p (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. destruct (p x); cbn; rewrite drop_0; reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. cbn. rewrite (IHt _ _ _ Heq). cbn.
          destruct (p h), (p x); cbn; reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma replace_findIndices :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
    findIndices p l' =
    findIndices p (take n l) ++
    map (plus n) (findIndices p [x]) ++
    map (plus (S n)) (findIndices p (drop (S n) l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. destruct (p x); cbn; rewrite drop_0; reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. cbn. rewrite (IHt _ _ _ Heq). cbn.
          destruct (p h), (p x); cbn; rewrite ?map_app, ?plus_0_r.
            do 2 f_equal. cbn. rewrite map_map. reflexivity.
            do 2 f_equal. rewrite map_map. reflexivity.
            do 2 f_equal. cbn. rewrite map_map. reflexivity.
            f_equal. rewrite map_map. reflexivity.
          inv H.
Qed.
(* end hide *)

(*
Lemma replace_takeWhile :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace_dropWhile :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)
*)

Lemma elem_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> elem x l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. left.
      destruct (replace t n' x) eqn: Heq; inv H.
        right. apply (IHt _ _ _ Heq).
Qed.
(* end hide *)

Lemma elem_replace' :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    replace l n x = Some l' ->
      elem y l -> elem y l' \/ nth n l = Some y.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      inv H. inv H0.
        right. reflexivity.
        left. right. assumption.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0.
        do 2 left.
        destruct (IHt _ _ _ _ Heq H2).
          left. right. assumption.
          right. assumption.
Qed.
(* end hide *)

Lemma elem_replace'_conv :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    replace l n x = Some l' ->
      elem y l' -> elem y l \/ x = y.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      inv H. inv H0.
        right. reflexivity.
        left. right. assumption.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0.
        do 2 left.
        destruct (IHt _ _ _ _ Heq H2).
          left. right. assumption.
          right. assumption.
Qed.
(* end hide *)

(* TODO: to samo dla In *)

Definition Classically (A : Type) : Type :=
  (forall P : Prop, P \/ ~ P) -> A.

Notation "f $ x" := (f x) (at level 100, only parsing).

Ltac cls := progress unfold Classically; intro LEM.


Lemma Dup_replace :
  Classically $
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Dup l -> Dup l' \/ ~ elem x l.
(* begin hide *)
Proof.
  cls. induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. inv H0.
        destruct (LEM (x = h)).
          subst. left. constructor. assumption.
          destruct (LEM (elem x t)).
            left. constructor. assumption.
            right. intro. inv H2; contradiction.
        left. right. assumption.
      destruct (replace t n' x) eqn: Heq.
        inv H. inv H0.
          destruct (LEM (elem h l)).
            left. constructor. assumption.
Abort.
(* end hide *)

(*
Lemma Dup_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Dup l' <-> Dup l \/ elem x (take n l) \/ elem x (drop (S n) l).
(* begin hide *)
Proof.
  split; revert l' n x H.
    intros. rewrite replace_spec in H. destruct (S n <=? length l).
      inv H. rewrite Dup_app, Dup_cons in H0. firstorder.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n']; cbn.
        inv H. inv H0.
          do 2 right. rewrite drop_0. assumption.
          left. right. assumption.
        destruct (replace t n' x) eqn: Heq; inv H. inv H0.
          destruct (elem_replace'_conv A _ _ _ _ _ Heq H1).
            left. constructor. assumption.
            right. left. subst. left.
          destruct (IHt _ _ _ Heq H1) as [IH | [IH | IH]].
            left. right. assumption.
            right. left. right. assumption.
            do 2 right. assumption.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n']; cbn in *.
        inv H. decompose [or] H0; clear H0.
          inv H.
          pose (elem_replace A t l n' x Heq).
            rewrite <- (app_take_drop A n' t), elem_app in e.
              destruct H.
                right. left.
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)
*)

Lemma Exists_replace :
  Classically $
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Exists P l -> Exists P l' \/ ~ P x.
(* begin hide *)
Proof.
  cls. induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct (LEM (P x)).
        do 2 left. assumption.
        right. assumption.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0.
        do 2 left. assumption.
        destruct (IHt _ _ _ Heq H1).
          left. right. assumption.
          right. assumption.
Qed.
(* end hide *)

Lemma Exists_replace' :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> Exists P l ->
      Exists P l' \/ exists y : A, nth n l = Some y /\ P y.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. inv H0.
        right. exists h. cbn. split; [reflexivity | assumption].
        left. right. assumption.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0.
        do 2 left. assumption.
        destruct (IHt _ _ _ Heq H1).
          left. right. assumption.
          right. cbn. assumption.
Qed.
(* end hide *)

Lemma Exists_replace'' :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Exists P l -> Exists P l' \/ ~ P x.
(* begin hide *)
Proof.
  intros. pose (Exists_replace' _ _ _ _ _ _ H H0). destruct o.
    left. assumption.
    rewrite replace_spec in H. destruct H1 as [y H1].
      destruct (S n <=? length l).
        inv H.
    left.
Abort.
(* end hide *)

Lemma Exists_replace_conv :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> Exists P l' ->
      Exists P l \/ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. inv H0.
        right. assumption.
        left. right. assumption.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0.
        do 2 left. assumption.
        destruct (IHt _ _ _ Heq H1).
          left. right. assumption.
          right. assumption.
Qed.
(* end hide *)

Lemma Forall_replace :
  Classically $
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> Forall P l ->
      Forall P l' \/ ~ P x.
(* begin hide *)
Proof.
  cls. induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct (LEM (P x)).
        inv H0. left. constructor; assumption.
        right. assumption.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0.
        destruct (IHt _ _ _ Heq H3).
          left. constructor; assumption.
          right. assumption.
Qed.
(* end hide *)

Lemma Forall_replace_conv :
  Classically $
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> Forall P l' ->
      (Forall P l /\ P x) \/
      exists y : A, nth n l = Some y /\ ~ P y.
(* begin hide *)
Proof.
  cls. induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      inv H. inv H0. destruct (LEM (P h)).
        left. repeat constructor; assumption.
        right. exists h. split; trivial.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0.
        destruct (IHt _ _ _ Heq H3) as [[IH1 IH2] | IH].
          left. repeat constructor; assumption.
          right. assumption.
Qed.
(* end hide *)

Lemma AtLeast_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' -> AtLeast P m l -> AtLeast P (m - 1) l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. inv H0; cbn.
        constructor.
        rewrite <- minus_n_O. constructor. assumption.
        apply AtLeast_le with m.
          constructor. assumption.
          omega.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0; cbn.
        constructor.
        rewrite <- minus_n_O. specialize (IHt _ _ _ _ Heq H4).
          destruct n; cbn in *.
            constructor.
            rewrite <- minus_n_O in IHt. constructor; assumption.
        specialize (IHt _ _ _ _ Heq H2). constructor. assumption.
Qed.
(* end hide *)

Lemma AtLeast_replace' :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' -> AtLeast P m l' -> AtLeast P (m - 1) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. inv H0; cbn.
        constructor.
        rewrite <- minus_n_O. constructor. assumption.
        apply AtLeast_le with m.
          constructor. assumption.
          omega.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0; cbn.
        constructor.
        rewrite <- minus_n_O. specialize (IHt _ _ _ _ Heq H4).
          destruct n; cbn in *.
            constructor.
            rewrite <- minus_n_O in IHt. constructor; assumption.
        specialize (IHt _ _ _ _ Heq H2). constructor. assumption.
Qed.
(* end hide *)

(* TODO: [Exactly], [AtMost] *)

(* TODO: sublist, incl (chyba nic ciekawego nie ma) *)

Require Import Rels.

Lemma replace_Palindrome :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> Palindrome l ->
      Palindrome l' <-> length l = 1 /\ n = 0 \/ nth n l = Some x.
(* begin hide *)
Proof.
  split.
    Focus 2. destruct 1 as [[H1 H2] | H1].
      subst. destruct l as [| h [| h' t]]; inv H; inv H1. constructor.
      assert (l = l').
        rewrite replace_nth_eq; eassumption.
        subst. assumption.
    intros. apply Palindrome_spec in H0. apply Palindrome_spec in H1.
      rewrite H0, H1 in H. rewrite replace_rev in H.
        unfold omap in H.
Abort.
(* end hide *)