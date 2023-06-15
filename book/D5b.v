(** * D5b: Listy: predykaty *)

From Typonomikon Require Export D5a.

(** * Proste predykaty *)

(** ** [elem] *)

(** Zdefiniuj induktywny predykat [elem]. [elem x l] jest spełniony, gdy
    [x] jest elementem listy [l]. *)

(* begin hide *)
Inductive elem {A : Type} : A -> list A -> Prop :=
| elem_head :
    forall (x : A) (l : list A),
      elem x (x :: l)
| elem_cons :
    forall (x h : A) (t : list A),
      elem x t -> elem x (h :: t).
(* end hide *)

Lemma elem_not_nil :
  forall (A : Type) (x : A), ~ elem x [].
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma elem_not_cons :
  forall (A : Type) (x h : A) (t : list A),
    ~ elem x (h :: t) -> x <> h /\ ~ elem x t.
(* begin hide *)
Proof.
  split; intro; apply H; subst; constructor; auto.
Qed.
(* end hide *)

Lemma elem_cons' :
  forall (A : Type) (x h : A) (t : list A),
    elem x (h :: t) <-> x = h \/ elem x t.
(* begin hide *)
Proof.
  split; (inversion 1; subst; [left | right]; trivial).
Qed.
(* end hide *)

Lemma elem_snoc :
  forall (A : Type) (x y : A) (l : list A),
    elem x (snoc y l) <-> elem x l \/ x = y.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros; inversion H; subst; clear H.
      right. reflexivity.
      inversion H2.
      do 2 left.
      destruct (IHt H2).
        left. right. assumption.
        right. assumption.
    destruct 1; subst.
      induction H; cbn.
        left.
        right. assumption.
      induction l as [| h t]; cbn.
        left.
        right. assumption.
Qed.
(* end hide *)

Lemma elem_app_l :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l1 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    constructor. assumption.
Qed.
(* end hide *)

Lemma elem_app_r :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma elem_or_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l1 \/ elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  destruct 1; [apply elem_app_l | apply elem_app_r]; assumption.
Qed.
(* end hide *)

Lemma elem_app_or :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x (l1 ++ l2) -> elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    right. assumption.
    inversion H; subst.
      left. constructor.
      destruct (IHt1 _ H2).
        left. constructor. assumption.
        right. assumption.
Qed.
(* end hide *)

Lemma elem_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x (l1 ++ l2) <-> elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  split; intros; [apply elem_app_or | apply elem_or_app]; assumption.
Qed.
(* end hide *)

Lemma elem_spec :
  forall (A : Type) (x : A) (l : list A),
    elem x l <-> exists l1 l2 : list A, l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      exists [], l. cbn. reflexivity.
      destruct IHelem as [l1 [l2 IH]].
        exists (h :: l1), l2. rewrite IH. cbn. reflexivity.
    destruct 1 as [l1 [l2 ->]]. apply elem_app_r. constructor.
Qed.
(* end hide *)

Lemma elem_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    elem x l -> elem (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; inversion 1; subst.
    constructor.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma elem_map_conv :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    elem y (map f l) <-> exists x : A, f x = y /\ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      inversion H; subst.
        exists h. split; trivial. constructor.
        destruct (IHt H2) as [x [Hx1 Hx2]]. exists x.
          split; trivial. constructor. assumption.
    destruct 1 as [x [<- H2]]. apply elem_map, H2.
Qed.
(* end hide *)

Lemma elem_map_conv' :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    (forall x y : A, f x = f y -> x = y) ->
      elem (f x) (map f l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; inversion 2; subst.
    specialize (H _ _ H3). subst. constructor.
    constructor. apply IHt; assumption.
Qed.
(* end hide *)

Lemma map_ext_elem :
  forall (A B : Type) (f g : A -> B) (l : list A),
    (forall x : A, elem x l -> f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite H, IHt.
      trivial.
      intros. apply H. constructor. assumption.
      constructor.
Qed.
(* end hide *)

Lemma elem_join :
  forall (A : Type) (x : A) (ll : list (list A)),
    elem x (join ll) <-> exists l : list A, elem x l /\ elem l ll.
(* begin hide *)
Proof.
  split.
    induction ll as [| h t]; cbn; intros.
      inversion H.
      rewrite elem_app in H. destruct H.
        exists h. split; try left; assumption.
        destruct (IHt H) as [l [H1 H2]].
          exists l. split; try right; assumption.
    destruct 1 as [l [H1 H2]]. induction H2; cbn.
      apply elem_app_l. assumption.
      apply elem_app_r, IHelem, H1.
Qed.
(* end hide *)

Lemma elem_replicate :
  forall (A : Type) (n : nat) (x y : A),
    elem y (replicate n x) <-> n <> 0 /\ x = y.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; inversion 1; subst.
      split; auto.
      destruct (IHn' H2). auto.
    intros [H H']. rewrite H'. destruct n as [| n'].
      contradiction H. trivial.
      cbn. left.
Qed.
(* end hide *)

Lemma nth_elem :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A, nth n l = Some x /\ elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      exists h. split; constructor.
      apply Nat.succ_lt_mono in H. destruct (IHt _ H) as (x & IH1 & IH2).
        exists x. split; try right; assumption.
Qed.
(* end hide *)

(* TOOD: ulepszyć? *) Lemma iff_elem_nth :
  forall (A : Type) (x : A) (l : list A),
    elem x l <-> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  split.
    induction 1.
      exists 0. cbn. reflexivity.
      destruct IHelem as (n & IH). exists (S n). cbn. assumption.
    destruct 1 as (n & H). revert n H.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. left.
        right. apply (IHt _ H).
Qed.
(* end hide *)

Lemma elem_rev_aux :
  forall (A : Type) (x : A) (l : list A),
    elem x l -> elem x (rev l).
(* begin hide *)
Proof.
  induction 1; cbn; rewrite elem_snoc.
    right. reflexivity.
    left. assumption.
Qed.
(* end hide *)

Lemma elem_rev :
  forall (A : Type) (x : A) (l : list A),
    elem x (rev l) <-> elem x l.
(* begin hide *)
Proof.
  split; intro.
    apply elem_rev_aux in H. rewrite rev_rev in H. assumption.
    apply elem_rev_aux, H.
Qed.
(* end hide *)

Lemma elem_remove_nth :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    elem x l -> nth n l <> Some x ->
    match remove n l with
    | None => True
    | Some (_, l') => elem x l'
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n']; cbn in *; inv H.
      contradiction.
      assumption.
      destruct (remove n' t).
        destruct p. left.
        trivial.
      specialize (IHt _ H3 H0). destruct (remove n' t).
        destruct p. right. assumption.
        trivial.
Qed.
(* end hide *)

Lemma elem_take :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    elem x (take n l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; inversion H; subst; clear H.
      left.
      right. apply (IHt _ _ H2).
Qed.
(* end hide *)

Lemma elem_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    elem x (drop n l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n'].
      assumption.
      right. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma elem_splitAt' :
  forall (A : Type) (l l1 l2 : list A) (n : nat) (x y : A),
    splitAt n l = Some (l1, y, l2) ->
      elem x l <-> x = y \/ elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  split.
    intro. revert l1 l2 n y H. induction H0; cbn; intros.
      destruct n as [| n'].
        inv H. left. reflexivity.
        destruct (splitAt n' l).
          destruct p, p. inv H. right. do 2 left.
          inv H.
      destruct n as [| n'].
        inv H. do 2 right. assumption.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. inv H. decompose [or] (IHelem _ _ _ _ Heq).
            left. assumption.
            right. left. right. assumption.
            do 2 right. assumption.
          inv H.
    revert l1 l2 n x y H. induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. decompose [or] H0; clear H0.
          subst. left.
          inv H1.
          right. assumption.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. inv H. specialize (IHt _ _ _ x _ Heq).
            decompose [or] H0; clear H0.
              right. apply IHt. left. assumption.
              inv H1.
                left.
                right. apply IHt. right. left. assumption.
              right. apply IHt. do 2 right. assumption.
              inv H.
Qed.
(* end hide *)

Lemma elem_insert :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    elem y (insert l n x) <-> x = y \/ elem y l.
(* begin hide *)
Proof.
  split.
    revert n x. induction l as [| h t]; cbn; intros.
      inv H.
        left. reflexivity.
        inv H2.
      destruct n as [| n'].
        rewrite ?elem_cons' in *.
          decompose [or] H; clear H; subst; firstorder.
        rewrite ?elem_cons' in *. firstorder.
    revert n. induction l as [| h t]; cbn; intros.
      destruct H; subst.
        constructor.
        inv H.
      destruct H, n as [| n']; subst.
        left.
        right. apply IHt. left. reflexivity.
        right. assumption.
        inv H.
          left.
          right. apply IHt. right. assumption.
Qed.
(* end hide *)

Lemma elem_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    replace l n x = Some l' ->
      elem y l' <-> elem y (take n l) \/ x = y \/ elem y (drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H. destruct (n <? length l).
    inv H. rewrite elem_app, elem_cons'. firstorder.
    inv H.
Qed.
(* end hide *)

Lemma elem_filter :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x (filter p l) <-> p x = true /\ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      case_eq (p h); intros; rewrite H0 in *.
        inversion H; subst; clear H.
          repeat constructor. assumption.
          destruct (IHt H3). firstorder constructor. assumption.
        destruct (IHt H). firstorder constructor. assumption.
    destruct 1. induction H0; cbn.
      rewrite H. constructor.
      destruct (p h).
        right. apply IHelem, H.
        apply IHelem, H.
Qed.
(* end hide *)

Lemma elem_filter_conv :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    elem x l <->
    elem x (filter p l) /\ p x = true \/
    elem x (filter (fun x : A => negb (p x)) l) /\ p x = false.
(* begin hide *)
Proof.
  split; rewrite ?elem_filter.
  destruct (p x). all: firstorder.
Qed.
(* end hide *)

Lemma elem_partition :
  forall (A : Type) (p : A -> bool) (x : A) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      elem x l <->
      (elem x l1 /\ p x = true) \/ (elem x l2 /\ p x = false).
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H. inversion H; subst; clear H.
  rewrite (elem_filter_conv _ p). reflexivity.
Qed.
(* end hide *)

Lemma elem_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x (takeWhile p l) -> elem x l /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intros; rewrite H0 in *.
      split.
        inversion H; subst; clear H.
          constructor.
          right. destruct (IHt _ H3). assumption.
        inversion H; subst; clear H.
          assumption.
          destruct (IHt _ H3). assumption.
      inversion H.
Qed.
(* end hide *)

Lemma elem_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x (dropWhile p l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intros; rewrite H0 in *.
      destruct (IHt _ H).
        right; left.
        right; right; assumption.
      assumption.
Qed.
(* end hide *)

Lemma elem_takeWhile_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x l <-> elem x (takeWhile p l) \/ elem x (dropWhile p l).
(* begin hide *)
Proof.
  split.
    intros. apply elem_app. rewrite takeWhile_dropWhile_spec. assumption.
    induction l as [| h t]; cbn.
      destruct 1; assumption.
      destruct (p h) eqn: Heq.
        destruct 1.
          inv H; [left | right]. apply IHt. left. assumption.
          right. apply IHt. right. assumption.
        destruct 1; inv H; [left | right]. assumption.
Qed.
(* end hide *)

Lemma elem_dropWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x l -> ~ elem x (dropWhile p l) -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intro.
      rewrite H1 in H0. inversion H; subst.
        assumption.
        apply IHt; assumption.
      rewrite H1 in H0. contradiction H.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: span vs intersperse, groupBy *)
(* end hide *)

Lemma span_spec' :
  forall (A : Type) (p : A -> bool) (l : list A),
    match span p l with
    | None => forall x : A, elem x l -> p x = false
    | Some (b, x, e) =>
        b = takeWhile (fun x : A => negb (p x)) l /\
        Some x = find p l /\
        x :: e = dropWhile (fun x : A => negb (p x)) l /\
        Some (x, b ++ e) = removeFirst p l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph; cbn.
      repeat split; reflexivity.
      destruct (span p t) eqn: Heq.
        destruct p0, p0. decompose [and] IHt; clear IHt.
          rewrite <- H3, ?H, H0. cbn. repeat split. assumption.
        intros. inv H.
          assumption.
          apply IHt. assumption.
Qed.
(* end hide *)

Lemma elem_span_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    span p l = None -> forall x : A, elem x l -> p x = false.
(* begin hide *)
Proof.
  induction 2; cbn in H.
    destruct (p x).
      inv H.
      reflexivity.
    destruct (p h).
      inv H.
      apply IHelem. destruct (span p t).
        destruct p0, p0. inv H.
        reflexivity.
Qed.
(* end hide *)

Lemma elem_span_Some :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) -> 
      forall y : A, elem y l <-> elem y b \/ y = x \/ elem y e.
(* begin hide *)
Proof.
  intros. apply span_spec in H.
  rewrite H, elem_app, elem_cons'. reflexivity.
Qed.
(* end hide *)

Lemma elem_span :
  forall (A : Type) (p : A -> bool) (l : list A),
    match span p l with
    | None => forall x : A, elem x l -> p x = false
    | Some (b, x, e) =>
        forall y : A, elem y l <-> elem y b \/ y = x \/ elem y e
    end.
(* begin hide *)
Proof.
  intros. destruct (span p l) eqn: Heq.
    destruct p0, p0. eapply elem_span_Some. eassumption.
    apply elem_span_None. assumption.
Qed.
(* end hide *)

Lemma elem_removeFirst_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p l = None ->
      forall x : A, elem x l -> p x = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H0.
    destruct (p h) eqn: Hph.
      inv H.
      destruct (removeFirst p t) eqn: Heq.
        destruct p0. inv H.
        inv H0.
          assumption.
          apply IHt; [reflexivity | assumption].
Qed.
(* end hide *)

Lemma elem_zip :
  forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    elem (a, b) (zip la lb) -> elem a la /\ elem b lb.
(* begin hide *)
Proof.
  induction la; cbn.
    inversion 1.
    destruct lb; cbn; inversion 1; subst; cbn in *.
      split; constructor.
      destruct (IHla _ H2). split; right; assumption.
Qed.
(* end hide *)

Lemma zip_not_elem :
  exists (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    elem a la /\ elem b lb /\ ~ elem (a, b) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists true, false.
  exists [true; false], [true; false].
  cbn. repeat split.
    repeat constructor.
    repeat constructor.
    inversion 1; subst. inversion H2; subst. inversion H3.
Qed.
(* end hide *)

Lemma elem_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    elem n (findIndices p l) ->
      exists x : A, nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h) eqn: H'.
      inversion H; subst; clear H; cbn.
        exists h. split; trivial.
        destruct n as [| n']; cbn.
          exists h. split; trivial.
          rewrite elem_map_conv in H2. destruct H2 as (n'' & IH1 & IH2).
            destruct (IHt _ IH2) as (i & IH1' & IH2'). exists i.
              inversion IH1; subst. split; trivial.
      destruct n as [| n'].
        rewrite elem_map_conv in H. destruct H as [n [Hn _]].
          inversion Hn.
        rewrite elem_map_conv in H. destruct H as (n'' & H1 & H2).
          destruct (IHt _ H2) as (x & IH1 & IH2).
            inversion H1; subst; cbn. exists x. split; trivial.
Qed.
(* end hide *)

Lemma isEmpty_bind :
  forall (A B : Type) (f : A -> list B) (l : list A),
    isEmpty (bind f l) = true <->
    l = [] \/ l <> [] /\ forall x : A, elem x l -> f x = [].
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      left. reflexivity.
      right. destruct (f h) eqn: Hfh; cbn in *.
        destruct (IHt H); subst.
          split; inversion 1; subst.
            assumption.
            inversion H3.
          destruct H0. split; inversion 1; subst.
            assumption.
            apply H1. assumption.
        inversion H.
    destruct 1 as [H | [H1 H2]]; subst.
      cbn. reflexivity.
      induction l as [| h t]; cbn.
        contradiction H1. reflexivity.
        destruct t as [| h' t']; cbn in *.
          rewrite app_nil_r. rewrite (H2 h).
            cbn. reflexivity.
            constructor.
          rewrite isEmpty_app, (H2 h); cbn.
            apply IHt.
              inversion 1.
              inversion 1; subst.
                apply H2. do 2 constructor.
                apply H2. do 2 constructor. assumption.
            constructor.
Qed.
(* end hide *)

Lemma elem_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A) (a : A) (b : B),
    f a = Some b -> elem a l -> elem b (pmap f l).
(* begin hide *)
Proof.
  induction 2; cbn.
    rewrite H. left.
    destruct (f h); try right; apply IHelem, H.
Qed.
(* end hide *)

Lemma elem_pmap' :
  forall (A B : Type) (f : A -> option B) (l : list A) (b : B),
    (exists a : A, elem a l /\ f a = Some b) -> elem b (pmap f l).
(* begin hide *)
Proof.
  destruct 1 as (a & H1 & H2). eapply elem_pmap; eauto.
Qed.
(* end hide *)

Lemma elem_pmap_conv :
  forall (A B : Type) (f : A -> option B) (l : list A) (b : B),
    elem b (pmap f l) -> exists a : A, elem a l /\ f a = Some b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (f h) eqn: Heq; cbn.
      inversion H; subst; clear H.
        exists h. split; [left | assumption].
        destruct (IHt _ H2) as (a & IH1 & IH2).
          exists a. split; try right; assumption.
      destruct (IHt _ H) as (a & IH1 & IH2).
        exists a. split; try right; assumption.
Qed.
(* end hide *)

Lemma elem_intersperse :
  forall (A : Type) (x y : A) (l : list A),
    elem x (intersperse y l) <-> elem x l \/ (x = y /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (intersperse y t) eqn : Heq.
        inversion H; subst.
          do 2 left.
          inversion H2.
        inversion H; subst.
          do 2 left.
          inversion H2; subst.
            destruct t; cbn in *.
              inversion Heq.
              right. split; trivial. lia.
            destruct (IHt H3).
              left. right. assumption.
              destruct H0. right. split; [assumption | lia].
    destruct 1.
      induction H; cbn.
        destruct (intersperse y l); left.
        destruct (intersperse y t).
          inversion IHelem.
          do 2 right. assumption.
      destruct H; subst. destruct l as [| h [| h' t]]; cbn.
        1-2: cbn in H0; lia.
        destruct (intersperse y t); cbn.
          right. left.
          right. left.
Qed.
(* end hide *)

Lemma groupBy_elem :
  forall (A : Type) (p : A -> A -> bool) (x : A) (l : list A),
    elem x l -> exists g : list A, elem x g /\ elem g (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l.
    inversion H.
    gb.
    inversion H; subst; clear H.
      exists [h]. split; constructor.
      inversion H2.
    gb.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists (h :: h' :: t'). split; constructor.
      destruct (IHl0 H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists (h :: h' :: t'). split.
            right. assumption.
            left.
          exists g. split; try right; assumption.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists [h]. split; constructor.
      destruct (IHl0 H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists (h' :: t'). split.
            assumption.
            right. left.
          exists g. split; repeat right; assumption.
Qed.
(* end hide *)

Lemma groupBy_elem_nil :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    ~ elem [] (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l.
    inversion 1.
    intro. inversion H; subst. inversion H2.
    gb.
    inversion 1; subst. apply IHl0. rewrite e0. right. assumption.
    inversion 1; subst. apply IHl0. rewrite e0. assumption.
Qed.
(* end hide *)

Lemma elem_insert_before_in :
  forall (A : Type) (x : A) (l1 l2 : list A) (n : nat),
    elem x (insertBefore.insertBefore n l1 l2) <->
    elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insertBefore.insert_before_in_nil. firstorder. inversion H.
    destruct n as [| n']; cbn.
      rewrite elem_app, ?elem_cons'. firstorder congruence.
      rewrite ?elem_cons', IHt. firstorder congruence.
Qed.
(* end hide *)

(** ** [In] *)

(** Gratuluję, udało ci się zdefiniować predykat [elem] i dowieść wszystkich
    jego właściwości. To jednak nie koniec zabawy, gdyż predykaty możemy
    definiować nie tylko przez indukcję, ale także przez rekursję. Być może
    taki sposób definiowania jest nawet lepszy? Przyjrzyjmy się poniższej
    definicji — tak właśnie "bycie elementem" jest zdefiniowane w bibliotece
    standardowej. *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
match l with
| [] => False
| h :: t => x = h \/ In x t
end.

(** Powyższa definicja jest bardzo podobna do tej induktywnej. [In x]
    dla listy pustej redukuje się do [False], co oznacza, że w pustej
    liście nic nie ma, zaś dla listy mającej głowę i ogon redukuje się do
    zdania "[x] jest głową lub jest elementem ogona".

    Definicja taka ma swoje wady i zalety. Największą moim zdaniem wadą jest
    to, że nie możemy robić indukcji po dowodzie, gdyż dowód faktu [In x l]
    nie jest induktywny. Największą zaletą zaś jest fakt, że nie możemy robić
    indukcji po dowodzie — im mniej potencjalnych rzeczy, po których można
    robić indukcję, tym mniej zastanawiania się. Przekonajmy się zatem na
    własnej skórze, która definicja jest "lepsza". *)

Lemma In_elem :
  forall (A : Type) (x : A) (l : list A),
    In x l <-> elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct H.
        subst. left.
        right. apply IHt, H.
    induction 1.
      left. reflexivity.
      right. assumption.
Qed.
(* end hide *)

Lemma In_not_nil :
  forall (A : Type) (x : A), ~ In x [].
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma In_not_cons :
  forall (A : Type) (x h : A) (t : list A),
    ~ In x (h :: t) -> x <> h /\ ~ In x t.
(* begin hide *)
Proof.
  split; intro; apply H; [left | right]; assumption.
Qed.
(* end hide *)

Lemma In_cons :
  forall (A : Type) (x h : A) (t : list A),
    In x (h :: t) <-> x = h \/ In x t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma In_snoc :
  forall (A : Type) (x y : A) (l : list A),
    In x (snoc y l) <-> In x l \/ x = y.
(* begin hide *)
Proof.
  intros. rewrite ?In_elem. apply elem_snoc.
Qed.
(* end hide *)

Lemma In_app_l :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x l1 -> In x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    contradiction.
    destruct H; [left | right].
      assumption.
      apply IHt1, H.
Qed.
(* end hide *)

Lemma In_app_r :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x l2 -> In x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    assumption.
    right. apply IHt. assumption.
Qed.
(* end hide *)

Lemma In_or_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x l1 \/ In x l2 -> In x (l1 ++ l2).
(* begin hide *)
Proof.
  destruct 1; [apply In_app_l | apply In_app_r]; assumption.
Qed.
(* end hide *)

Lemma In_app_or :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x (l1 ++ l2) -> In x l1 \/ In x l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    right. assumption.
    destruct H.
      do 2 left. assumption.
      destruct (IHt1 _ H).
        left. right. assumption.
        right. assumption.
Qed.
(* end hide *)

Lemma In_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x (l1 ++ l2) <-> In x l1 \/ In x l2.
(* begin hide *)
Proof.
  split; intros; [apply In_app_or | apply In_or_app]; assumption.
Qed.
(* end hide *)

Lemma In_spec :
  forall (A : Type) (x : A) (l : list A),
    In x l <-> exists l1 l2 : list A, l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct H; subst.
        exists [], t. cbn. reflexivity.
        destruct (IHt H) as (l1 & l2 & IH); subst.
          exists (h :: l1), l2. cbn. reflexivity.
    destruct 1 as (l1 & l2 & H); subst.
      rewrite In_app. right. left. reflexivity.
Qed.
(* end hide *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct H; subst; [left | right].
      reflexivity.
      apply IHt, H.
Qed.
(* end hide *)

Lemma In_map_conv :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x : A, f x = y /\ In x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct H; subst.
        exists h. split; trivial. left. reflexivity.
        destruct (IHt H) as (x & H1 & H2). exists x.
          split; trivial. right. assumption.
    destruct 1 as [x [<- H2]]. apply In_map, H2.
Qed.
(* end hide *)

Lemma In_map_conv' :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    (forall x y : A, f x = f y -> x = y) ->
      In (f x) (map f l) -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct H0.
      specialize (H _ _ H0). subst. left. reflexivity.
      right. apply IHt; assumption.
Qed.
(* end hide *)

Lemma map_ext_In :
  forall (A B : Type) (f g : A -> B) (l : list A),
    (forall x : A, In x l -> f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite H, IHt.
      reflexivity.
      intros. apply H. right. assumption.
      left. reflexivity.
Qed.
(* end hide *)

Lemma In_join :
  forall (A : Type) (x : A) (ll : list (list A)),
    In x (join ll) <->
    exists l : list A, In x l /\ In l ll.
(* begin hide *)
Proof.
  split.
    induction ll as [| h t]; cbn; intros.
      contradiction.
      rewrite In_app in H. destruct H.
        exists h. split; try left; trivial.
        destruct (IHt H) as [l [H1 H2]].
          exists l. split; try right; assumption.
    destruct 1 as (l & H1 & H2).
    induction ll as [| h t]; cbn in *.
      assumption.
      destruct H2; subst.
        apply In_app_l. assumption.
        apply In_app_r, IHt, H.
Qed.
(* end hide *)

Lemma In_replicate :
  forall (A : Type) (n : nat) (x y : A),
    In y (replicate n x) <-> n <> 0 /\ x = y.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; inversion 1; subst.
      split; auto.
      destruct (IHn' H0). auto.
    intros [H H']. rewrite H'. destruct n as [| n'].
      contradiction H. trivial.
      cbn. left. reflexivity.
Qed.
(* end hide *)

Lemma In_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x y : A),
    In y (iterate f n x) <-> exists k : nat, k < n /\ y = iter f k x.
(* begin hide *)
Proof.
  split.
    revert f x y. induction n as [| n']; cbn; intros.
      contradiction.
      destruct H.
        rewrite H. exists 0. cbn. split.
          apply le_n_S, Nat.le_0_l.
          reflexivity.
        destruct (IHn' _ _ _ H) as (n & IH1 & IH2). exists (S n). split.
          now apply Nat.succ_lt_mono in IH1.
          cbn. assumption.
    revert f x y. induction n as [| n']; cbn; intros.
      destruct H as (k & H1 & H2). inv H1.
      destruct H as (k & H1 & H2). destruct k as [| k']; cbn in *.
        left. assumption.
        right. rewrite H2. apply IHn'. exists k'. split.
          apply Nat.succ_lt_mono. assumption.
          reflexivity.
Qed.
(* end hide *)

Lemma nth_In :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A, nth n l = Some x /\ In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      exists h. repeat constructor.
      apply Nat.succ_lt_mono in H. destruct (IHt _ H) as (x & IH1 & IH2).
        exists x. split; try right; assumption.
Qed.
(* end hide *)

Lemma iff_In_nth :
  forall (A : Type) (x : A) (l : list A),
    In x l <-> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct H; subst.
        exists 0. reflexivity.
        destruct (IHt H) as (n & IH). exists (S n). assumption.
    induction l as [| h t]; cbn; intros.
      destruct H. inv H.
      destruct H as (n & H). destruct n as [| n'].
        inv H. left. reflexivity.
        right. apply IHt. exists n'. assumption.
Qed.
(* end hide *)

Lemma In_rev :
  forall (A : Type) (x : A) (l : list A),
    In x (rev l) <-> In x l.
(* begin hide *)
Proof.
  intros. rewrite ?In_elem in *. apply elem_rev.
Qed.
(* end hide *)

Lemma In_take :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    In x (take n l) -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; inversion H; subst; clear H.
      left. reflexivity.
      right. apply (IHt _ _ H0).
Qed.
(* end hide *)

Lemma In_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    In x (drop n l) -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n'].
      assumption.
      right. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma In_splitAt :
  forall (A : Type) (l b e : list A) (n : nat) (x y : A),
    splitAt n l = Some (b, x, e) ->
      In y l <-> In y b \/ x = y \/ In y e.
(* begin hide *)
Proof.
  intros. pose (splitAt_spec _ l n). rewrite H in y0. subst.
  rewrite In_app. cbn. firstorder.
Qed.
(* end hide *)

Lemma In_insert :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    In y (insert l n x) <-> x = y \/ In y l.
(* begin hide *)
Proof.
  split; revert n x.
    induction l as [| h t]; cbn; intros.
      firstorder.
      destruct n as [| n']; cbn in *.
        clear IHt. firstorder.
        firstorder.
    induction l as [| h t]; cbn; intros.
      firstorder.
      destruct n as [| n']; cbn.
        clear IHt. firstorder.
        firstorder.
Qed.
(* end hide *)

Lemma In_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    replace l n x = Some l' ->
      In y l' <-> In y (take n l) \/ x = y \/ In y (drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H. destruct (n <? length l).
    inv H. rewrite In_app, In_cons. firstorder.
    inv H.
Qed.
(* end hide *)

Lemma In_filter :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x (filter p l) <-> p x = true /\ In x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      case_eq (p h); intros; rewrite H0 in *.
        inversion H; subst; clear H.
          repeat constructor. assumption.
          destruct (IHt H1). firstorder constructor.
        destruct (IHt H). firstorder constructor.
    induction l as [| h t]; cbn; destruct 1.
      assumption.
      case_eq (p h); cbn; intros.
        destruct H0; [left | right].
          assumption.
          apply IHt. split; assumption.
        destruct H0; subst.
          congruence.
          apply IHt. split; assumption.
Qed.
(* end hide *)

Lemma In_filter_conv :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    In x l <->
    In x (filter p l) /\ p x = true \/
    In x (filter (fun x : A => negb (p x)) l) /\ p x = false.
(* begin hide *)
Proof.
  split; rewrite ?In_filter.
  destruct (p x). all: firstorder.
Qed.
(* end hide *)

Lemma In_partition :
  forall (A : Type) (p : A -> bool) (x : A) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      In x l <->
      (In x l1 /\ p x = true) \/ (In x l2 /\ p x = false).
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H. inversion H; subst; clear H.
  rewrite (In_filter_conv _ p). reflexivity.
Qed.
(* end hide *)

Lemma In_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x (takeWhile p l) -> In x l /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction.
    case_eq (p h); intros; rewrite H0 in *; cbn in *.
      split; destruct H; subst.
        left. reflexivity.
          right. destruct (IHt _ H). assumption.
          assumption.
          destruct (IHt _ H). assumption.
      contradiction.
Qed.
(* end hide *)

Lemma In_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x (dropWhile p l) -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction.
    case_eq (p h); intros; rewrite H0 in *; cbn in *.
      right. apply IHt. assumption.
      assumption.
Qed.
(* end hide *)

Lemma In_takeWhile_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x l ->
      In x (takeWhile p l) \/
      In x (dropWhile p l).
(* begin hide *)
Proof.
  intros. apply In_app. rewrite takeWhile_dropWhile_spec. assumption.
Qed.
(* end hide *)

Lemma In_dropWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x l -> ~ In x (dropWhile p l) -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction.
    case_eq (p h); intros; rewrite H1 in *; cbn in *.
      destruct H; subst.
        assumption.
        apply IHt; assumption.
      contradiction.
Qed.
(* end hide *)

Lemma In_span :
  forall (A : Type) (p : A -> bool) (x y : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      In y l <-> In y b \/ y = x \/ In y e.
(* begin hide *)
(* TODO: In_span jak elem (nie pamiętam, o co chodzi) *)
Proof.
  intros. rewrite ?In_elem. assert (H' := elem_span _ p l).
  rewrite H in H'. rewrite H'. reflexivity.
Qed.
(* end hide *)

Lemma In_zip :
  forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    In (a, b) (zip la lb) -> In a la /\ In b lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    contradiction.
    destruct lb as [| hb tb]; cbn in *.
      contradiction.
      destruct H.
        inversion H; subst. split; left; reflexivity.
      destruct (IHta _ H). split; right; assumption.
Qed.
(* end hide *)

Lemma zip_not_In :
  exists (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    In a la /\ In b lb /\ ~ In (a, b) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists true, false.
  exists [true; false], [true; false].
  cbn. repeat split.
    repeat constructor.
    right; left. reflexivity.
    inversion 1; inversion H0; subst.
      inversion H1.
      contradiction.
Qed.
(* end hide *)

Lemma In_intersperse :
  forall (A : Type) (x y : A) (l : list A),
    In x (intersperse y l) <->
    In x l \/ (x = y /\ 2 <= length l).
(* begin hide *)
Proof.
  intros. rewrite ?In_elem. apply elem_intersperse.
Qed.
(* end hide *)

Lemma In_insert_before_in :
  forall (A : Type) (x : A) (l1 l2 : list A) (n : nat),
    In x (insertBefore.insertBefore n l1 l2) <->
    In x l1 \/ In x l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insertBefore.insert_before_in_nil. firstorder.
    destruct n as [| n']; cbn.
      rewrite In_app; cbn. firstorder congruence.
      rewrite IHt. firstorder congruence.
Qed.
(* end hide *)

(** ** [NoDup] *)

(** Zdefiniuj induktywny predykat [NoDup]. Zdanie [NoDup l] jest prawdziwe,
    gdy w [l] nie ma powtarzających się elementów. Udowodnij, że zdefiniowany
    przez ciebie predykat posiada pożądane właściwości. *)

(* begin hide *)
Inductive NoDup {A : Type} : list A -> Prop :=
| NoDup_nil : NoDup []
| NoDup_cons :
    forall (h : A) (t : list A),
      ~ elem h t -> NoDup t -> NoDup (h :: t).
(* end hide *)

Lemma NoDup_singl :
  forall (A : Type) (x : A), NoDup [x].
(* begin hide *)
Proof.
  repeat constructor. inversion 1.
Qed.
(* end hide *)

Lemma NoDup_cons_inv :
  forall (A : Type) (h : A) (t : list A),
    NoDup (h :: t) -> NoDup t.
(* begin hide *)
Proof.
  intros. inv H. assumption.
Qed.
(* end hide *)

Lemma NoDup_length :
  forall (A : Type) (l : list A),
    ~ NoDup l -> 2 <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction H. constructor.
    destruct t as [| h' t']; cbn.
      contradiction H. apply NoDup_singl.
      apply le_n_S, le_n_S, Nat.le_0_l.
Qed.
(* end hide *)

Lemma NoDup_snoc :
  forall (A : Type) (x : A) (l : list A),
    NoDup (snoc x l) <-> NoDup l /\ ~ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      split.
        constructor.
        inversion 1.
      inversion H; subst; clear H. split.
        constructor.
          intro. apply H2. rewrite elem_snoc. left. assumption.
          destruct (IHt H3). assumption.
        inversion 1; subst.
          apply H2. rewrite elem_snoc. right. reflexivity.
          destruct (IHt H3). contradiction.
    destruct 1. induction H; cbn.
      repeat constructor. inversion 1.
      constructor.
        intro. rewrite elem_snoc in H2. destruct H2; subst.
          contradiction.
          apply H0. left.
        apply IHNoDup. intro. apply H0. right. assumption.
Qed.
(* end hide *)

Lemma NoDup_app :
  forall (A : Type) (l1 l2 : list A),
    NoDup (l1 ++ l2) <->
    NoDup l1 /\
    NoDup l2 /\
    (forall x : A, elem x l1 -> ~ elem x l2) /\
    (forall x : A, elem x l2 -> ~ elem x l1).
(* begin hide *)
Proof.
  split; intros.
    induction l1 as [| h1 t1]; cbn; intros.
      repeat split; firstorder.
        constructor.
        inversion H0.
        intro. inversion H1.
      inversion H; subst; clear H. rewrite elem_app in H2.
        decompose [and] (IHt1 H3); clear IHt1. repeat split; intros.
          constructor.
            firstorder.
            assumption.
          assumption.
          inversion H4; firstorder.
          inversion 1; subst; firstorder.
  decompose [and] H; clear H.
  induction H0; cbn.
    assumption.
    constructor.
      rewrite elem_app. destruct 1.
        contradiction.
        apply (H1 h).
          constructor.
          assumption.
      apply IHNoDup; intros.
        intro. apply (H1 x).
          constructor. assumption.
          assumption.
        intro. apply (H4 x).
          assumption.
          constructor. assumption.
Qed.
(* end hide *)

Lemma NoDup_app_comm :
  forall (A : Type) (l1 l2 : list A),
    NoDup (l1 ++ l2) <-> NoDup (l2 ++ l1).
(* begin hide *)
Proof.
  intro.
  assert (forall l1 l2 : list A, NoDup (l1 ++ l2) -> NoDup (l2 ++ l1)).
    intros l1 l2. revert l1. induction l2 as [| h t]; cbn; intros.
      rewrite app_nil_r in H. assumption.
      constructor.
        intro. apply NoDup_app in H. decompose [and] H; clear H.
          apply elem_app_or in H0. destruct H0.
            inversion H3. contradiction.
            specialize (H5 _ ltac:(left)). contradiction.
        apply IHt. apply NoDup_app in H. apply NoDup_app.
          decompose [and] H; clear H. repeat split.
            assumption.
            inversion H2. assumption.
            intros. specialize (H1 _ H). intro. apply H1. right. assumption.
            repeat intro. apply (H1 _ H3). right. assumption.
      intros. split; apply H.
Qed.
(* end hide *)

Lemma NoDup_rev :
  forall (A : Type) (l : list A),
    NoDup (rev l) <-> NoDup l.
(* begin hide *)
Proof.
  (* TODO: być może dobry przykład do zilustrowania reguły
         wlog (bez straty ogólności)? *)
  assert (forall (A : Type) (l : list A), NoDup l -> NoDup (rev l)).
    induction 1; cbn.
      constructor.
      apply NoDup_snoc; repeat split; intros.
        assumption.
        intro. rewrite elem_rev in H1. contradiction.
  split; intro.
    rewrite <- rev_rev. apply H. assumption.
    apply H. assumption.
Qed.
(* end hide *)

Lemma NoDup_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    NoDup (map f l) -> NoDup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  constructor; inversion H; subst; clear H.
    intro. apply H2, elem_map. assumption.
    apply IHt. assumption.
Qed.
(* end hide *)

Lemma NoDup_map_inj :
  forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y : A, f x = f y -> x = y) ->
      NoDup l -> NoDup (map f l).
(* begin hide *)
Proof.
  induction 2; cbn; constructor.
    intro. apply H0, (elem_map_conv' _ _ f _ h H). assumption.
    assumption.
Qed.
(* end hide *)

Lemma NoDup_replicate :
  forall (A : Type) (n : nat) (x : A),
    NoDup (replicate n x) <-> n = 0 \/ n = 1.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; intros.
      left. reflexivity.
      inversion H; subst. destruct (IHn' H3); subst.
        right. reflexivity.
        contradiction H2. constructor.
    destruct 1; subst; cbn; repeat constructor. inversion 1.
Qed.
(* end hide *)

Lemma NoDup_take :
  forall (A : Type) (l : list A) (n : nat),
    NoDup l -> NoDup (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn; constructor.
      intro. inversion H; subst; clear H.
        apply elem_take in H0. contradiction.
      apply IHt. inversion H. assumption.
Qed.
(* end hide *)

Lemma NoDup_drop :
  forall (A : Type) (l : list A) (n : nat),
    NoDup l -> NoDup (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      apply IHt. inversion H. assumption.
Qed.
(* end hide *)

Lemma NoDup_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    NoDup l -> NoDup (filter p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h).
      constructor.
        intro. apply H. apply elem_filter in H1. destruct H1. assumption.
        assumption.
      assumption.
Qed.
(* end hide *)

Lemma NoDup_partition :
  forall (A : Type) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) -> NoDup l <-> NoDup l1 /\ NoDup l2.
(* begin hide *)
Proof.
  split.
    intro. revert dependent l2. revert dependent l1.
    induction H0; cbn in *; intros.
      inversion H; subst; clear H. split; constructor.
      case_eq (partition p t); case_eq (p h); intros; rewrite H2, H3 in *.
        inversion H1; subst; clear H1. destruct (IHNoDup _ _ eq_refl). split.
          constructor.
            intro. apply H. apply (elem_partition _ _ h) in H3.
              rewrite H3. left. split; assumption.
            assumption.
          assumption.
        inversion H1; subst; clear H1. destruct (IHNoDup _ _ eq_refl). split.
          assumption.
          constructor.
            intro. apply H. apply (elem_partition _ _ h) in H3. rewrite H3.
              right. split; assumption.
            assumption.
    revert dependent l2; revert dependent l1.
    induction l as [| h t]; cbn in *; intros.
      constructor.
      constructor.
        2: {
          destruct (partition p t), (p h).
            destruct H0. inversion H; subst; inversion H0; subst; clear H H0.
              eapply IHt; eauto.
            destruct H0. inversion H; subst; inversion H1; subst; clear H H1.
              eapply IHt; eauto.
        }
        intro. case_eq (partition p t); case_eq (p h); intros; subst;
        rewrite H2, H3 in *; inversion H; subst; clear H.
          pose (H4 := H3). apply (elem_partition _ _ h) in H4.
            rewrite H4 in H1. destruct H1.
              destruct H0. inversion H0. destruct H; contradiction.
              rewrite partition_spec in H3. inversion H3; subst; clear H3.
                destruct H. apply elem_filter in H. destruct H. destruct (p h).
                  inversion H.
                  inversion H2.
          pose (H4 := H3). apply (elem_partition _ _ h) in H4.
            rewrite H4 in H1. destruct H1.
              rewrite partition_spec in H3. inversion H3; subst; clear H3.
                destruct H. apply elem_filter in H. destruct H. destruct (p h).
                  inversion H2.
                  inversion H.
              destruct H0. inversion H1. destruct H. contradiction.
Qed.
(* end hide *)

Lemma NoDup_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    NoDup l -> NoDup (takeWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h); constructor.
      intro. apply H. apply elem_takeWhile in H1. destruct H1. assumption.
      assumption.
Qed.
(* end hide *)

Lemma NoDup_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    NoDup l -> NoDup (dropWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h).
      assumption.
      constructor; assumption.
Qed.
(* end hide *)

Lemma NoDup_zip :
  forall (A B : Type) (la : list A) (lb : list B),
    NoDup la /\ NoDup lb -> NoDup (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    constructor.
    destruct lb as [| hb tb]; cbn in *.
      constructor.
      destruct H. inversion H; inversion H0; subst; clear H H0; constructor.
        intro. apply elem_zip in H. destruct H. contradiction.
        apply IHta. split; assumption.
Qed.
(* end hide *)

Lemma NoDup_zip_conv :
  exists (A B : Type) (la : list A) (lb : list B),
    NoDup (zip la lb) /\ ~ NoDup la /\ ~ NoDup lb.
(* begin hide *)
Proof.
  exists bool, bool, [true; false; true], [false; false; true]. split.
    cbn. repeat constructor; intro; inv H; inv H2; inv H1.
    split; intro; inv H; apply H2.
      right. left.
      left.
Qed.
(* end hide *)

Lemma NoDup_pmap :
  exists (A B : Type) (f : A -> option B) (l : list A),
    NoDup l /\ ~ NoDup (pmap f l).
(* begin hide *)
Proof.
  exists bool, unit, (fun _ => Some tt), [true; false]. split.
    repeat constructor; inversion 1. inversion H2.
    cbn. inversion 1; subst. apply H2. constructor.
Qed.
(* end hide *)

Lemma NoDup_intersperse :
  forall (A : Type) (x : A) (l : list A),
    NoDup (intersperse x l) -> length l <= 2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply Nat.le_0_l.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        apply le_S, le_n.
        destruct (intersperse x t); inversion Heq.
      inversion H. inversion H3. subst. specialize (IHt H7).
        destruct t as [| w1 [| w2 z]]; cbn in *.
          inversion Heq.
          apply le_n.
          destruct (intersperse x z).
            inversion Heq. subst. contradiction H6. right. left.
            inversion Heq; subst. contradiction H6. right. left.
Qed.
(* end hide *)

Lemma NoDup_spec :
  forall (A : Type) (l : list A),
    ~ NoDup l <->
    exists (x : A) (l1 l2 l3 : list A),
      l = l1 ++ x :: l2 ++ x :: l3.
(* begin hide *)
Proof.
  split.
    2: {
      destruct 1 as (x & l1 & l2 & l3 & H). subst. intro.
        rewrite <- !app_cons_l in H. rewrite !NoDup_app in H.
        decompose [and] H; clear H. specialize (H4 x). apply H4; constructor.
    }
    induction l as [| h t]; cbn; intros.
      contradiction H. constructor.
      change (h :: t) with ([h] ++ t) in H. rewrite NoDup_app in H.
        contradiction H.
Abort. (* Ten [Abort] jest umyślny. *)
(* end hide *)

(** ** [Dup] *)

(** Powodem problemów z predykatem [NoDup] jest fakt, że jest on w pewnym
    sensie niekonstruktywny. Wynika to wprost z jego definicji: [NoDup l]
    zachodzi, gdy w [l] nie ma duplikatów. Parafrazując: [NoDup l] zachodzi,
    gdy _nieprawda_, że w [l] są duplikaty.

    Jak widać, w naszej definicji implicite występuje negacja. Wobec tego
    jeżeli spróbujemy za pomocą [NoDup] wyrazić zdanie "na liście [l] są
    duplikaty", to tak naprawdę dostaniemy zdanie "nieprawda, że nieprawda,
    że [l] ma duplikaty".

    Dostaliśmy więc po głowie nagłym atakiem podwójnej negacji. Nie ma się
    co dziwić w takiej sytuacji, że nasza "negatywna" definicja predykatu
    [NoDup] jest nazbyt klasyczna. Możemy jednak uratować sytuację, jeżeli
    zdefiniujemy predykat [Dup] i zanegujemy go.

    Zdefiniuj predykat [Dup], który jest spełniony, gdy na liście występują
    duplikaty. *)

(* begin hide *)
Inductive Dup {A : Type} : list A -> Prop :=
| Dup_elem :
    forall (h : A) (t : list A),
      elem h t -> Dup (h :: t)
| Dup_tail :
    forall (h : A) (t : list A),
      Dup t -> Dup (h :: t).
(* end hide *)

Lemma Dup_nil :
  forall A : Type, ~ Dup (@nil A).
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma Dup_cons :
  forall (A : Type) (x : A) (l : list A),
    Dup (x :: l) <-> elem x l \/ Dup l.
(* begin hide *)
Proof.
  split; intro.
    inv H; [left | right]; assumption.
    destruct H; constructor; assumption.
Qed.
(* end hide *)

Lemma Dup_singl :
  forall (A : Type) (x : A), ~ Dup [x].
(* begin hide *)
Proof.
  inversion 1; subst; inversion H1.
Qed.
(* end hide *)

Lemma Dup_cons_inv :
  forall (A : Type) (h : A) (t : list A),
    ~ Dup (h :: t) -> ~ elem h t /\ ~ Dup t.
(* begin hide *)
Proof.
  intros. split; intro; apply H; [left | right]; assumption.
Qed.
(* end hide *)

Lemma Dup_spec :
  forall (A : Type) (l : list A),
    Dup l <->
    exists (x : A) (l1 l2 l3 : list A),
      l = l1 ++ x :: l2 ++ x :: l3.
(* begin hide *)
Proof.
  split.
    induction 1.
      induction H.
        exists x, [], [], l. cbn. reflexivity.
        destruct IHelem as (x' & l1 & l2 & l3 & H').
          destruct l1; inversion H'; subst; clear H'.
            exists x', [], (h :: l2), l3. cbn. reflexivity.
            exists x', (a :: h :: l1), l2, l3. cbn. reflexivity.
      destruct IHDup as (x' & l1 & l2 & l3 & H'); subst.
        exists x', (h :: l1), l2, l3. cbn. reflexivity.
    destruct 1 as (x & l1 & l2 & l3 & H); subst.
    induction l1 as [| h1 t1]; cbn.
      constructor. rewrite elem_app. right. constructor.
      right. assumption.
Qed.
(* end hide *)

Lemma Dup_NoDup :
  forall (A : Type) (l : list A),
    ~ Dup l <-> NoDup l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      constructor.
      constructor.
        intro. apply H. left. assumption.
        apply IHt. intro. apply H. right. assumption.
    induction 1; cbn; intro.
      inversion H.
      inversion H1; subst; clear H1; contradiction.
Qed.
(* end hide *)

Lemma Dup_length :
  forall (A : Type) (l : list A),
    Dup l -> 2 <= length l.
(* begin hide *)
Proof.
  induction 1; cbn.
    destruct t; cbn.
      inversion H.
      apply le_n_S, le_n_S, Nat.le_0_l.
    apply Nat.le_trans with (length t).
      assumption.
      apply le_S. apply Nat.le_refl.
Qed.
(* end hide *)

Lemma Dup_snoc :
  forall (A : Type) (x : A) (l : list A),
    Dup (snoc x l) <-> Dup l \/ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H; subst; inversion H1.
      inversion H; subst; clear H.
        rewrite elem_snoc in H1. destruct H1.
          left. constructor. assumption.
          right. subst. left.
        destruct (IHt H1).
          left. right. assumption.
          do 2 right. assumption.
    destruct 1.
      induction H; cbn.
        left. rewrite elem_snoc. left. assumption.
        right. assumption.
      induction H; cbn.
        left. rewrite elem_snoc. right. reflexivity.
        right. assumption.
Qed.
(* end hide *)

Lemma Dup_app_l :
  forall (A : Type) (l1 l2 : list A),
    Dup l1 -> Dup (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor. apply elem_app_l. assumption.
    right. assumption.
Qed.
(* end hide *)

Lemma Dup_app_r :
  forall (A : Type) (l1 l2 : list A),
    Dup l2 -> Dup (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    right. apply (IHt1 _ H).
Qed.
(* end hide *)

Lemma Dup_app_both :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l1 -> elem x l2 -> Dup (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. apply elem_app_r. assumption.
    right. apply IHelem, H0.
Qed.
(* end hide *)

Lemma Dup_app :
  forall (A : Type) (l1 l2 : list A),
    Dup (l1 ++ l2) <->
    Dup l1 \/ Dup l2 \/ exists x : A, elem x l1 /\ elem x l2.
(* begin hide *)
Proof.
  split.
    induction l1 as [| h1 t1]; cbn; intros.
      right; left. assumption.
      inversion H; subst; clear H.
        rewrite elem_app in H1. destruct H1.
          left. constructor. assumption.
          right; right. exists h1. split; [constructor | assumption].
        decompose [ex or] (IHt1 H1); clear IHt1.
          left; right. assumption.
          right; left. assumption.
          destruct H. right; right. exists x.
            split; try constructor; assumption.
    destruct 1 as [H | [H | [x [H1 H2]]]].
      apply Dup_app_l; assumption.
      apply Dup_app_r; assumption.
      apply (Dup_app_both _ x); assumption.
Qed.
(* end hide *)

Lemma Dup_rev :
  forall (A : Type) (l : list A),
    Dup (rev l) <-> Dup l.
(* begin hide *)
Proof.
  assert (forall (A : Type) (l : list A), Dup l -> Dup (rev l)).
    induction 1; cbn; rewrite Dup_snoc, elem_rev.
      right. assumption.
      left. assumption.
    split; intros.
      rewrite <- rev_rev. apply H. assumption.
      apply H. assumption.
Qed.
(* end hide *)

Lemma Dup_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    Dup l -> Dup (map f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    left. apply elem_map. assumption.
    right. assumption.
Qed.
(* end hide *)

Lemma Dup_map_conv :
  forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y : A, f x = f y -> x = y) ->
      Dup (map f l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0.
    inversion H0; subst; clear H0.
      left. apply (elem_map_conv' _ _ _ _ _ H H2).
      right. apply IHt; assumption.
Qed.
(* end hide *)

Lemma Dup_join :
  forall (A : Type) (ll : list (list A)),
    Dup (join ll) ->
    (exists l : list A, elem l ll /\ Dup l) \/
    (exists (x : A) (l1 l2 : list A),
      elem x l1 /\ elem x l2 /\ elem l1 ll /\ elem l2 ll).
(* begin hide *)
Proof.
  induction ll as [| h t]; cbn; intros.
    inversion H.
    apply Dup_app in H. decompose [or ex] H; clear H.
      left. exists h. split; [constructor | assumption].
      decompose [ex or and] (IHt H1); clear IHt.
        left. exists x. split; try right; assumption.
        right. exists x, x0, x1. firstorder (constructor; assumption).
      right. destruct H0. apply elem_join in H0. destruct H0 as [l [H1 H2]].
        exists x, h, l. firstorder.
          1-2: constructor; assumption.
Qed.
(* end hide *)

Lemma Dup_replicate :
  forall (A : Type) (n : nat) (x : A),
    Dup (replicate n x) -> 2 <= n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; inversion H; subst; clear H.
    destruct n' as [| n'']; cbn in H1.
      inversion H1.
      apply le_n_S, le_n_S, Nat.le_0_l.
    apply Nat.le_trans with n'.
      apply (IHn' _ H1).
      apply le_S, le_n.
Qed.
(* end hide *)

Lemma Dup_nth :
  forall (A : Type) (l : list A),
    Dup l <->
    exists (x : A) (n1 n2 : nat),
      n1 < n2 /\ nth n1 l = Some x /\ nth n2 l = Some x.
(* begin hide *)
Proof.
  split.
    intro. apply Dup_spec in H. destruct H as (x & l1 & l2 & l3 & H); subst.
      exists x, (length l1), (length l1 + length l2 + 1). repeat split.
        lia.
        rewrite nth_app_r.
          rewrite Nat.sub_diag. cbn. reflexivity.
          apply le_n.
        rewrite nth_app_r.
          rewrite <- app_cons_l, nth_app_r.
            replace (nth _ (x :: l3)) with (nth 0 (x :: l3)).
              cbn. reflexivity.
              f_equal. 1-3: cbn; lia.
    destruct 1 as (x & n1 & n2 & H1 & H2 & H3). revert x n1 n2 H1 H2 H3.
    induction l as [| h t]; cbn; intros.
      inv H2.
      destruct n1 as [| n1'], n2 as [| n2'].
        inv H1.
        inv H2. constructor. rewrite iff_elem_nth. exists n2'. assumption.
        inv H1.
        right. apply Nat.succ_lt_mono in H1.
          apply (IHt _ _ _ H1 H2 H3).
Qed.
(* end hide *)

Lemma Dup_take :
  forall (A : Type) (l : list A) (n : nat),
    Dup (take n l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn; inversion H; subst; clear H.
      constructor. apply elem_take in H1. assumption.
      right. apply (IHt _ H1).
Qed.
(* end hide *)

Lemma Dup_drop :
  forall (A : Type) (l : list A) (n : nat),
    Dup (drop n l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      right. apply (IHt _ H).
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Dup vs insert i replace *)
(* TODO: findIndex, takeWhile, dropWhile dla replace *)
(* end hide *)

Lemma Dup_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup (filter p l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      inversion H; subst; clear H.
        left. apply elem_filter in H1. destruct H1. assumption.
        right. apply IHt, H1.
      right. apply IHt, H.
Qed.
(* end hide *)

Lemma Dup_filter_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup l ->
      Dup (filter p l) \/
      Dup (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction 1; cbn; case_eq (p h); cbn; intros.
    do 2 left. apply elem_filter. split; assumption.
    right. left. apply elem_filter. rewrite H0. split; trivial.
    destruct IHDup.
      left. right. assumption.
      right. assumption.
    destruct IHDup.
      left. assumption.
      right. right. assumption.
Qed.
(* end hide *)

Lemma Dup_partition :
  forall (A : Type) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) -> Dup l <-> Dup l1 \/ Dup l2.
(* begin hide *)
Proof.
  split.
    intro. revert dependent l2; revert dependent l1.
    induction H0; cbn in *; intros.
      case_eq (partition p t); case_eq (p h); intros;
      rewrite H1, H2 in *; inversion H0; subst; clear H0.
        apply (elem_partition _ _ h) in H2. rewrite H2 in H. destruct H.
          do 2 left. destruct H. assumption.
          destruct H. congruence.
        apply (elem_partition _ _ h) in H2. rewrite H2 in H. destruct H.
          destruct H. congruence.
          right; left. destruct H. assumption.
      destruct (partition p t), (p h);
      inversion H; subst; clear H; destruct (IHDup _ _ eq_refl).
        left; right; assumption.
        right; assumption.
        left; assumption.
        right; right. assumption.
    revert dependent l2; revert dependent l1.
    induction l as [| h t]; cbn in *; intros.
      inversion H; subst; clear H. destruct H0; assumption.
      case_eq (partition p t); case_eq (p h); intros;
      rewrite H1, H2 in *; inversion H; subst; clear H.
        destruct H0.
          inversion H; subst; clear H.
            apply (elem_partition _ _ h) in H2. left. rewrite H2. left.
              split; assumption.
            right. apply (IHt _ _ eq_refl). left. assumption.
          right. apply (IHt _ _ eq_refl). right. assumption.
        destruct H0.
          right. apply (IHt _ _ eq_refl). left. assumption.
          inversion H; subst; clear H.
            apply (elem_partition _ _ h) in H2. left. rewrite H2.
              right. split; assumption.
            right. apply (IHt _ _ eq_refl). right. assumption.
Qed.
(* end hide *)

Lemma Dup_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup (takeWhile p l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      inversion H; subst; clear H.
        left. apply elem_takeWhile in H1. destruct H1. assumption.
        right. apply IHt, H1.
      inversion H.
Qed.
(* end hide *)

Lemma Dup_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup (dropWhile p l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      right. apply IHt, H.
      assumption.
Qed.
(* end hide *)

Lemma Dup_takeWhile_dropWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup l ->
      Dup (takeWhile p l) \/
      Dup (dropWhile p l) \/
      exists x : A,
        elem x (takeWhile p l) /\ elem x (dropWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    case_eq (p h); intro.
      apply (elem_takeWhile_dropWhile _ p) in H. destruct H.
        do 2 left. assumption.
        do 2 right. exists h. split; [constructor | assumption].
      apply (elem_takeWhile_dropWhile _ p) in H. destruct H.
        right; do 2 left. apply elem_takeWhile in H. destruct H. assumption.
        right; do 2 left. apply elem_dropWhile in H. assumption.
    case_eq (p h); intro.
      destruct IHDup as [IH | [IH | [x [H1 H2]]]].
        left; right. assumption.
        right; left. assumption.
        right; right. exists x. split; try right; assumption.
      destruct IHDup as [IH | [IH | [x [H1 H2]]]].
        right; left; right. apply (Dup_takeWhile _ p). assumption.
        right; left; right. apply (Dup_dropWhile _ p). assumption.
        right; left; right. assumption.
Qed.
(* end hide *)

Lemma Dup_span :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      Dup l <-> Dup b \/ Dup e \/ elem x b \/ elem x e \/
        exists y : A, elem y b /\ elem y e.
(* begin hide *)
Proof.
  intros. apply span_spec in H. subst.
  rewrite Dup_app, Dup_cons. firstorder.
    inv H0; firstorder.
    do 2 right. exists x. split; [assumption | left].
    do 2 right. exists x0. split; try right; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Dup vs NoDup, Rep *)
(* end hide *)

Lemma Dup_zip :
  forall (A B : Type) (la : list A) (lb : list B),
    Dup (zip la lb) -> Dup la /\ Dup lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H.
    destruct lb as [| hb tb]; cbn; inversion H; subst; clear H.
      apply elem_zip in H1. destruct H1. split; left; assumption.
      destruct (IHta _ H1). split; right; assumption.
Qed.
(* end hide *)

Lemma Dup_zip_conv :
  forall (A B : Type) (la : list A) (lb : list B),
    ~ Dup la /\ ~ Dup lb -> ~ Dup (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion 1.
    destruct lb as [| hb tb]; cbn; intros.
      inversion 1.
      inversion 1; subst; clear H0.
        apply elem_zip in H2. destruct H, H2. apply H; left; assumption.
        destruct H. apply Dup_cons_inv in H. apply Dup_cons_inv in  H0.
          destruct H, H0. apply (IHta tb); try split; assumption.
Qed.
(* end hide *)

Lemma Dup_pmap :
  exists (A B : Type) (f : A -> option B) (l : list A),
    Dup l /\ ~ Dup (pmap f l).
(* begin hide *)
Proof.
  exists unit, unit, (fun _ => None), [tt; tt]. split.
    do 2 constructor.
    cbn. inversion 1.
Qed.
(* end hide *)

Lemma Dup_intersperse :
  forall (A : Type) (x : A) (l : list A),
    Dup (intersperse x l) -> 2 <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (intersperse x t) eqn: Heq.
      inversion H; inversion H1.
      destruct t; cbn in *.
        inversion Heq.
        apply le_n_S, le_n_S, Nat.le_0_l.
Qed.
(* end hide *)

Lemma Dup_interleave :
  forall {A : Type} (l1 l2 : list A),
    Dup (interleave l1 l2) <->
    Dup l1 \/ Dup l2 \/ exists x : A, elem x l1 /\ elem x l2.
(* begin hide *)
Proof.
  intros.
  functional induction interleave l1 l2.
    firstorder; inv H.
    firstorder; inv H; inv H0.
    {
      rewrite !Dup_cons, !elem_cons', !IHl,
              !elem_Exists, !Exists_interleave, <- !elem_Exists.
      firstorder; subst; cbn in *.
        do 2 right. exists h2. split; constructor.
        do 2 right. exists h1. split; constructor; assumption.
        do 2 right. exists h2. split; constructor; assumption.
        do 2 right. exists x. split; constructor; assumption.
        inv H3; inv H4; eauto. eauto 7.
    }
Qed.
(* end hide *)

(** ** [Rep] *)

(** Jeżeli zastanowimy się chwilę, to dojdziemy do wniosku, że [Dup l]
    znaczy "istnieje x, który występuje na liście l co najmniej dwa
    razy". Widać więc, że [Dup] jest jedynie specjalnym przypadkiem
    pewngo bardziej ogólnego predykatu [Rep x n] dla dowolnego [x] oraz
    n = 2. Zdefiniuj relację [Rep]. Zdanie [Rep x n l] zachodzi, gdy
    element [x] występuje na liście [l] co najmnej [n] razy.

    Zastanów się, czy lepsza będzie definicja induktywna, czy rekurencyjna.
    Jeżeli nie masz nic lepszego do roboty, zaimplementuj obie wersje i
    porównaj je pod względem łatwości w użyciu. *)

(* begin hide *)
Inductive Rep {A : Type} (x : A) : nat -> list A -> Prop :=
| Rep_zero :
    forall l : list A, Rep x 0 l
| Rep_cons_1 :
    forall (n : nat) (l : list A),
      Rep x n l -> Rep x (S n) (x :: l)
| Rep_cons_2 :
    forall (n : nat) (l : list A) (y : A),
      Rep x n l -> Rep x n (y :: l).
(* end hide *)

Lemma Rep_S_cons :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x (S n) (y :: l) <-> (x = y /\ Rep x n l) \/ Rep x (S n) l.
(* begin hide *)
Proof.
  split; intros.
    inv H.
      left. split; [reflexivity | assumption].
      right. assumption.
    decompose [and or] H; clear H; subst; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_cons :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n (y :: l) <-> (x = y /\ Rep x (n - 1) l) \/ Rep x n l.
(* begin hide *)
Proof.
  split; intros.
    inv H.
      right. constructor.
      left. cbn. rewrite Nat.sub_0_r. split; [reflexivity | assumption].
    right. assumption.
    decompose [and or] H; clear H; subst.
      destruct n as [| n']; cbn in *; constructor.
        rewrite Nat.sub_0_r in H2. assumption.
      constructor. assumption.
Qed.
(* end hide *)

Lemma elem_Rep :
  forall (A : Type) (x : A) (l : list A),
    elem x l -> Rep x 1 l.
(* begin hide *)
Proof.
  induction 1; constructor.
    constructor.
    assumption.
Qed.
(* end hide *)

Lemma Rep_elem :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    1 <= n -> Rep x n l -> elem x l.
(* begin hide *)
Proof.
  induction 2.
    inversion H.
    left.
    destruct n as [| n'].
      inversion H.
      right. apply IHRep. apply le_n_S, Nat.le_0_l.
Qed.
(* end hide *)

Lemma Dup_Rep :
  forall (A : Type) (l : list A),
    Dup l -> exists x : A, Rep x 2 l.
(* begin hide *)
Proof.
  induction 1.
    exists h. constructor. apply elem_Rep. assumption.
    destruct IHDup as [x IH]. exists x. constructor. assumption.
Qed.
(* end hide *)

Lemma Rep_Dup :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    2 <= n -> Rep x n l -> Dup l.
(* begin hide *)
Proof.
  induction 2.
    inversion H.
    left. apply Rep_elem in H0.
      assumption.
      apply le_S_n. assumption.
    right. apply IHRep, H.
Qed.
(* end hide *)

Lemma Rep_le :
  forall (A : Type) (x : A) (n m : nat) (l : list A),
    n <= m -> Rep x m l -> Rep x n l.
(* begin hide *)
Proof.
  intros A x n m l H HR. generalize dependent n.
  induction HR; intros.
    destruct n as [| n'].
      constructor.
      inversion H.
    destruct n0 as [| n0'].
      constructor.
      constructor. apply IHHR. apply le_S_n. assumption.
    constructor. apply IHHR. assumption.
Qed.
(* end hide *)

Lemma Rep_S_inv :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x (S n) l -> Rep x n l.
(* begin hide *)
Proof.
  intros. apply Rep_le with (S n).
    apply le_S, le_n.
    assumption.
Qed.
(* end hide *)

Lemma Rep_length :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x n l -> n <= length l.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Nat.le_0_l.
    apply le_n_S. assumption.
    apply Nat.le_trans with (length l).
      assumption.
      apply le_S, le_n.
Qed.
(* end hide *)

Lemma Rep_S_snoc :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x n l -> Rep x (S n) (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn.
      repeat constructor.
      constructor. assumption.
    1-2: constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_snoc :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n l -> Rep x n (snoc y l).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_app_l :
  forall (A : Type) (x : A) (n : nat) (l1 l2 : list A),
    Rep x n l1 -> Rep x n (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_app_r :
  forall (A : Type) (x : A) (n : nat) (l1 l2 : list A),
    Rep x n l2 -> Rep x n (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    constructor. apply IHt1, H.
Qed.
(* end hide *)

Lemma Rep_app :
  forall (A : Type) (x : A) (n1 n2 : nat) (l1 l2 : list A),
    Rep x n1 l1 -> Rep x n2 l2 -> Rep x (n1 + n2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    apply Rep_app_r. assumption.
    constructor. apply IHRep, H0.
    constructor. apply IHRep, H0.
Qed.
(* end hide *)

Lemma Rep_app_conv :
  forall (A : Type) (x : A) (n : nat) (l1 l2 : list A),
    Rep x n (l1 ++ l2) <->
      exists n1 n2 : nat,
        Rep x n1 l1 /\ Rep x n2 l2 /\ n = n1 + n2.
(* begin hide *)
Proof.
  split.
    generalize dependent n. induction l1 as [| h1 t1]; cbn; intros.
      exists 0, n. repeat split; [constructor | assumption].
      inversion H; subst; clear H.
        exists 0, 0. repeat split; constructor.
        destruct (IHt1 _ H2) as (n1 & n2 & Hn1 & Hn2 & Heq).
          exists (S n1), n2. repeat split.
            constructor. assumption.
            assumption.
            rewrite Heq. cbn. reflexivity.
        destruct (IHt1 _ H2) as (n1 & n2 & Hn1 & Hn2 & Heq).
          exists n1, n2. repeat constructor; assumption.
    destruct 1 as (n1 & n2 & H1 & H2 & H3).
      rewrite H3. apply Rep_app; assumption.
Qed.
(* end hide *)

Lemma Rep_rev :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x n (rev l) <-> Rep x n l.
(* begin hide *)
Proof.
  assert (forall (A : Type) (x : A) (n : nat) (l : list A),
            Rep x n l -> Rep x n (rev l)).
    induction 1; cbn.
      constructor.
      apply Rep_S_snoc. assumption.
      apply Rep_snoc. assumption.
    split; intros.
      rewrite <- rev_rev. apply H, H0.
      apply H, H0.
Qed.
(* end hide *)

Lemma Rep_map :
  forall (A B : Type) (f : A -> B) (x : A) (n : nat) (l : list A),
    Rep x n l -> Rep (f x) n (map f l).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_map_conv :
  forall (A B : Type) (f : A -> B) (x : A) (n : nat) (l : list A),
    (forall x y : A, f x = f y -> x = y) ->
      Rep (f x) n (map f l) -> Rep x n l.
(* begin hide *)
Proof.
  intros A B f x n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    inversion H0; subst. constructor.
    destruct n as [| n'].
      constructor.
      inversion H0; subst; clear H0.
        rewrite (H _ _ H2) in *. constructor. apply IHt; assumption.
        constructor. apply IHt, H3. assumption.
Qed.
(* end hide *)

Lemma Rep_replicate :
  forall (A : Type) (x : A) (n : nat),
    Rep x n (replicate n x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_replicate_general :
  forall (A : Type) (x : A) (n m : nat),
    n <= m -> Rep x n (replicate m x).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Rep_replicate.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Rep_take :
  forall (A : Type) (x : A) (l : list A) (n m : nat),
    Rep x n (take m l) -> Rep x n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      constructor.
      destruct m as [| m']; inversion H; subst; clear H.
        constructor. apply (IHt _ _ H2).
        apply Rep_cons_2. apply (IHt _ _ H2).
Qed.
(* end hide *)

Lemma Rep_drop :
  forall (A : Type) (x : A) (l : list A) (n m : nat),
    Rep x n (drop m l) -> Rep x n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      constructor.
      destruct m as [| m'].
        assumption.
        apply Rep_cons_2, (IHt _ _ H).
Qed.
(* end hide *)

Lemma Rep_filter :
  forall (A : Type) (p : A -> bool) (x : A) (n : nat) (l : list A),
    Rep x n (filter p l) -> Rep x n l.
(* begin hide *)
Proof.
  intros A p x n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    assumption.
    case_eq (p h); intros; rewrite H0 in *.
      inversion H; subst; clear H; constructor; apply IHt, H3.
      constructor. apply IHt, H.
Qed.
(* end hide *)

Lemma Rep_filter_true :
  forall (A : Type) (p : A -> bool) (x : A) (n : nat) (l : list A),
    p x = true -> Rep x n l -> Rep x n (filter p l).
(* begin hide *)
Proof.
  induction 2; cbn.
    constructor.
    rewrite H. constructor. assumption.
    destruct (p y); try constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_filter_false :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A) (n : nat),
    p x = false -> Rep x n (filter p l) -> n = 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0. reflexivity.
    case_eq (p h); intros; rewrite H1 in *.
      inversion H0; subst; clear H0.
        reflexivity.
        congruence.
        apply IHt, H4. assumption.
      apply IHt, H0. assumption.
Qed.
(* end hide *)

Lemma Rep_takeWhile :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A) (n : nat),
    Rep x n (takeWhile p l) -> Rep x n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h); inversion H; subst; clear H; constructor; apply IHt, H2.
Qed.
(* end hide *)

Lemma Rep_dropWhile :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A) (n : nat),
    Rep x n (dropWhile p l) -> Rep x n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      constructor; apply IHt, H.
      inversion H; subst; clear H; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_zip :
  forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B) (n : nat),
    Rep (a, b) n (zip la lb) -> Rep a n la /\ Rep b n lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H; subst; clear H. split; constructor.
    destruct lb as [| hb tb]; inversion H; subst; clear H;
      try destruct (IHta _ _ H2); split; constructor; assumption.
Qed.
(* end hide *)

#[global] Hint Constructors Rep : core.

Lemma Rep_intersperse :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n (intersperse y l) <->
    Rep x n l \/ x = y /\ Rep x (S n - length l) l.
(* begin hide *)
Proof.
  split; revert n.
    induction l as [| h t]; cbn; intros.
      inversion H; subst. left. constructor.
      destruct (intersperse y t) eqn: Heq.
        inv H.
          left. constructor.
          inv H2. left. do 2 constructor.
          inv H2. left. constructor.
        inv H.
          left. constructor.
          inv H2.
Admitted.
(* end hide *)

(** ** [Exists] *)

(** Zaimplementuj induktywny predykat [Exists]. [Exists P l] zachodzi, gdy
    lista [l] zawiera taki element, który spełnia predykat [P]. *)

(* begin hide *)
Inductive Exists {A : Type} (P : A -> Prop) : list A -> Prop :=
| Exists_head :
    forall (h : A) (t : list A), P h -> Exists P (h :: t)
| Exists_tail :
    forall (h : A) (t : list A), Exists P t -> Exists P (h :: t).
(* end hide *)

Lemma Exists_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l <-> exists x : A, elem x l /\ P x.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists h. split; [constructor | assumption].
      destruct IHExists as [x [H1 H2]].
        exists x. split; try right; assumption.
    destruct 1 as [x [H1 H2]]. induction H1.
      left. assumption.
      right. apply IHelem; assumption.
Qed.
(* end hide *)

Lemma elem_Exists :
  forall {A : Type} {x : A} {l : list A},
    elem x l <-> Exists (fun y => x = y) l.
(* begin hide *)
Proof.
  split; induction 1; subst; constructor; auto; fail.
Qed.
(* end hide *)

Lemma Exists_nil :
  forall (A : Type) (P : A -> Prop),
    Exists P [] <-> False.
(* begin hide *)
Proof.
  split; inversion 1.
Qed.
(* end hide *)

Lemma Exists_cons :
  forall (A : Type) (P : A -> Prop) (h : A) (t : list A),
    Exists P (h :: t) <-> P h \/ Exists P t.
(* begin hide *)
Proof.
  split.
    inversion 1; subst; [left | right]; assumption.
    destruct 1; [left | right]; assumption.
Qed.
(* end hide *)

Lemma Exists_length :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l -> 1 <= length l.
(* begin hide *)
Proof.
  induction 1; cbn; apply le_n_S, Nat.le_0_l.
Qed.
(* end hide *)

Lemma Exists_snoc :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Exists P (snoc x l) <-> Exists P l \/ P x.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H; subst; clear H; [right | left]; assumption.
      inversion H; subst; clear H.
        do 2 left. assumption.
        destruct (IHt H1).
          left. right. assumption.
          right. assumption.
    destruct 1.
      induction H; cbn; [left | right]; assumption.
      induction l as [| h t]; cbn; [left | right]; assumption.
Qed.
(* end hide *)

Lemma Exists_app :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Exists P (l1 ++ l2) <-> Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  split.
    induction l1 as [| h1 t1]; cbn; intros.
      right. assumption.
      inversion H; subst; clear H.
        do 2 left. assumption.
        destruct (IHt1 H1).
          left; right. assumption.
          right. assumption.
    destruct 1.
      induction H; cbn.
        left. assumption.
        right. assumption.
      induction l1 as [| h t]; cbn.
        assumption.
        right. assumption.
Qed.
(* end hide *)

Lemma Exists_rev :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P (rev l) <-> Exists P l.
(* begin hide *)
Proof.
  intros A P. assert (forall l : list A, Exists P l -> Exists P (rev l)).
    induction 1; cbn; rewrite Exists_snoc.
      right. assumption.
      left. assumption.
    split; intro.
      rewrite <- rev_rev. apply H, H0.
      apply H, H0.
Qed.
(* end hide *)

Lemma Exists_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    Exists P (map f l) -> Exists (fun x : A => P (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  inversion H; subst; clear H.
    left. assumption.
    right. apply IHt, H1.
Qed.
(* end hide *)

Lemma Exists_join :
  forall (A : Type) (P : A -> Prop) (ll : list (list A)),
    Exists P (join ll) <->
    Exists (fun l : list A => Exists  P l) ll.
(* begin hide *)
Proof.
  split.
    induction ll as [| h t]; cbn; intros.
      inversion H.
      rewrite Exists_app in H. destruct H.
        left. assumption.
        right. apply IHt, H.
    induction ll as [| h t]; cbn; intros;
    inversion H; subst; clear H.
      rewrite Exists_app. left. assumption.
      rewrite Exists_app. right. apply IHt, H1.
Qed.
(* end hide *)

Lemma Exists_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    Exists P (replicate n x) <-> 1 <= n /\ P x.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; intros;
    inversion H; subst; clear H.
      split.
        apply le_n_S, Nat.le_0_l.
        assumption.
      destruct (IHn' H1). split.
        apply Nat.le_trans with n'.
          assumption.
          apply le_S, le_n.
        assumption.
    destruct 1, n as [| n']; cbn.
      inversion H.
      left. assumption.
Qed.
(* end hide *)

Lemma Exists_nth :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l <->
    exists (n : nat) (x : A), nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists 0, h. split; trivial.
      destruct IHExists as (n & x & H1 & H2).
        exists (S n), x. split; assumption.
    destruct 1 as (n & x & H1 & H2).
      pose (nth_spec A l n). rewrite H1 in y.
        rewrite y, Exists_app, Exists_cons. right. left. assumption.
Qed.
(* end hide *)

Lemma Exists_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P l ->
    match remove n l with
    | None => True
    | Some (x, l') => ~ P x -> Exists P l'
    end.
(* begin hide *)
Proof.
  intros; revert n.
  induction H; cbn; intros.
    destruct n as [| n'].
      intro. contradiction.
      destruct (remove n' t).
        destruct p. intro. left. assumption.
        trivial.
    destruct n as [| n'].
      intro. assumption.
      specialize (IHExists n'). destruct (remove n' t).
        destruct p. intro. right. apply IHExists. assumption.
        assumption.
Qed.
(* end hide *)

Lemma Exists_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P (take n l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn; inversion H; subst; clear H.
      left. assumption.
      right. apply (IHt _ H1).
Qed.
(* end hide *)

Lemma Exists_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P (drop n l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      right. apply (IHt _ H).
Qed.
(* end hide *)

Lemma Exists_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P l -> Exists P (take n l) \/ Exists P (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. assumption.
    destruct n as [| n']; cbn.
      right. assumption.
      inversion H; subst; clear H.
        do 2 left. assumption.
        destruct (IHt n' H1).
          left. right. assumption.
          right. assumption.
Qed.
(* end hide *)

Lemma Exists_cycle :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exists P (cycle n l) <-> Exists P l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn', Exists_snoc, !Exists_cons. firstorder.
Qed.
(* end hide *)

Lemma Exists_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      Exists P l <-> P x \/ Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  split.
    intro. revert l1 l2 n x H. induction H0; cbn; intros.
      destruct n as [| n'].
        inv H0. left. assumption.
        destruct (splitAt n' t).
          destruct p, p. inv H0. right. do 2 left. assumption.
          inv H0.
      destruct n as [| n'].
        inv H. do 2 right. assumption.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. inv H. decompose [or] (IHExists _ _ _ _ Heq).
            left. assumption.
            right. left. right. assumption.
            do 2 right. assumption.
          inv H.
    revert l1 l2 n x H. induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. decompose [or] H0; clear H0.
          left. assumption.
          inv H1.
          right. assumption.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. inv H. specialize (IHt _ _ _ x Heq).
            decompose [or] H0; clear H0.
              right. apply IHt. left. assumption.
              inv H1.
                left. assumption.
                right. apply IHt. right. left. assumption.
              right. apply IHt. do 2 right. assumption.
              inv H.
Restart.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  rewrite Exists_app, Exists_cons. firstorder.
Qed.
(* end hide *)

Lemma Exists_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat) (x : A),
    Exists P (insert l n x) <-> P x \/ Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite Exists_cons, Exists_nil. reflexivity.
    destruct n as [| n'].
      rewrite !Exists_cons. reflexivity.
      rewrite !Exists_cons, IHt. firstorder.
Qed.
(* end hide *)

Lemma Exists_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Exists P l' <->
      Exists P (take n l) \/ P x \/ Exists P (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. rewrite Exists_nil, Exists_cons, drop_0. firstorder.
      destruct (replace t n' x) eqn: Heq; inv H.
        rewrite ?Exists_cons, (IHt _ _ _ Heq), or_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Exists_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P (filter p l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h).
      inversion H; subst; clear H.
        left. assumption.
        right. apply IHt, H1.
      right. apply IHt, H.
Qed.
(* end hide *)

Lemma Exists_filter_conv :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P l ->
      Exists P (filter p l) \/
      Exists P (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction 1; cbn.
    destruct (p h); cbn.
      do 2 left. assumption.
      right; left. assumption.
    destruct (p h), IHExists as [IH | IH]; cbn.
      left; right. assumption.
      right. assumption.
      left. assumption.
      right; right. assumption.
Qed.
(* end hide *)

Lemma Exists_filter_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ Exists P (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    inversion H0.
    case_eq (p h); intros; rewrite H1 in *.
      inversion H0; subst; clear H0.
        rewrite H, H1 in H3. congruence.
        apply IHt; assumption.
      apply IHt; assumption.
Qed.
(* end hide *)

Lemma Exists_partition :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      Exists P l <-> Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H.
  inversion H; subst; clear H. split; intro.
    apply Exists_filter_conv. assumption.
    destruct H; apply Exists_filter in H; assumption.
Qed.
(* end hide *)

Lemma Exists_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P (takeWhile p l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  try destruct (p h); inversion H; subst; clear H.
    left. assumption.
    right. apply IHt, H1.
Qed.
(* end hide *)

Lemma Exists_takeWhile_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ Exists P (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    inversion H0.
    case_eq (p h); intros; rewrite H1 in *; inversion H0; subst; clear H0.
        rewrite H, H1 in H3. congruence.
        apply IHt; assumption.
Qed.
(* end hide *)

Lemma Exists_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P (dropWhile p l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      right. apply IHt, H.
      assumption.
Qed.
(* end hide *)

Lemma Exists_takeWhile_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P l -> Exists P (takeWhile p l) \/ Exists P (dropWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    destruct (p h).
      do 2 left. assumption.
      right; left. assumption.
    destruct (p h), IHExists.
      left; right. assumption.
      right. assumption.
      apply Exists_takeWhile in H0. right; right. assumption.
      apply Exists_dropWhile in H0. right; right. assumption.
Qed.
(* end hide *)

Lemma Exists_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        Exists P l <-> Exists P b \/ P x \/ Exists P e.
(* begin hide *)
Proof.
  intros. apply span_spec in H0.
  rewrite H0, Exists_app, Exists_cons.
  reflexivity.
Qed.
(* end hide *)

Lemma Exists_interesting :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (hb : B) (tb : list B),
    Exists (fun a : A => Exists (fun b : B => P (a, b)) tb) la ->
    Exists (fun a : A => Exists (fun b : B => P (a, b)) (hb :: tb)) la.
(* begin hide *)
Proof.
  induction 1.
    left. right. assumption.
    right. assumption.
Qed.
(* end hide *)

Lemma Exists_zip :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (lb : list B),
    Exists P (zip la lb) ->
      Exists (fun a : A => Exists (fun b : B => P (a, b)) lb) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H.
    induction lb as [| hb tb]; inversion H; subst; clear H.
      left. left. assumption.
      specialize (IHta _ H1). apply Exists_interesting. right. assumption.
Qed.
(* end hide *)

Lemma Exists_pmap :
  forall (A B : Type) (f : A -> option B) (P : B -> Prop) (l : list A),
    Exists P (pmap f l) <->
      Exists (fun x : A => match f x with | Some b => P b | _ => False end) l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (f h) eqn: Hfh.
        inversion H; subst.
          left. rewrite Hfh. assumption.
          right. apply IHt. assumption.
        right. apply IHt. assumption.
    induction l as [| h t]; cbn; inversion 1; subst; clear H.
      destruct (f h).
        left. assumption.
        contradiction.
      destruct (f h); try right; apply IHt, H1.
Restart.
  induction l as [| h t]; cbn; intros.
    rewrite ?Exists_nil. reflexivity.
    destruct (f h) eqn: H; cbn.
      rewrite ?Exists_cons, IHt, H. reflexivity.
      rewrite ?Exists_cons, IHt, H. tauto.
Qed.
(* end hide *)

Lemma Exists_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Exists P (intersperse x l) <->
    Exists P l \/ (P x /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (intersperse x t) eqn: Heq.
        inv H.
          do 2 left. assumption.
          inv H1.
        inv H.
          do 2 left. assumption.
          inv H1.
            right. split; try assumption. destruct t; cbn in *.
              inv Heq.
              apply le_n_S, le_n_S, Nat.le_0_l.
            destruct (IHt H0).
              left. right. assumption.
              right. destruct H. split.
                assumption.
                destruct t; cbn in *.
                  inv H1.
                  apply le_n_S, le_n_S, Nat.le_0_l.
    destruct 1.
      induction H; cbn.
        destruct (intersperse x t); left; assumption.
        destruct (intersperse x t).
          inv IHExists.
          do 2 right. assumption.
      destruct H. destruct l as [| h [| h' t]]; cbn.
        inv H0.
        inv H0. inv H2.
        destruct (intersperse x t); cbn.
          right. left. assumption.
          right. left. assumption.
Qed.
(* end hide *)

Lemma Exists_interleave :
  forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Exists P (interleave l1 l2) <->
    Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  split; revert l2.
    induction l1 as [| h1 t1]; cbn.
      right. assumption.
      destruct l2 as [| h2 t2]; cbn; intro.
        left. assumption.
        inv H.
          left. constructor. assumption.
          inv H1.
            right. constructor. assumption.
            destruct (IHt1 _ H0).
              left. right. assumption.
              right. right. assumption.
    induction l1 as [| h1 t1]; cbn.
      destruct 1.
        inv H.
        assumption.
      destruct l2 as [| h2 t2]; cbn; intros [].
        assumption.
        inv H.
        inv H.
          left. assumption.
          right. right. apply IHt1. left. assumption.
        inv H.
          right. left. assumption.
          right. right. apply IHt1. right. assumption.
Qed.
(* end hide *)

Lemma Exists_insert_before_in :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A) (n : nat),
    Exists P (insertBefore.insertBefore n l1 l2) <->
    Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insertBefore.insert_before_in_nil. firstorder. inversion H.
    destruct n as [| n']; cbn.
      rewrite Exists_app; cbn. firstorder congruence.
      rewrite ?Exists_cons, IHt. firstorder congruence.
Qed.
(* end hide *)

(** ** [Forall] *)

(** Zaimplementuj induktywny predykat [Forall]. [Forall P l] jest
    spełniony, gdy każdy element listy [l] spełnia predykat [P]. *)

(* begin hide *)
Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
| Forall_nil' : Forall P []
| Forall_cons' :
    forall (h : A) (t : list A), P h -> Forall P t -> Forall P (h :: t).
(* end hide *)

Lemma Forall_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P l <-> forall x : A, elem x l -> P x.
(* begin hide *)
Proof.
  split.
    induction 1; intros.
      inv H.
      inv H1.
        assumption.
        apply IHForall. assumption.
    induction l as [| h t]; constructor.
      apply H. left.
      apply IHt. intros. apply H. right. assumption.
Qed.
(* end hide *)

Lemma Forall_nil :
  forall (A : Type) (P : A -> Prop),
    Forall P [] <-> True.
(* begin hide *)
Proof.
  split; constructor.
Qed.
(* end hide *)

Lemma Forall_cons :
  forall (A : Type) (P : A -> Prop) (h : A) (t : list A),
    Forall P (h :: t) <-> P h /\ Forall P t.
(* begin hide *)
Proof.
  split; inversion 1; constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_snoc :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Forall P (snoc x l) <-> Forall P l /\ P x.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H; subst; clear H. split; assumption.
      inversion H; subst; clear H. destruct (IHt H3). split.
        constructor. 1-3: assumption.
    destruct 1.
      induction H; cbn; repeat constructor; try assumption.
Qed.
(* end hide *)

Lemma Forall_app :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  split.
    induction l1 as [| h1 t1]; cbn; intros.
      split; [constructor | assumption].
      inversion H; subst; clear H. destruct (IHt1 H3). split.
        constructor; assumption.
        assumption.
    destruct 1. induction H; cbn; try constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_rev :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P (rev l) <-> Forall P l.
(* begin hide *)
Proof.
  intros A P. assert (forall l : list A, Forall P l -> Forall P (rev l)).
    induction 1; cbn.
      constructor.
      rewrite Forall_snoc. split; assumption.
    split; intro.
      rewrite <- rev_rev. apply H, H0.
      apply H, H0.
Qed.
(* end hide *)

Lemma Forall_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    Forall P (map f l) -> Forall (fun x : A => P (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    inversion H; subst; clear H. constructor.
      assumption.
      apply IHt, H3.
Qed.
(* end hide *)

Lemma Forall_join :
  forall (A : Type) (P : A -> Prop) (ll : list (list A)),
    Forall P (join ll) <-> Forall (fun l : list A => Forall P l) ll.
(* begin hide *)
Proof.
  split.
    induction ll as [| h t]; cbn; intros.
      constructor.
      rewrite Forall_app in H. destruct H. constructor.
        assumption.
        apply IHt, H0.
    induction ll as [| h t]; cbn; intros.
      constructor.
      inversion H; subst; clear H. apply Forall_app; auto.
Qed.
(* end hide *)

Lemma Forall_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    Forall P (replicate n x) <-> n = 0 \/ P x.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; intros.
      left. reflexivity.
      right. inversion H. assumption.
    destruct 1.
      subst. cbn. constructor.
      induction n as [| n']; cbn.
        constructor.
        constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_nth :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P l <-> forall n : nat, n < length l ->
      exists x : A, nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  split.
    induction 1; cbn; intros.
      inv H.
      destruct n as [| n']; cbn.
        exists h. split; trivial.
        apply IHForall. apply Nat.succ_lt_mono. assumption.
    induction l as [| h t]; cbn; intros.
      constructor.
      destruct (H 0 (Nat.lt_0_succ _)) as [x [H1 H2]]; cbn in *.
        inv H1. constructor.
          assumption.
          apply IHt. intros. apply (H (S n)). now apply Nat.succ_lt_mono in H0.
Qed.
(* end hide *)

Lemma Forall_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P l ->
    match remove n l with
    | None => True
    | Some (x, l') => Forall P l'
    end.
(* begin hide *)
Proof.
  intros. revert n.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n'].
      assumption.
      specialize (IHForall n'). destruct (remove n' t).
        destruct p. constructor; assumption.
        trivial.
Qed.
(* end hide *)

Lemma Forall_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P l -> Forall P (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      constructor.
      inversion H; subst; clear H. constructor.
        assumption.
        apply (IHt _ H3).
Qed.
(* end hide *)

Lemma Forall_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P l -> Forall P (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      inversion H; subst; clear H. apply (IHt _ H3).
Qed.
(* end hide *)

Lemma Forall_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P (take n l) -> Forall P (drop n l) -> Forall P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      inversion H; subst; clear H. constructor.
        assumption.
        apply (IHt _ H4 H0).
Qed.
(* end hide *)

Lemma Forall_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      Forall P l <-> P x /\ Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  rewrite Forall_app, Forall_cons. firstorder.
Qed.
(* end hide *)

Lemma Forall_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat) (x : A),
      Forall P (insert l n x) <-> P x /\ Forall P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite Forall_cons, Forall_nil. reflexivity.
    destruct n as [| n'].
      rewrite 2!Forall_cons. reflexivity.
      rewrite 2!Forall_cons, IHt. firstorder.
Qed.
(* end hide *)

Lemma Forall_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Forall P l' <->
      Forall P (take n l) /\ P x /\ Forall P (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. rewrite Forall_nil, Forall_cons, drop_0. firstorder.
      destruct (replace t n' x) eqn: Heq; inv H.
        rewrite ?Forall_cons, (IHt _ _ _ Heq), and_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Forall_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P l -> Forall P (filter p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h); try constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_filter_conv :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P (filter p l) ->
    Forall P (filter (fun x : A => negb (p x)) l) ->
      Forall P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h); cbn in *.
      inversion H; subst; clear H. constructor; auto.
      inversion H0; subst; clear H0. constructor; auto.
Qed.
(* end hide *)

Lemma Forall_filter_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) -> Forall P (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    case_eq (p h); intros.
      constructor.
        rewrite H. assumption.
        apply IHt. assumption.
      apply IHt. assumption.
Qed.
(* end hide *)

Lemma Forall_partition :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      Forall P l <-> Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H.
  inversion H; subst; clear H; split; intros.
    split; apply Forall_filter; assumption.
    destruct H. apply (Forall_filter_conv _ _ p); assumption.
Qed.
(* end hide *)

Lemma Forall_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P l -> Forall P (takeWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h); constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_takeWhile_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) -> Forall P (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    case_eq (p h); intros; constructor; firstorder.
Qed.
(* end hide *)

Lemma Forall_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P l -> Forall P (dropWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h); try constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_takeWhile_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P (takeWhile p l) -> Forall P (dropWhile p l) -> Forall P l.
(* begin hide *)
Proof.
  intros. rewrite <- (takeWhile_dropWhile_spec _ p), Forall_app.
  split; assumption.
Qed.
(* end hide *)

Lemma Forall_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        Forall P l <-> Forall P b /\ P x /\ Forall P e.
(* begin hide *)
Proof.
  intros. apply span_spec in H0.
  rewrite H0, Forall_app, Forall_cons.
  reflexivity.
Qed.
(* end hide *)

Lemma Forall_zip :
  forall (A B : Type) (PA : A -> Prop) (PB : B -> Prop)
  (la : list A) (lb : list B),
    Forall PA la -> Forall PB lb ->
      Forall (fun '(a, b) => PA a /\ PB b) (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    constructor.
    destruct lb as [| hb tb].
      constructor.
      inversion H; inversion H0; subst; clear H H0. constructor.
        split; assumption.
        apply IHta; assumption.
Qed.
(* end hide *)

Lemma Forall_pmap :
  forall (A B : Type) (f : A -> option B) (P : B -> Prop) (l : list A),
    Forall (fun x : A => match f x with | Some b => P b | _ => False end) l ->
      Forall P (pmap f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    inversion H; subst; clear H. destruct (f h).
      constructor; try apply IHt; assumption.
      apply IHt. assumption.
Qed.
(* end hide *)

Lemma Forall_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Forall P (intersperse x l) <->
    Forall P l /\ (2 <= length l -> P x).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      split; [constructor | inversion 1].
      destruct (intersperse x t) eqn: Heq.
        inv H. destruct (IHt H3). split.
          constructor; assumption.
          intro. apply H0. destruct t as [| h' [| h'' t']]; cbn in *.
            inv H1. inv H5.
            inv Heq.
            apply le_n_S, le_n_S, Nat.le_0_l.
        inv H. inv H3. destruct (IHt H4). split.
          constructor; assumption.
          intro. assumption.
    destruct 1. induction H; cbn in *.
      constructor.
      destruct (intersperse x t) eqn: Heq.
        repeat constructor; assumption.
        constructor; [assumption | constructor].
          apply H0. destruct t; cbn in *.
            inv Heq.
            apply le_n_S, le_n_S, Nat.le_0_l.
          apply IHForall. intro. apply H0. destruct t; cbn in *.
            inv Heq.
            lia.
Qed.
(* end hide *)

Lemma Forall_interleave :
  forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Forall P (interleave l1 l2) <->
    Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  split; revert l2.
    induction l1 as [| h1 t1]; cbn.
      split; [constructor | assumption].
      destruct l2 as [| h2 t2]; cbn; intro.
        split; [assumption | constructor].
        inv H. inv H3. destruct (IHt1 _ H4).
          split; constructor; assumption.
    induction l1 as [| h1 t1]; cbn; intros l2 [].
      assumption.
      destruct l2 as [| h2 t2].
        assumption.
        inv H; inv H0. repeat constructor.
          1-2: assumption.
          apply IHt1. split; assumption.
Qed.
(* end hide *)

Lemma Forall_insert_before_in :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A) (n : nat),
    Forall P (insertBefore.insertBefore n l1 l2) <->
    Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insertBefore.insert_before_in_nil. firstorder. constructor.
    destruct n as [| n']; cbn.
      rewrite Forall_app, Forall_cons. firstorder congruence.
      rewrite ?Forall_cons, IHt. firstorder congruence.
Qed.
(* end hide *)

Lemma Forall_impl :
  forall (A : Type) (P Q : A -> Prop) (l : list A),
    (forall x : A , P x -> Q x) ->
      Forall P l -> Forall Q l.
(* begin hide *)
Proof.
  induction 2; cbn; constructor.
    apply H. assumption.
    apply IHForall.
Qed.
(* end hide *)

Lemma Forall_Exists :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P l -> ~ Exists (fun x : A => ~ P x) l.
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    inversion H.
    inversion H1; contradiction.
Qed.
(* end hide *)

Lemma Exists_Forall :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l -> ~ Forall (fun x : A => ~ P x) l.
(* begin hide *)
Proof.
  induction 1; cbn; intro;
  rewrite Forall_cons in H0; destruct H0; contradiction.
Qed.
(* end hide *)

(** ** [AtLeast] *)

(** Czas uogólnić relację [Rep] oraz predykaty [Exists] i [Forall]. Zdefiniuj
    w tym celu relację [AtLeast]. Zdanie [AtLeast P n l] zachodzi, gdy na
    liście [l] jest co najmniej [n] elementów spełniających predykat [P]. *)

(* begin hide *)
Inductive AtLeast {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
| AL_0 :
    forall l : list A, AtLeast P 0 l
| AL_S :
    forall (n : nat) (h : A) (t : list A),
      P h -> AtLeast P n t -> AtLeast P (S n) (h :: t)
| AL_skip :
    forall (n : nat) (h : A) (t : list A),
      AtLeast P n t -> AtLeast P n (h :: t).
(* begin hide *)

Lemma AtLeast_le :
  forall (A : Type) (P : A -> Prop) (n m : nat) (l : list A),
    AtLeast P n l -> m <= n -> AtLeast P m l.
(* begin hide *)
Proof.
  intros A P n m l H. generalize dependent m.
  induction H; intros.
    inversion H. constructor.
    destruct m as [| m'].
      constructor.
      constructor.
        assumption.
        apply IHAtLeast, le_S_n, H1.
      constructor. apply IHAtLeast, H0.
Qed.
(* end hide *)

Lemma AtLeast_cons :
  forall (A : Type) (P : A -> Prop) (n : nat) (h : A) (t : list A),
    AtLeast P n (h :: t) <->
    AtLeast P n t \/ P h /\ AtLeast P (n - 1) t.
(* begin hide *)
Proof.
  split; intros.
    inv H.
      left. constructor.
      right. cbn. rewrite Nat.sub_0_r. split; assumption.
      left. assumption.
    decompose [and or] H; clear H.
      constructor. assumption.
      destruct n as [| n'].
        constructor.
        cbn in H2. rewrite Nat.sub_0_r in H2. constructor; assumption.
Qed.
(* end hide *)

Lemma AtLeast_cons' :
  forall (A : Type) (P : A -> Prop) (n : nat) (h : A) (t : list A),
    AtLeast P (S n) (h :: t) -> AtLeast P n t.
(* begin hide *)
Proof.
  intros. inv H.
    assumption.
    apply AtLeast_le with (S n).
      assumption.
      apply le_S, le_n.
Qed.
(* end hide *)

Lemma AtLeast_length :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    AtLeast P n l -> n <= length l.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Nat.le_0_l.
    apply le_n_S, IHAtLeast.
    apply Nat.le_trans with (length t).
      assumption.
      apply le_S, le_n.
Qed.
(* end hide *)

Lemma AtLeast_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtLeast P n l -> AtLeast P n (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma AtLeast_S_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtLeast P n l -> P x -> AtLeast P (S n) (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    induction l as [| h t]; cbn.
      repeat constructor; assumption.
      apply AL_skip. assumption.
    constructor.
      assumption.
      apply IHAtLeast, H1.
    apply AL_skip, IHAtLeast, H0.
Qed.
(* end hide *)

Lemma AtLeast_Exists :
  forall (A : Type) (P : A -> Prop) (l : list A),
    AtLeast P 1 l <-> Exists P l.
(* begin hide *)
Proof.
  split.
    remember 1 as n. induction 1; inversion Heqn; subst.
      left. assumption.
      right. apply IHAtLeast. reflexivity.
    induction 1.
      constructor.
        assumption.
        constructor.
      constructor 3. assumption.
Qed.
(* end hide *)

Lemma AtLeast_Forall :
  forall (A : Type) (P : A -> Prop) (l : list A),
    AtLeast P (length l) l <-> Forall P l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      constructor.
      inversion H; subst; clear H.
        constructor; auto.
        apply AtLeast_length in H2. lia.
    induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma AtLeast_Rep :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    AtLeast (fun y : A => x = y) n l <-> Rep x n l.
(* begin hide *)
Proof.
  split; induction 1; subst; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_app_l :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n l1 -> AtLeast P n (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_app_r :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n l2 -> AtLeast P n (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_plus_app :
  forall (A : Type) (P : A -> Prop) (n1 n2 : nat) (l1 l2 : list A),
    AtLeast P n1 l1 -> AtLeast P n2 l2 ->
      AtLeast P (n1 + n2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    apply AtLeast_app_r. assumption.
    1-2: constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_app_conv :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n (l1 ++ l2) ->
      exists n1 n2 : nat, AtLeast P n1 l1 /\ AtLeast P n2 l2 /\ n = n1 + n2.
(* begin hide *)
Proof.
  intros A P n l1. generalize dependent n.
  induction l1 as [| h t]; cbn; intros.
    exists 0, n. repeat split.
      constructor.
      assumption.
    inversion H; subst; clear H.
      exists 0, 0. repeat constructor.
      destruct (IHt _ _ H4) as (n1 & n2 & Hn1 & Hn2 & Heq).
        exists (S n1), n2. subst. cbn. repeat constructor; auto.
      destruct (IHt _ _ H2) as (n1 & n2 & Hn1 & Hn2 & Heq).
        exists n1, n2. subst. repeat constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_app :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n (l1 ++ l2) <->
    exists n1 n2 : nat,
      AtLeast P n1 l1 /\ AtLeast P n2 l2 /\ n = n1 + n2.
(* begin hide *)
Proof.
  split.
    apply AtLeast_app_conv.
    destruct 1 as (n1 & n2 & H1 & H2 & H3); subst.
      apply AtLeast_plus_app; assumption.
Qed.
(* end hide *)

Lemma AtLeast_app_comm :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n (l1 ++ l2) -> AtLeast P n (l2 ++ l1).
(* begin hide *)
Proof.
  intros. apply AtLeast_app_conv in H.
  destruct H as (n1 & n2 & H1 & H2 & H3); subst.
  rewrite Nat.add_comm. apply AtLeast_plus_app; assumption.
Qed.
(* end hide *)

Lemma AtLeast_rev :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    AtLeast P n (rev l) <-> AtLeast P n l.
(* begin hide *)
Proof.
  assert (forall (A : Type) P n (l : list A),
            AtLeast P n l -> AtLeast P n (rev l)).
    induction 1; cbn.
      constructor.
      apply AtLeast_S_snoc; assumption.
      apply AtLeast_snoc; assumption.
    split; intro.
      rewrite <- rev_rev. apply H, H0.
      apply H, H0.
Qed.
(* end hide *)

Lemma AtLeast_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (n : nat) (l : list A),
    AtLeast (fun x : A => P (f x)) n l ->
      AtLeast P n (map f l).
(* begin hide *)
Proof.
  induction 1; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_map_conv :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (n : nat) (l : list A),
    (forall x y : A, f x = f y -> x = y) -> AtLeast P n (map f l) ->
      AtLeast (fun x : A => P (f x)) n l.
(* begin hide *)
Proof.
  intros A B P f n l. generalize dependent n.
  induction l as [| h t]; cbn; intros;
  inversion H0; subst; clear H0; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    n <> 0 -> P x -> AtLeast P n (replicate n x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    contradiction H. reflexivity.
    destruct n' as [| n'']; cbn in *.
      constructor; [assumption | constructor].
    constructor.
      assumption.
      apply IHn'; [inversion 1 | assumption].
Qed.
(* end hide *)

Lemma AtLeast_replicate_conv :
  forall (A : Type) (P : A -> Prop) (n m : nat) (x : A),
    AtLeast P m (replicate n x) -> m = 0 \/ m <= n /\ P x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros;
  inversion H; subst; clear H.
    1-2: left; reflexivity.
    destruct (IHn' _ _ H4) as [H | [H1 H2]]; subst; right.
      split; [apply le_n_S, Nat.le_0_l | assumption].
      split; [apply le_n_S, H1 | assumption].
    destruct (IHn' _ _ H2) as [H | [H1' H2']]; subst.
      left. reflexivity.
      right. split; try apply le_S; assumption.
Qed.
(* end hide *)

Lemma AtLeast_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (m : nat),
    AtLeast P m l -> forall n : nat,
      match remove n l with
      | None => True
      | Some (_, l') => AtLeast P (m - 1) l'
      end.
(* begin hide *)
Proof.
  induction 1; cbn; intro m.
    destruct (remove m l).
      destruct p. 1-2: constructor.
    destruct m as [| m']; cbn in *.
      rewrite Nat.sub_0_r. assumption.
      specialize (IHAtLeast m'). destruct (remove m' t).
        destruct p. destruct n as [| n']; cbn in *.
          constructor.
          rewrite Nat.sub_0_r in *. constructor; assumption.
        trivial.
    destruct m as [| m']; cbn in *.
      apply AtLeast_le with n.
        assumption.
        destruct n as [| n']; cbn.
          apply le_n.
          rewrite Nat.sub_0_r. apply le_S, le_n.
      specialize (IHAtLeast m'). destruct (remove m' t).
        destruct p. constructor. assumption.
        trivial.
Qed.
(* end hide *)

Lemma AtLeast_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m : nat),
    AtLeast P m (take n l) -> AtLeast P m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn; inversion H; subst; clear H.
      1-3: constructor.
        assumption.
        apply (IHt _ _ H4).
      constructor. apply (IHt _ _ H2).
Qed.
(* end hide *)

Lemma AtLeast_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m : nat),
    AtLeast P m (drop n l) -> AtLeast P m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      constructor. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma AtLeast_take_drop :
  forall (A : Type) (P : A -> Prop) (n m : nat) (l : list A),
    AtLeast P n l ->
    exists n1 n2 : nat,
      AtLeast P n1 (take m l) /\ AtLeast P n2 (drop m l) /\ n = n1 + n2.
(* begin hide *)
Proof.
  intros. apply AtLeast_app. rewrite app_take_drop. assumption.
Qed.
(* end hide *)

Lemma AtLeast_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      forall m : nat,
        AtLeast P m l ->
        exists m1 mx m2 : nat,
          AtLeast P m1 l1 /\ AtLeast P mx [x] /\ AtLeast P m2 l2 /\
          m1 + mx + m2 = m.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. inv H0.
        exists 0, 0, 0. repeat constructor.
        exists 0, 1, n. repeat constructor; assumption.
        exists 0, 0, m. repeat constructor. assumption.
    destruct (splitAt n' t) eqn: Heq.
      destruct p, p. inv H. inv H0.
        exists 0, 0, 0. repeat constructor.
        destruct (IHt _ _ _ _ Heq _ H4) as
                 (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4).
          exists (S m1), mx, m2. subst. firstorder. constructor; assumption.
        destruct (IHt _ _ _ _ Heq _ H2) as
                 (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4).
          exists m1, mx, m2. subst. firstorder. apply AL_skip. assumption.
      inv H.
Qed.
(* end hide *)

Lemma AtLeast_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    AtLeast P n l -> forall (m : nat) (x : A),
      AtLeast P n (insert l m x).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    destruct m as [| m']; cbn.
      apply AL_skip. constructor; assumption.
      constructor.
        assumption.
        apply IHAtLeast.
    destruct m as [| m']; cbn.
      do 2 apply AL_skip. assumption.
      apply AL_skip. apply IHAtLeast.
Qed.
(* end hide *)

Lemma AtLeast_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' -> AtLeast P m l ->
      AtLeast P (m - 1) l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. inv H0; cbn.
        constructor.
        rewrite Nat.sub_0_r. constructor. assumption.
        apply AtLeast_le with m.
          constructor. assumption.
          lia.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0; cbn.
        constructor.
        rewrite Nat.sub_0_r. specialize (IHt _ _ _ _ Heq H4).
          destruct n; cbn in *.
            constructor.
            rewrite Nat.sub_0_r in IHt. constructor; assumption.
        specialize (IHt _ _ _ _ Heq H2). constructor. assumption.
Qed.
(* end hide *)

Lemma AtLeast_replace' :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' -> AtLeast P m l -> P x ->
      AtLeast P m l'.
(* begin hide *)
Proof.
  intros until 2. revert l' n x H.
  induction H0; cbn; intros.
    constructor.
    destruct n0; cbn in *.
      inv H1. constructor; assumption.
      destruct (replace t n0 x) eqn: Heq; inv H1. constructor.
        assumption.
        apply (IHAtLeast _ _ _ Heq H2).
    destruct n0; cbn in H.
      inv H. constructor. assumption.
      destruct (replace t n0 x) eqn: Heq; inv H.
        constructor. apply (IHAtLeast _ _ _ Heq H1).
Qed.
(* end hide *)

Lemma AtLeast_replace_conv :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' -> AtLeast P m l' -> AtLeast P (m - 1) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. inv H0; cbn.
        constructor.
        rewrite Nat.sub_0_r. constructor. assumption.
        apply AtLeast_le with m.
          constructor. assumption.
          lia.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0; cbn.
        constructor.
        rewrite Nat.sub_0_r. specialize (IHt _ _ _ _ Heq H4).
          destruct n; cbn in *.
            constructor.
            rewrite Nat.sub_0_r in IHt. constructor; assumption.
        specialize (IHt _ _ _ _ Heq H2). constructor. assumption.
Qed.
(* end hide *)

Lemma AtLeast_replace_conv' :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x y : A),
    replace l n x = Some l' -> nth n l = Some y -> P y ->
      AtLeast P m l' -> AtLeast P m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. inv H0. inv H2.
        constructor.
        constructor; assumption.
      constructor. assumption.
    destruct (replace t n' x) eqn: Heq; inv H. inv H2; constructor.
      assumption.
      apply (IHt _ _ _ _ _ Heq H0 H1 H6).
      apply (IHt _ _ _ _ _ Heq H0 H1 H4).
Qed.
(* end hide *)

(* begin hide *)
(* TODO: [Exactly], [AtMost] dla [replace] *)
(* end hide *)

Lemma AtLeast_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    AtLeast P n (filter p l) -> AtLeast P n l.
(* begin hide *)
Proof.
  intros A P p n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h) eqn: Hph.
      inversion H; subst; clear H; constructor; auto.
      constructor. apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_filter_compat_true :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) ->
      AtLeast P (length (filter p l)) (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h) eqn: Hph; cbn.
      constructor.
        rewrite H. assumption.
        apply IHt, H.
      apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_filter_compat_false :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    (forall x : A, P x <-> p x = false) ->
      AtLeast P n (filter p l) -> n = 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0. reflexivity.
    destruct (p h) eqn: Hph.
      inv H0.
        reflexivity.
        rewrite H in H4. congruence.
        apply (IHt H H3).
      apply (IHt H H0).
Qed.
(* end hide *)

Lemma AtLeast_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    AtLeast P n (takeWhile p l) -> AtLeast P n l.
(* begin hide *)
Proof.
  intros A P p n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h) eqn: Heq.
      inversion H; subst; clear H; constructor; auto.
      inversion H. constructor.
Qed.
(* end hide *)

Lemma AtLeast_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    AtLeast P n (dropWhile p l) -> AtLeast P n l.
(* begin hide *)
Proof.
  intros A P p n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h) eqn: Heq.
      constructor; auto.
      inversion H; subst; clear H; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_takeWhile_true :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) ->
      AtLeast P (length (takeWhile p l)) (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h) eqn: Heq; cbn.
      constructor; [rewrite H | apply IHt]; assumption.
      constructor.
Qed.
(* end hide *)

Lemma AtLeast_takeWhile_false :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    (forall x : A, P x <-> p x = false) ->
      AtLeast P n (takeWhile p l) -> n = 0.
(* begin hide *)
Proof.
  intros A P p n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    inversion H0. reflexivity.
    destruct (p h) eqn: Heq.
      inversion H0; subst; clear H0.
        reflexivity.
        rewrite H, Heq in H4. congruence.
        apply IHt; assumption.
      inversion H0. reflexivity.
Qed.
(* end hide *)

Lemma AtLeast_dropWhile_true :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A) (n : nat),
    (forall x : A, P x <-> p x = true) ->
      AtLeast P n l -> AtLeast P (n - length (takeWhile p l)) (dropWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0. cbn. constructor.
    destruct (p h) eqn: Heq; cbn.
      inversion H0; subst; clear H0.
        cbn. constructor.
        cbn. apply IHt; assumption.
        destruct n as [| n']; cbn.
          constructor.
          apply IHt.
            assumption.
            apply AtLeast_le with (S n').
              assumption.
              apply le_S, le_n.
      rewrite Nat.sub_0_r. assumption.
Qed.
(* end hide *)

Lemma AtLeast_dropWhile_false :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A) (n : nat),
    (forall x : A, P x <-> p x = false) ->
      AtLeast P n l -> AtLeast P n (dropWhile p l).
(* begin hide *)
Proof.
  induction 2; cbn.
    constructor.
    destruct (p h) eqn: Heq.
      rewrite H, Heq in H0. congruence.
      constructor; assumption.
    destruct (p h) eqn: Heq; try constructor; assumption.
Qed.
(* end hide *)

Lemma AtLeast_zip :
  forall (A B : Type) (PA : A -> Prop) (PB : B -> Prop)
  (la : list A) (lb : list B) (n : nat),
    AtLeast (fun '(a, b) => PA a /\ PB b) n (zip la lb) ->
      AtLeast PA n la /\ AtLeast PB n lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H. split; constructor.
    destruct lb as [| hb tb]; inversion H; subst; clear H.
      1-2: split; constructor.
      destruct H3. destruct (IHta _ _ H4). split; constructor; auto.
      destruct (IHta _ _ H2). split; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_findIndices :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A) (n : nat),
    (forall x : A, P x <-> p x = true) ->
      AtLeast P n l -> n <= length (findIndices p l).
(* begin hide *)
Proof.
  induction 2.
    apply Nat.le_0_l.
    cbn. destruct (H h). rewrite (H2 H0). cbn. apply le_n_S.
      rewrite length_map. assumption.
    cbn. destruct (p h); cbn; rewrite length_map.
      apply le_S. assumption.
      assumption.
Qed.
(* end hide *)

Lemma AtLeast_1_elem :
  forall (A : Type) (P : A -> Prop) (l : list A),
    AtLeast P 1 l <-> exists x : A, elem x l /\ P x.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; inversion 1; subst; clear H.
      exists h. split; [left | assumption].
      destruct (IHt H2) as (x & IH1 & IH2).
        exists x. split; try right; assumption.
    destruct 1 as (x & H1 & H2). induction H1.
      repeat constructor. assumption.
      apply AL_skip, IHelem, H2.
Qed.
(* end hide *)

Lemma AtLeast_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    P x -> AtLeast P (length l - 1) (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        constructor.
        destruct (intersperse x t); inv Heq.
      constructor. destruct t; cbn in *; constructor.
        assumption.
        rewrite Nat.sub_0_r in IHt. apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    AtLeast P n l -> P x ->
      AtLeast P (n + (length l - 1)) (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    apply AtLeast_intersperse. assumption.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        inv H0. cbn. repeat constructor; assumption.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        rewrite <- plus_n_Sm. constructor.
          assumption.
          constructor.
            assumption.
            rewrite Nat.sub_0_r in IHAtLeast. apply IHAtLeast, H1.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        inv H. cbn. constructor.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        rewrite <- plus_n_Sm. apply AL_skip. constructor.
          assumption.
          rewrite Nat.sub_0_r in IHAtLeast. apply IHAtLeast, H0.
Qed.
(* end hide *)

Lemma AtLeast_intersperse'' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    AtLeast P n l -> ~ P x -> AtLeast P n (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          inv H0. constructor.
          destruct (intersperse x t); inv Heq.
      constructor.
        assumption.
        apply AL_skip. apply IHAtLeast, H1.
    destruct (intersperse x t) eqn: Heq.
      constructor. destruct t; cbn in *.
        inv H. constructor.
        destruct (intersperse x t); inv Heq.
      do 2 constructor. apply IHAtLeast, H0.
Qed.
(* end hide *)

Lemma AtLeast_insert_before_in :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A) (n m : nat),
    AtLeast P m (insertBefore.insertBefore n l1 l2) <->
    (exists m1 m2 : nat,
      AtLeast P m1 l1 /\ AtLeast P m2 l2 /\ m = m1 + m2).
(* begin hide *)
Proof.
  split.
    revert l2 m n.
    induction l1 as [| h t]; cbn; intros.
      exists 0, m. repeat split.
        constructor.
        rewrite insertBefore.insert_before_in_nil in H. assumption.
      destruct n as [| n']; cbn in *.
        apply AtLeast_app_conv in H. firstorder lia.
        destruct t as [| h' t'].
          rewrite insert_before_in_nil in H.
            change (h :: l2) with ([h] ++ l2) in H.
            apply AtLeast_app_conv in H. firstorder.
          inversion H; subst.
            exists 0, 0. firstorder constructor.
            destruct (IHt _ _ _ H4) as (m1 & m2 & IH).
              exists (S m1), m2. firstorder; subst; constructor; trivial.
            destruct (IHt _ _ _ H2) as (m1 & m2 & IH).
              exists m1, m2. firstorder. constructor. assumption.
    destruct 1 as (m1 & m2 & H1 & H2 & H3); subst.
      rewrite insertBefore.insert_before_in_char.
      apply AtLeast_app_comm. rewrite <- app_assoc. apply AtLeast_app.
        exists m2, m1. split.
          assumption.
          pose (AtLeast_take_drop _ _ _ n _ H1).
            rewrite AtLeast_app. firstorder lia.
Qed.
(* end hide *)

(** ** [Exactly] *)

(** Zdefiniuj predykat [Exactly]. Zdanie [Exactly P n l] zachodzi, gdy
    na liście [l] występuje dokładnie [n] elementów spełniających predykat
    [P]. *)

(* begin hide *)
Inductive Exactly {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
| Ex_0 : Exactly P 0 []
| Ex_S :
    forall (n : nat) (h : A) (t : list A),
      P h -> Exactly P n t -> Exactly P (S n) (h :: t)
| Ex_skip :
    forall (n : nat) (h : A) (t : list A),
      ~ P h -> Exactly P n t -> Exactly P n (h :: t).
(* end hide *)

Lemma Exactly_0_cons :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Exactly P 0 (x :: l) <-> ~ P x /\ Exactly P 0 l.
(* begin hide *)
Proof.
  split; intros.
    inv H; firstorder.
    decompose [and or] H; clear H; constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_S_cons :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    Exactly P (S n) (x :: l) <->
    P x /\ Exactly P n l \/ ~ P x /\ Exactly P (S n) l.
(* begin hide *)
Proof.
  split; intros.
    inv H; firstorder.
    decompose [and or] H; clear H; constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_AtLeast :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exactly P n l -> AtLeast P n l.
(* begin hide *)
Proof.
  induction 1; constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_eq :
  forall (A : Type) (P : A -> Prop) (n m : nat) (l : list A),
    Exactly P n l -> Exactly P m l -> n = m.
(* begin hide *)
Proof.
  intros A P n m l H. generalize dependent m.
  induction H; cbn; intros.
    inversion H; subst. reflexivity.
    inversion H1; subst; clear H1.
      rewrite (IHExactly _ H6). reflexivity.
      contradiction.
    inversion H1; subst; clear H1.
      contradiction.
      apply IHExactly, H6.
Qed.
(* end hide *)

Lemma Exactly_length :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exactly P n l -> n <= length l.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_n.
    apply le_n_S. assumption.
    apply le_S. assumption.
Qed.
(* end hide *)

Lemma Exactly_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    Exactly P n l -> ~ P x -> Exactly P n (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    repeat constructor. assumption.
    1-2: constructor; [assumption | apply IHExactly, H1].
Qed.
(* end hide *)

Lemma Exactly_S_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    Exactly P n l -> P x -> Exactly P (S n) (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    repeat constructor. assumption.
    1-2: constructor; [assumption | apply IHExactly, H1].
Qed.
(* end hide *)

Lemma Exactly_app :
  forall (A : Type) (P : A -> Prop) (n1 n2 : nat) (l1 l2 : list A),
    Exactly P n1 l1 -> Exactly P n2 l2 -> Exactly P (n1 + n2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros; try constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_app_conv :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Exactly P n (l1 ++ l2) ->
      exists n1 n2 : nat,
        Exactly P n1 l1 /\ Exactly P n2 l2 /\ n = n1 + n2.
(* begin hide *)
Proof.
  intros A P n l1. generalize dependent n.
  induction l1 as [| h1 t1]; cbn; intros.
    exists 0, n. repeat constructor. assumption.
    inversion H; subst; clear H.
      destruct (IHt1 _ _ H4) as (n1 & n2 & H1 & H2 & Heq); subst.
        exists (S n1), n2. repeat constructor; assumption.
      destruct (IHt1 _ _ H4) as (n1 & n2 & H1 & H2 & Heq); subst.
        exists n1, n2. repeat constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_app_comm :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Exactly P n (l1 ++ l2) -> Exactly P n (l2 ++ l1).
(* begin hide *)
Proof.
  intros. generalize dependent n.
  induction l1 as [| h t]; cbn; intros.
    rewrite app_nil_r. assumption.
    inversion H; subst; clear H; apply Exactly_app_conv in H4;
    destruct H4 as (n1 & n2 & H1 & H2 & Heq); subst.
      rewrite Nat.add_comm, plus_n_Sm.
        apply Exactly_app; try constructor; assumption.
      rewrite Nat.add_comm. apply Exactly_app; try constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_rev :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exactly P n (rev l) <-> Exactly P n l.
(* begin hide *)
Proof.
  intros A P. assert (forall (n : nat) (l : list A),
                        Exactly P n l -> Exactly P n (rev l)).
    induction 1; cbn.
      constructor.
      apply Exactly_S_snoc; assumption.
      apply Exactly_snoc; assumption.
    split; intros.
      rewrite <- rev_rev. apply H. assumption.
      apply H. assumption.
Qed.
(* end hide *)

Lemma Exactly_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (n : nat) (l : list A),
    (forall x y : A, f x = f y -> x = y) ->
    Exactly (fun x : A => P (f x)) n l <->
      Exactly P n (map f l).
(* begin hide *)
Proof.
  split.
    induction 1; cbn; constructor; auto.
    generalize dependent n.
      induction l as [| h t]; cbn; intros;
      inversion H0; subst; clear H0;
      constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    P x -> Exactly P n (replicate n x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_replicate_conv :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    Exactly P n (replicate n x) -> n = 0 \/ P x.
(* begin hide *)
Proof.
  destruct n as [| n']; cbn; intros.
    left. reflexivity.
    right. inversion H; subst; clear H.
      assumption.
      apply Exactly_length in H4. rewrite length_replicate in H4. lia.
Qed.
(* end hide *)

Lemma Exactly_replicate' :
  forall (A : Type) (P : A -> Prop) (n m : nat) (x : A),
    Exactly P n (replicate m x) <->
    n = 0 /\ m = 0 \/
    n = 0 /\ ~ P x \/
    n = m /\ P x.
(* begin hide *)
Proof.
  split.
    generalize dependent n.
    induction m as [| m']; cbn; inversion 1; subst.
      left. split; reflexivity.
      decompose [and or] (IHm' _ H4); subst; clear IHm'.
        do 2 right. split; trivial.
        contradiction.
        do 2 right. split; trivial.
      decompose [and or] (IHm' _ H4); subst; clear IHm'.
        right. left. split; trivial.
        right. left. split; trivial.
        contradiction.
    intro. decompose [and or] H; clear H; subst.
      cbn. constructor.
      induction m as [| m']; cbn; constructor; assumption.
      induction m as [| m']; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m1 m2 : nat),
    Exactly P m1 (take n l) -> Exactly P m2 l -> m1 <= m2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H; subst. apply Nat.le_0_l.
    destruct n as [| n']; cbn.
      inversion H. apply Nat.le_0_l.
      inversion H; inversion H0; subst; clear H H0; try contradiction.
        apply le_n_S. apply (IHt _ _ _ H5 H10).
        apply (IHt _ _ _ H5 H10).
Qed.
(* end hide *)

Lemma Exactly_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m1 m2 : nat),
    Exactly P m1 (drop n l) -> Exactly P m2 l -> m1 <= m2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H. apply Nat.le_0_l.
    destruct n as [| n']; cbn.
      inversion H; inversion H0; subst; clear H H0.
        specialize (IHt 0). rewrite drop_0 in IHt.
          specialize (IHt _ _ H5 H10). apply le_n_S, IHt.
        1-2: contradiction.
        specialize (IHt 0). rewrite drop_0 in IHt.
          apply (IHt _ _ H5 H10).
      inversion H0; subst; clear H0.
        apply le_S. apply (IHt _ _ _ H H5).
        apply (IHt _ _ _ H H5).
Qed.
(* end hide *)

Lemma Exactly_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m : nat),
    Exactly P n l -> exists n1 n2 : nat,
      n = n1 + n2 /\ Exactly P n1 (take m l) /\ Exactly P n2 (drop m l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H; subst. exists 0, 0. repeat constructor.
    inversion H; subst; clear H.
      destruct m as [| m']; cbn.
        exists 0, (S n0). repeat constructor; assumption.
        destruct (IHt _ m' H4) as (n1 & n2 & IH1 & IH2 & IH3); subst.
          exists (S n1), n2. repeat constructor; assumption.
      destruct m as [| m']; cbn.
        exists 0, n. repeat constructor; assumption.
        destruct (IHt _ m' H4) as (n1 & n2 & IH1 & IH2 & IH3); subst.
          exists n1, n2. repeat constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      forall m : nat,
        Exactly P m l <->
        exists m1 mx m2 : nat,
          Exactly P m1 l1 /\ Exactly P mx [x] /\ Exactly P m2 l2 /\
          m1 + mx + m2 = m.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. split; intro.
        inv H.
          exists 0, 1, n. repeat constructor; assumption.
          exists 0, 0, m. repeat constructor; assumption.
          decompose [ex and] H; clear H; subst. inv H1. inv H0.
            cbn. constructor.
              assumption.
              inv H5. cbn. assumption.
            inv H5. cbn. constructor; assumption.
    destruct (splitAt n' t) eqn: Heq.
      destruct p, p. inv H. split; intro.
        inv H.
          rewrite (IHt _ _ _ _ Heq) in H4.
            destruct H4 as (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4); subst.
            exists (S m1), mx, m2. firstorder (constructor; assumption).
          rewrite (IHt _ _ _ _ Heq) in H4.
            destruct H4 as (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4); subst.
            exists m1, mx, m2. firstorder (constructor; assumption).
          destruct H as (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4); subst.
            inv IH1.
              cbn. constructor.
                assumption.
                rewrite (IHt _ _ _ _ Heq). exists n, mx, m2. firstorder.
              constructor.
                assumption.
                rewrite (IHt _ _ _ _ Heq). exists m1, mx, m2. firstorder.
    inv H.
Qed.
(* end hide *)

Lemma Exactly_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) ->
      Exactly P (length (filter p l)) (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h) eqn: Hph; cbn.
      constructor.
        rewrite H. assumption.
        apply IHt, H.
      apply IHt, H.
Qed.
(* end hide *)

Lemma Exactly_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) ->
      Exactly P (length (takeWhile p l)) (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h) eqn: Hph; cbn; constructor.
      rewrite H. assumption.
      apply IHt, H.
Qed.
(* end hide *)

Lemma Exactly_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    (forall x : A, P x <-> p x = true) ->
    Exactly P n l ->
      Exactly P (n - length (takeWhile p l)) (dropWhile p l).
(* begin hide *)
Proof.
  induction 2; cbn.
    constructor.
    destruct (p h) eqn: Hph; cbn.
      assumption.
      rewrite H, Hph in H0. congruence.
    destruct (p h) eqn: Hph; cbn.
      destruct n as [| n']; cbn in *.
        assumption.
        rewrite H in H0. contradiction.
      rewrite Nat.sub_0_r. constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool)
    (n : nat)(x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        Exactly P n l <->
        exists n1 n2 : nat,
          Exactly P n1 b /\ Exactly P n2 e /\
          if p x then S (n1 + n2) = n else n1 + n2 = n.
(* begin hide *)
Proof.
  intros. apply span_spec in H0. subst. split; intro.
    apply Exactly_app_conv in H0.
      destruct H0 as (n1 & n2 & H1 & H2 & H3). inv H2.
        destruct (p x) eqn: Hpx.
          exists n1, n0. repeat split; try assumption. apply plus_n_Sm.
          rewrite H in H6. congruence.
        destruct (p x) eqn: Hpx.
          rewrite H in H6. congruence.
          exists n1, n2. repeat split; assumption.
    destruct H0 as (n1 & n2 & IH1 & IH2 & IH3).
      destruct (p x) eqn: Hpx; subst.
        apply Exactly_app_comm. cbn. constructor.
          rewrite H. assumption.
          apply Exactly_app_comm, Exactly_app; assumption.
        apply Exactly_app_comm. cbn. constructor.
          intro. rewrite H in H0. congruence.
          apply Exactly_app_comm, Exactly_app; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Exactly vs span i AtLeast, AtMost *)
(* end hide *)

Lemma Exactly_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    Exactly P n l -> P x ->
      Exactly P (n + (length l - 1)) (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          specialize (IHExactly H1). inv IHExactly. constructor.
          destruct (intersperse x t); inv Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          inv Heq.
          rewrite <- plus_n_Sm. constructor.
            assumption.
            rewrite Nat.sub_0_r in IHExactly. apply IHExactly, H1.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        constructor; [assumption | apply IHExactly, H1].
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t); inv Heq.
          constructor.
            assumption.
            rewrite <- plus_n_Sm. constructor.
              assumption.
              rewrite Nat.sub_0_r in *. apply IHExactly, H1.
          constructor.
            assumption.
            rewrite <- plus_n_Sm. constructor.
              assumption.
              rewrite Nat.sub_0_r in IHExactly. apply IHExactly, H1.
Restart.
  intros. revert dependent n.
  functional induction @intersperse A x l; cbn; intros.
    inv H. constructor.
    destruct t; cbn in *.
      rewrite Nat.add_0_r. assumption.
      destruct (intersperse x t); inv e0.
    destruct t; cbn in *.
      inv e0.
      rewrite <- plus_n_Sm. inv H.
        cbn. do 2 try constructor; try assumption.
          rewrite Nat.sub_0_r in IHl0.
            destruct (intersperse x t); inv e0; apply IHl0; assumption.
        apply Ex_skip; try constructor; try assumption.
          rewrite Nat.sub_0_r in IHl0.
            destruct (intersperse x t); inv e0; apply IHl0; assumption.
Qed.
(* end hide *)

Lemma Exactly_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    Exactly P n l -> ~ P x ->
      Exactly P n (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    specialize (IHExactly H1). destruct (intersperse x t).
      constructor; assumption.
      do 2 try constructor; assumption.
    specialize (IHExactly H1). destruct (intersperse x t).
      inv IHExactly. repeat constructor; assumption.
      do 2 try constructor; try assumption.
Qed.
(* end hide *)

(** ** [AtMost] *)

(** Zdefiniuj relację [AtMost]. Zdanie [AtMost P n l] zachodzi, gdy
    na liście [l] występuje co najwyżej [n] elementów spełniających
    predykat [P].

    Przykład: *)

(** [AtMost (fun n => n = 0) 3 [0; 1; 2; 3; 0]] zachodzi. *)

(** [AtMost (fun n => n < 5) 5 [1; 2; 3; 4; 5; 6; 7]] nie zachodzi. *)

(* begin hide *)
Inductive AtMost  {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
| AM_0 : forall n : nat, AtMost P n []
| AM_S :
    forall (n : nat) (h : A) (t : list A),
      ~ P h -> AtMost P n t -> AtMost P n (h :: t)
| AM_skip :
    forall (n : nat) (h : A) (t : list A),
      AtMost P n t -> AtMost P (S n) (h :: t).
(* end hide *)

Lemma AtMost_0 :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    AtMost P 0 (x :: l) <-> ~ P x /\ AtMost P 0 l.
(* begin hide *)
Proof.
  split; intros.
    inv H. split; assumption.
    destruct H. constructor; assumption.
Qed.
(* end hide *)

Lemma AtMost_nil :
  forall (A : Type) (P : A -> Prop) (n : nat),
    AtMost P n [] <-> True.
(* begin hide *)
Proof.
  repeat constructor.
Qed.
(* end hide *)

Lemma AtMost_le :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    AtMost P n l -> forall m : nat, n <= m -> AtMost P m l.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    constructor.
      assumption.
      apply IHAtMost. assumption.
    destruct m as [| m'].
      inv H0.
      apply AM_skip, IHAtMost, le_S_n, H0.
Qed.
(* end hide *)

Lemma AtMost_S_cons :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtMost P (S n) (x :: l) <->
    (~ P x /\ AtMost P (S n) l) \/ AtMost P n l.
(* begin hide *)
Proof.
  split; intros.
    inv H; [left | right].
      split; assumption.
      cbn. assumption.
    decompose [and or] H; clear H.
      constructor; assumption.
      constructor; assumption.
Qed.
(* end hide *)

Lemma AtMost_S_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtMost P n l -> AtMost P (S n) (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply AM_skip. constructor.
    constructor; assumption.
    apply AM_skip. assumption.
Qed.
(* end hide *)

Lemma AtMost_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtMost P n l -> ~ P x -> AtMost P n (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    repeat constructor; assumption.
    constructor; [assumption | apply IHAtMost, H1].
    apply AM_skip. apply IHAtMost, H0.
Qed.
(* end hide *)

Lemma AtMost_S :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    AtMost P n l -> AtMost P (S n) l.
(* begin hide *)
Proof.
  induction 1; constructor; assumption.
Qed.
(* end hide *)