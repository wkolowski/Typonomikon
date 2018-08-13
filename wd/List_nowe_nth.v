Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(* begin hide *)
Fixpoint nth {A : Type} (n : nat) (l : list A) {struct l} : option A :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some h
    | h :: t, S n' => nth n' t
end.
(* end hide *)

Lemma nth_nil :
  forall (A : Type) (n : nat),
    nth n (@nil A) = None.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma nth_isEmpty_true :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty l = true -> nth n l = None.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_nth_not_None :
  forall (A : Type) (l : list A) (n : nat),
    nth n l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma nth_length :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A, nth n l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      exists h. reflexivity.
      destruct (IHt _ (lt_S_n _ _ H)) as [x IH]. exists x. assumption.
Qed.
(* end hide *)

Lemma nth_length_lt :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A, nth n l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      exists h. reflexivity.
      destruct (IHt _ (lt_S_n _ _ H)) as [x IH]. exists x. assumption.
Qed.
(* end hide *)

Lemma nth_length_ge :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> nth n l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inversion H.
      apply IHt, le_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_snoc_length_lt :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l -> nth n (snoc x l) = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      reflexivity.
      apply IHt, lt_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_snoc_length_eq :
  forall (A : Type) (x : A) (l : list A),
    nth (length l) (snoc x l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma nth_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    nth n (l1 ++ l2) =
    match nth n l1 with
        | None => nth (n - length l1) l2
        | Some x => Some x
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. reflexivity.
    destruct n as [| n'].
      reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma nth_app_l :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n < length l1 -> nth n (l1 ++ l2) = nth n l1.
(* begin hide *)
Proof.
  intros. rewrite nth_app.
  destruct (nth_length_lt _ _ _ H). rewrite H0. reflexivity.
Qed.
(* end hide *)

Lemma nth_app_r :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 <= n -> nth n (l1 ++ l2) = nth (n - length l1) l2.
(* begin hide *)
Proof.
  intros. rewrite nth_app.
  rewrite (nth_length_ge _ _ _ H). reflexivity.
Qed.
(* end hide *)

Lemma nth_split :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> exists l1 l2 : list A,
      l = l1 ++ x :: l2 /\ length l1 = n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H; subst. exists [], t. cbn. split; reflexivity.
      destruct (IHt _ _ H) as (l1 & l2 & IH1 & IH2); subst.
        exists (h :: l1), l2. cbn. split; reflexivity.
Qed.
(* end hide *)

Lemma nth_None :
  forall (A : Type) (l : list A) (n : nat),
    nth n l = None -> length l <= n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n'].
      inversion H.
      apply le_n_S, IHt, H.
Qed.
(* end hide *)

Lemma nth_Some :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> n < length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      apply le_n_S, le_0_n.
      apply lt_n_S, (IHt _ _ H).
Qed.
(* end hide *)

Lemma nth_spec' :
  forall (A : Type) (l : list A) (n : nat),
    match nth n l with
        | None => length l <= n
        | Some x => exists l1 l2 : list A,
                      l = l1 ++ x :: l2 /\ length l1 = n
    end.
(* begin hide *)
Proof.
  intros. destruct (nth n l) eqn: Heq.
    apply nth_split. assumption.
    apply nth_None. assumption.
Qed.
(* end hide *)

Lemma nth_spec :
  forall (A : Type) (l : list A) (n : nat),
    match nth n l with
        | None => length l <= n
        | Some x => l = take n l ++ x :: drop (S n) l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      reflexivity.
      destruct (nth n' t) eqn: Heq.
        specialize (IHt n'). rewrite Heq in IHt. rewrite IHt at 1.
          reflexivity.
        apply le_n_S. specialize (IHt n'). rewrite Heq in IHt. apply IHt.
Qed.
(* end hide *)

Lemma nth_map_Some :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> nth n (map f l) = Some (f x).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H. reflexivity.
      apply IHt. assumption.
Qed.
(* end hide *)

Lemma nth_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    nth n (map f l) =
    match nth n l with
        | None => None
        | Some x => Some (f x)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma nth_replicate :
  forall (A : Type) (n i : nat) (x : A),
    i < n -> nth i (replicate n x) = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct i; inversion H.
    destruct i as [| i'].
      reflexivity.
      apply IHn', lt_S_n, H.
Qed.
(* end hide *)

Lemma nth_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    nth m (iterate f n x) =
    if leb n m then None else Some (iter f m x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma head_nth :
  forall (A : Type) (l : list A),
    nth 0 l = head l.
(* begin hide *)
Proof. destruct l; reflexivity. Qed.
(* end hide *)

Lemma last_nth :
  forall (A : Type) (l : list A),
    last l = nth (length l - 1) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct t; cbn in *.
      reflexivity.
      rewrite IHt, <- minus_n_O. reflexivity.
Qed.
(* end hide *)

(* DALSZE *)

Lemma nth_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n <= length l -> nth n (insert l n x) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; [reflexivity | inversion H].
    destruct n as [| n']; cbn.
      reflexivity.
      apply IHt, le_S_n, H.
Qed.
(* end hide *)

Lemma nth_insert' :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n (insert l n x) =
    if leb n (length l) then Some x else None.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    1-3: reflexivity.
    apply IHt.
Qed.
(* end hide *)

Lemma remove_length_lt :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      nth n l =
      match remove n l with
          | None => None
          | Some (h, _) => Some h
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      reflexivity.
      rewrite (IHt _ (lt_S_n _ _ H)). destruct (remove n' t).
        destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma last_take :
  forall (A : Type) (l : list A) (n : nat),
    last (take (S n) l) = nth (min n (length l - 1)) l.
(* begin hide *)
Proof.
  intros A l n. revert l.
  induction n as [| n']; destruct l as [| h t]; cbn.
    1-3: reflexivity.
    destruct t; cbn.
      reflexivity.
      specialize (IHn' (a :: t)). cbn in IHn'.
        rewrite IHn', <- minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma nth_take :
  forall (A : Type) (n m : nat) (l : list A),
    nth m (take n l) =
    if leb (S m) n then nth m l else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn.
      destruct (_ <=? _); reflexivity.
      destruct m as [| m']; cbn.
        reflexivity.
        rewrite IHn'. destruct n'; reflexivity.
Qed.
(* end hide *)

Lemma head_drop :
  forall (A : Type) (n : nat) (l : list A),
    head (drop n l) = nth n l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; trivial.
Qed.
(* end hide *)

Lemma nth_drop :
  forall (A : Type) (n m : nat) (l : list A),
    nth m (drop n l) = nth (n + m) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      apply IHn'.
Qed.
(* end hide *)

Lemma remove_nth_take_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x <->
    remove n l = Some (x, take n l ++ drop (S n) l).
(* begin hide *)
Proof.
  split; revert n x.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct n as [| n']; cbn in *.
        inversion H. reflexivity.
        rewrite (IHt _ _ H). reflexivity.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct n as [| n']; cbn in *.
        inversion H. reflexivity.
        apply IHt. destruct (remove n' t).
          destruct p. inversion H. reflexivity.
          inversion H.
Qed.
(* end hide *)

Lemma any_nth :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p l = true <->
    exists (n : nat) (x : A), nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intro.
      inversion H.
      destruct (p h) eqn: Hph; cbn in *.
        exists 0, h. split; [reflexivity | assumption].
        destruct (IHt H) as (n & x & H1 & H2).
          exists (S n), x. split; assumption.
    destruct 1 as (n & x & H1 & H2).
    revert x n H1 H2.
    induction l as [| h t]; cbn; intros.
      inversion H1.
      destruct n as [| n'].
        inversion H1. rewrite H2. cbn. reflexivity.
        rewrite (IHt _ _ H1 H2). rewrite Bool.orb_true_r. reflexivity.
Qed.
(* end hide *)

Lemma all_nth :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p l = true <->
    forall n : nat, n < length l -> exists x : A,
      nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H0.
      destruct (p h) eqn: Hph; cbn in *.
        destruct n as [| n']; cbn.
          exists h. split; [reflexivity | assumption].
          apply lt_S_n in H0. destruct (IHt H _ H0) as (x & H1 & H2).
            exists x. split; assumption.
        congruence.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h) eqn: Hph; cbn in *.
        apply IHt. intros. destruct t as [| h' t'].
          cbn in H0. inversion H0.
          destruct (H 1 ltac:(omega)) as (x & H1 & H2); cbn in *.
            destruct n as [| n']; cbn in *.
              exists h'. inversion H1; subst. split; trivial.
              destruct (H (S (S n')) ltac:(omega)) as (x' & H1' & H2').
                cbn in H1'. exists x'. split; trivial.
        destruct (H 0 ltac:(omega)) as (x & H1 & H2); cbn in *.
          inversion H1; subst. congruence.
Qed.
(* end hide *)

Lemma find_nth :
  forall (A : Type) (p : A -> bool) (l : list A),
    (exists (n : nat) (x : A), nth n l = Some x /\ p x = true) <->
    find p l <> None.
(* begin hide *)
Proof.
  split.
    destruct 1 as (n & x & H1 & H2). revert n x H1 H2.
      induction l as [| h t]; cbn; intros.
        inv H1.
        destruct (p h) eqn: Hph.
          inversion 1.
          destruct n as [| n'].
            inv H1. congruence.
            apply (IHt _ _ H1 H2).
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct (p h) eqn: Hph.
        exists 0, h. split; [reflexivity | assumption].
        destruct (IHt H) as (n & x & H1 & H2). exists (S n), x.
          split; assumption.
Qed.
(* end hide *)

(*Lemma removeFirst_nth_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p l = None <->
      forall (n : nat) (x : A), nth n l = Some x -> p x = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; split; intros.
    inv H0.
    reflexivity.
    destruct (p h) eqn: .
      inv H.
      destruct (removeFirst p t) eqn: Heq.
        destruct p0. inv H.
        destruct IHt. apply (H1 eq_refl 
    Focus 2. rewrite (H 0 h).
  split.
    intros H n. generalize dependent l.
    induction n as [| n']; destruct l as [| h t];
    inversion 2; subst; cbn in *.
      destruct (p x).
        inversion H.
        reflexivity.
      destruct (p h).
        inversion H.
        destruct (removeFirst p t) eqn: Heq.
          destruct p0. inversion H.
          apply (IHn' _ Heq _ H0).
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h) eqn: Hph.
        specialize (H 0 h eq_refl). congruence.
        rewrite IHt.
          reflexivity.
          intros. apply H with (S n). cbn. assumption.
Qed.
(* end hide *)

Lemma removeFirst_nth_Some :
  forall (A : Type) (p : A -> bool) (x : A) (l l' : list A),
    removeFirst p l = Some (x, l') ->
    exists n : nat, nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 1.
    intros. destruct (p h) eqn: Hph.
      inversion H; subst. exists 0. cbn. split; trivial.
      destruct (removeFirst p t) eqn: Heq.
        destruct p0. inversion H; subst.
          destruct (IHt _ eq_refl) as (n & H1 & H2).
            exists (S n). cbn. split; assumption.
        inversion H.
Qed.
(* end hide *)

Lemma removeFirst_nth_Some' :
  exists (A : Type) (p : A -> bool) (n : nat) (x y : A) (l l' : list A),
    removeFirst p l = Some (x, l') /\
    nth n l = Some y /\ p y = true.
(* begin hide *)
Proof.
  exists bool, (fun _ => true), 1, true, false, [true; false], [false].
  cbn. auto.
Qed.
(* end hide *)
*)

Lemma findIndex_nth :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n ->
      exists x : A, nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. exists h. split; [reflexivity | assumption].
      destruct (findIndex p t).
        inv H. destruct (IHt _ eq_refl) as (x & IH1 & IH2).
          exists x. split; assumption.
        inv H.
Qed.
(* end hide *)

Lemma findIndex_nth_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> p x = true ->
      exists m : nat, findIndex p l = Some m /\ m <= n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      exists 0. split; [reflexivity | apply le_0_n].
      destruct n as [| n'].
        inv H. congruence.
        destruct (IHt _ _ H H0) as (m & IH1 & IH2).
          rewrite IH1. exists (S m). split.
            reflexivity.
            apply le_n_S, IH2.
Qed.
(* end hide *)

Lemma findIndex_nth' :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n -> find p l = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. reflexivity.
      destruct (findIndex p t).
        inv H. apply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

(* TODO: move *)
Lemma findIndex_spec2 :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n ->
      takeWhile (fun x : A => negb (p x)) l = take n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite take_nil. reflexivity.
    destruct (p h); cbn.
      inv H. cbn. reflexivity.
      destruct (findIndex p t); inv H.
        cbn. f_equal. apply IHt. reflexivity.
Qed.
(* end hide *)

Lemma findIndex_spec :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n ->
      forall m : nat, m < n ->
        exists x : A, nth m l = Some x /\ p x = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. inv H0.
      destruct m as [| m']; cbn.
        exists h. split; [reflexivity | assumption].
        destruct (findIndex p t); inv H.
          apply (IHt _ eq_refl _ (lt_S_n _ _ H0)).
Qed.
(* end hide *)

Lemma findIndex_last :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndex p l = Some (length l - 1) <->
    exists x : A,
      last l = Some x /\
      p x = true /\
      forall (n : nat) (y : A),
        n < length l - 1 -> nth n l = Some y -> p y = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; split.
    inversion 1.
    destruct 1 as (x & H1 & H2 & H3). inv H1.
    destruct (p h) eqn: Hph; intros.
      inv H. destruct t; inv H1. exists h. repeat split.
        assumption.
        intros. inv H.
Abort.
(* end hide *)

Lemma filter_nth :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> p x = true ->
      exists m : nat, m <= n /\ nth m (filter p l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. exists 0. rewrite H0. cbn. split; reflexivity.
      destruct (IHt _ _ H H0) as (m & IH1 & IH2).
        destruct (p h); cbn.
          exists (S m). split.
            apply le_n_S, IH1.
            assumption.
          exists m. split.
            apply le_trans with (S m).
              apply le_S, le_n.
              apply le_n_S. assumption.
            assumption.
Qed.
(* end hide *)

Lemma map_nth_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    map (fun n : nat => nth n l) (findIndices p l) =
    map Some (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      1-2: rewrite map_map; cbn; rewrite IHt; reflexivity.
Qed.
(* end hide *)

Lemma nth_intersperse_even :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l ->
      nth (2 * n) (intersperse x l) = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      destruct (intersperse x t); reflexivity.
      destruct (intersperse x t).
        cbn. destruct t; cbn in *.
          reflexivity.
          apply lt_S_n in H. specialize (IHt _ H).
            destruct n'; cbn in *; inversion IHt.
              reflexivity.
        rewrite <- plus_n_Sm. cbn. rewrite <- IHt.
          cbn. reflexivity.
          apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_intersperse_odd :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    0 < n -> n < length l ->
      nth (2 * n - 1) (intersperse x l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H0.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        destruct n; cbn in *.
          inversion H.
          destruct n; cbn in *.
            inversion H0. inversion H2.
            inversion H0. inversion H2.
        destruct (intersperse x t); inversion Heq.
      destruct t; cbn in *.
        inversion Heq.
        destruct n as [| n']; cbn.
          inversion H.
          destruct n' as [| n'']; cbn.
            reflexivity.
            rewrite <- IHt with (S n'').
              cbn. rewrite <- ?plus_n_Sm, <- minus_n_O, ?plus_0_r.
                cbn. reflexivity.
              apply le_n_S, le_0_n.
              apply lt_S_n. assumption.
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
      destruct (IHt _ (lt_S_n _ _ H)) as (x & IH1 & IH2).
        exists x. split; try right; assumption.
Qed.
(* end hide *)

Lemma nth_elem_conv :
  forall (A : Type) (x : A) (l : list A),
    elem x l -> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; inversion 1; subst.
    exists 0. reflexivity.
    destruct (IHt H2) as [n Hn]. exists (S n). assumption.
Qed.
(* end hide *)

Lemma nth_elem_Some :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    nth n l = Some x -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. left.
      right. apply (IHt _ H).
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

Lemma nth_In :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A, nth n l = Some x /\ In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      exists h. repeat constructor.
      destruct (IHt _ (lt_S_n _ _ H)) as (x & IH1 & IH2).
        exists x. split; try right; assumption.
Qed.
(* end hide *)

Lemma nth_In_conv :
  forall (A : Type) (x : A) (l : list A),
    In x l -> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; inversion 1; subst.
    exists 0. cbn. trivial.
    destruct (IHt H0) as [n Hn]. exists (S n). cbn. assumption.
Qed.
(* end hide *)

Lemma nth_In_Some :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    nth n l = Some x -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. left. reflexivity.
      right. apply (IHt _ H).
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
        omega.
        rewrite nth_app_r.
          rewrite <- minus_n_n. cbn. reflexivity.
          apply le_n.
        rewrite nth_app_r.
          rewrite <- app_cons_l, nth_app_r.
            replace (nth _ (x :: l3)) with (nth 0 (x :: l3)).
              cbn. reflexivity.
              f_equal. 1-3: simpl; omega.
    destruct 1 as (x & n1 & n2 & H1 & H2 & H3). revert x n1 n2 H1 H2 H3.
    induction l as [| h t]; cbn; intros.
      inv H2.
      destruct n1 as [| n1'], n2 as [| n2'].
        inv H1.
        inv H2. constructor. apply nth_elem_Some with n2'. assumption.
        inv H1.
        right. apply (IHt _ _ _ (lt_S_n _ _ H1) H2 H3).
Qed.
(* end hide *)

Lemma Exists_nth :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l -> exists (n : nat) (x : A),
      nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  induction 1; cbn.
    exists 0, h. split; trivial.
    destruct IHExists as (n & x & H1 & H2).
      exists (S n), x. split; assumption.
Qed.
(* end hide *)

Lemma Exists_nth' :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l <-> exists (n : nat) (x : A),
      nth n l = Some x /\ P x.
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
        apply IHForall. apply lt_S_n. assumption.
    induction l as [| h t]; cbn; intros.
      constructor.
      destruct (H 0 (Nat.lt_0_succ _)) as [x [H1 H2]]; cbn in *.
        inv H1. constructor.
          assumption.
          apply IHt. intros. apply (H (S n)), lt_n_S. assumption.
Qed.
(* end hide *)

Lemma iff_elem_nth :
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

Lemma iff_In_nth :
  forall (A : Type) (x : A) (l : list A),
    In x l <-> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  intros. rewrite In_elem. apply iff_elem_nth.
Qed.
(* end hide *)

Lemma incl_nth :
  forall (A : Type) (l1 l2 : list A),
    incl l1 l2 <->
    forall (n1 : nat) (x : A), nth n1 l1 = Some x ->
      exists n2 : nat, nth n2 l2 = Some x.
(* begin hide *)
Proof.
  unfold incl; split; intros.
    rewrite <- iff_elem_nth. apply H. rewrite iff_elem_nth.
      exists n1. assumption.
    rewrite iff_elem_nth in *. destruct H0 as (n & H0).
      apply H with n. assumption.
Qed.
(* end hide *)