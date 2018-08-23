Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Arith.
Require Import Omega.

Require Import CoqBookPL.book.X3.

(** ** [splitAt] *)

Fixpoint splitAt
  {A : Type} (n : nat) (l : list A) {struct l}
  : option (list A * A * list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some ([], h, t)
    | h :: t, S n' =>
        match splitAt n' t with
            | None => None
            | Some (l1, x, l2) => Some (h :: l1, x, l2)
        end
end.

Lemma splitAt_spec :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
        | None => length l <= n
        | Some (l1, x, l2) => l = l1 ++ x :: l2
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      reflexivity.
      specialize (IHt n'). destruct (splitAt n' t).
        destruct p, p. cbn. rewrite <- IHt. reflexivity.
        apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma splitAt_isEmpty_true :
  forall (A : Type) (l : list A),
    isEmpty l = true -> forall n : nat, splitAt n l = None.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_splitAt_false :
  forall (A : Type) (l : list A) (n : nat),
    splitAt n l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma splitAt_length_inv :
  forall (A : Type) (l : list A) (n : nat),
    splitAt n l <> None <-> n < length l.
(* begin hide *)
Proof.
  split; revert n.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct n as [| n'].
        apply le_n_S, le_0_n.
        apply lt_n_S, IHt. destruct (splitAt n' t); congruence.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inversion 1.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. congruence.
          intro. apply (IHt _ (lt_S_n _ _ H)). assumption.
Qed.
(* end hide *)

(* TODO *) (*Lemma splitAt_length_inv :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
        | None => length l <= n
        | Some _ => n < length l
    end.
(* begin hide *)
Proof.*)

Lemma splitAt_length_lt :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A,
      splitAt n l = Some (take n l, x, drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inv H.
    destruct n as [| n']; cbn.
      exists h. rewrite drop_0. reflexivity.
      apply lt_S_n in H. destruct (IHt _ H) as [x IH].
        exists x. rewrite IH. cbn. reflexivity.
Qed.
(* end hide *)

Lemma splitAt_length_ge :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> splitAt n l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      inversion H.
      apply le_S_n in H. rewrite (IHt _ H). reflexivity.
Qed.
(* end hide *)

(* TODO Lemma splitAt_length :
  forall (A : Type) (l : list A) (n : nat),
    splitAt n l =
    if n <? length l
    then
*)

Lemma splitAt_snoc :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    splitAt n (snoc x l) =
    if n <? length l
    then
      match splitAt n l with
          | None => None
          | Some (b, y, e) => Some (b, y, snoc x e)
      end
    else
      if beq_nat n (length l)
      then Some (l, x, [])
      else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. unfold ltb. destruct (length t); cbn.
        destruct n'; reflexivity.
        destruct (n' <=? n).
          destruct (splitAt n' t).
            destruct p, p. 1-2: reflexivity.
            destruct (n' =? S n); reflexivity.
Qed.
(* end hide *)

Lemma splitAt_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    splitAt n (l1 ++ l2) =
    match splitAt n l1 with
        | Some (l11, x, l12) => Some (l11, x, l12 ++ l2)
        | None =>
            match splitAt (n - length l1) l2 with
                | Some (l21, x, l22) => Some (l1 ++ l21, x, l22)
                | None => None
            end
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (splitAt n l2).
      destruct p, p. 1-2: reflexivity.
    destruct n as [| n'].
      reflexivity.
      rewrite IHt. destruct (splitAt n' t).
        destruct p, p. reflexivity.
        cbn. destruct (splitAt (n' - length t) l2).
          destruct p, p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma splitAt_app_lt :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n < length l1 ->
      splitAt n (l1 ++ l2) =
      match splitAt n l1 with
          | None => None
          | Some (x, l11, l12) => Some (x, l11, l12 ++ l2)
      end.
(* begin hide *)
Proof.
  intros. rewrite splitAt_app.
  destruct (splitAt_length_lt _ l1 n H).
  rewrite H0. reflexivity.
Qed.
(* end hide *)

Lemma splitAt_app_ge :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 <= n ->
      splitAt n (l1 ++ l2) =
      match splitAt (n - length l1) l2 with
          | None => None
          | Some (l21, x, l22) => Some (l1 ++ l21, x, l22)
      end.
(* begin hide *)
Proof.
  intros. rewrite splitAt_app, splitAt_length_ge.
    destruct (splitAt (n - length l1) l2).
      destruct p, p. 1-2: reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma splitAt_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      splitAt n l =
      match splitAt (length l - S n) (rev l) with
          | None => None
          | Some (l1, x, l2) => Some (rev l2, x, rev l1)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite splitAt_app, splitAt_length_ge.
        1-2: rewrite length_rev, <- minus_n_O.
          cbn. rewrite minus_diag, rev_app, rev_inv. cbn. reflexivity.
        reflexivity.
      rewrite IHt, splitAt_app; clear IHt.
        destruct (splitAt (length t - S n') (rev t)) eqn: Heq.
          destruct p, p. rewrite rev_app. cbn. reflexivity.
          destruct t; cbn in *.
            omega.
            destruct
              (splitAt_length_lt A (rev t ++ [a]) (length t - n'))
            as [x H'].
              rewrite length_app, length_rev. cbn. omega.
              congruence.
        apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma splitAt_rev :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      splitAt n (rev l) =
      match splitAt (length l - S n) l with
          | None => None
          | Some (l1, x, l2) => Some (rev l2, x, rev l1)
      end.
(* begin hide *)
Proof.
  intros. rewrite <- length_rev in H.
  rewrite (splitAt_rev_aux _ _ _ H).
  rewrite length_rev, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma splitAt_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    splitAt n (map f l) =
    match splitAt n l with
        | None => None
        | Some (l1, x, l2) => Some (map f l1, f x, map f l2)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (splitAt n' t).
        destruct p, p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma splitAt_replicate :
  forall (A : Type) (n m : nat) (x : A),
    splitAt m (replicate n x) =
      if m <? n
      then Some (replicate m x, x, replicate (n - S m) x)
      else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. unfold ltb. destruct n' as [| n'']; cbn.
        reflexivity.
        destruct (m' <=? n''); reflexivity.
Qed.
(* end hide *)

Lemma splitAt_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    splitAt m (iterate f n x) =
    if m <? n
    then Some (iterate f m x, iter f m x, iterate f (n - S m) (iter f (S m) x))
    else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. unfold ltb. destruct n' as [| n'']; cbn.
        reflexivity.
        destruct (m' <=? n''); reflexivity.
Qed.
(* end hide *)

Lemma splitAt_spec' :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      l1 = take n l /\ l2 = drop (S n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 2.
    destruct n as [| n']; cbn.
      inversion 1; subst. rewrite drop_0. split; reflexivity.
      destruct (splitAt n' t) eqn: Heq; intros.
        destruct p, p. inversion H; subst; clear H.
          destruct (IHt _ _ _ _ Heq). rewrite H, H0.
            cbn. split; reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma splitAt_head_l :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      head l1 =
      match n with
          | 0 => None
          | _ => head l
      end.
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  rewrite H, ?H0. rewrite head_take. destruct n; reflexivity.
Qed.
(* end hide *)

Lemma splitAt_head_r :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      head l2 = nth (S n) l.
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  rewrite H0. rewrite head_drop. reflexivity.
Qed.
(* end hide *)

(* TODO: tail, uncons *)

Lemma splitAt_Some :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) -> n < length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      apply Nat.lt_0_succ.
      destruct (splitAt n' t) eqn: Heq.
        destruct p, p. inversion H; subst; clear H.
          apply lt_n_S, (IHt _ _ _ _ Heq).
        inversion H.
Qed.
(* end hide *)

Lemma splitAt_last_l :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      last l1 =
      match n with
          | 0 => None
          | S n' => nth n' l
      end.
(* begin hide *)
Proof.
  intros. pose (H' := H). apply splitAt_spec' in H'. destruct H'.
  rewrite H0. destruct n.
    rewrite take_0. reflexivity.
    rewrite last_take. apply splitAt_Some in H.
    rewrite Min.min_r.
      reflexivity.
      omega.
Qed.
(* end hide *)

Lemma splitAt_last_r :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      last l2 =
      if beq_nat n (length l - 1)
      then nth (length l - 2) l
      else last l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H; subst; clear H. destruct l2; cbn.
Abort.
(* end hide *)

(* TODO: init, unsnoc *)

Lemma take_splitAt :
  forall (A : Type) (l l1 l2 : list A) (n m : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      take m l1 = take (min n m) l.
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  rewrite H, take_take. reflexivity.
Qed.
(* end hide *)

Lemma take_splitAt' :
  forall (A : Type) (l l1 l2 : list A) (n m : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      take m l2 = take m (drop (S n) l).
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H.
  destruct H. subst. reflexivity.
Qed.
(* end hide *)

Lemma drop_splitAt_l :
  forall (A : Type) (l l1 l2 : list A) (n m : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      drop m l1 = take (n - m) (drop m l).
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  subst. rewrite drop_take. reflexivity.
Qed.
(* end hide *)

Lemma drop_splitAt_r :
  forall (A : Type) (l l1 l2 : list A) (n m : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      drop m l2 = drop (S n + m) l.
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  subst. rewrite drop_drop. reflexivity.
Qed.
(* end hide *)

Lemma splitAt_megaspec :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
        | None => length l <= n
        | Some (l1, x, l2) =>
            nth n l = Some x /\
            l1 = take n l /\
            l2 = drop (S n) l /\
            l = l1 ++ x :: l2
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      repeat split. rewrite drop_0. reflexivity.
      destruct (splitAt n' t) eqn: Heq.
        destruct p, p. specialize (IHt n'). rewrite Heq in IHt.
          decompose [and] IHt; clear IHt. subst. repeat split.
            assumption.
            rewrite H3 at 1. reflexivity.
        specialize (IHt n'). rewrite Heq in IHt. apply le_n_S, IHt.
Qed.
(* end hide *)

Lemma splitAt_zip :
  forall (A B : Type) (la : list A) (lb : list B) (n : nat),
    splitAt n (zip la lb) =
    match splitAt n la, splitAt n lb with
        | Some (la1, a, la2), Some (lb1, b, lb2) =>
            Some (zip la1 lb1, (a, b), zip la2 lb2)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  intros. assert (H := splitAt_megaspec A la n). destruct (splitAt n la).
    Focus 2. apply splitAt_length_ge. rewrite length_zip.
      apply Nat.min_case_strong; intros.
        assumption.
        apply le_trans with (length la); assumption.
    destruct p, p. decompose [and] H; clear H; subst.
      assert (H := splitAt_megaspec B lb n). destruct (splitAt n lb).
        Focus 2. apply splitAt_length_ge. rewrite length_zip.
          apply Nat.min_case_strong; intros.
            apply le_trans with (length lb); assumption.
            assumption.
        destruct p, p. decompose [and] H; clear H; subst.
          rewrite H4, H6.
Restart.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (splitAt n' ta).
          destruct p, p. 1-2: reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (splitAt n' ta), (splitAt n' tb).
          destruct p, p, p0, p. cbn. reflexivity.
          destruct p, p. 1-3: reflexivity.
Qed.
(* end hide *)

Lemma splitAt_zipWith :
  forall (A B C : Type) (f : A -> B -> C)
    (la : list A) (lb : list B) (n : nat),
      splitAt n (zipWith f la lb) =
      match splitAt n la, splitAt n lb with
          | Some (la1, a, la2), Some (lb1, b, lb2) =>
              Some (zipWith f la1 lb1, f a b, zipWith f la2 lb2)
          | _, _ => None
      end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (splitAt n' ta).
          destruct p, p. 1-2: reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (splitAt n' ta), (splitAt n' tb).
          destruct p, p, p0, p. cbn. reflexivity.
          destruct p, p. 1-3: reflexivity.
Qed.
(* end hide *)

Lemma count_splitAt :
  forall (A : Type) (p : A -> bool) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      count p l = (if p x then 1 else 0) + count p l1 + count p l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n']; cbn.
      inversion H; subst; clear H. destruct (p x); reflexivity.
      destruct (splitAt n' t) eqn: Heq; cbn in H.
        destruct p0, p0. inversion H; subst; clear H.
          cbn. destruct (p h), (p x) eqn: Hpx; cbn;
          rewrite (IHt _ _ _ _ Heq), Hpx; reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma splitAt_filter :
  forall (A : Type) (p : A -> bool) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n (filter p l) = Some (l1, x, l2) ->
      exists m : nat,
      match splitAt m l with
          | None => False
          | Some (l1', y, l2') =>
              x = y /\ l1 = filter p l1' /\ l2 = filter p l2'
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h) eqn: Hph.
      destruct n as [| n']; cbn in *.
        inversion H; subst; clear H. exists 0. repeat split.
        destruct (splitAt n' (filter p t)) eqn: Heq.
          destruct p0, p0. inversion H; subst; clear H.
            destruct (IHt _ _ _ _ Heq) as [m IH].
              exists (S m). destruct (splitAt m t).
                destruct p0, p0, IH as (IH1 & IH2 & IH3); subst.
                  cbn. rewrite Hph. repeat split.
                assumption.
          inversion H.
      destruct (IHt _ _ _ _ H) as (m & IH). exists (S m).
        destruct (splitAt m t).
          destruct p0, p0. cbn. rewrite Hph. assumption.
          assumption.
Qed.
(* end hide *)

(* TODO: intersperse_splitAt *)

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

Lemma Forall_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      Forall P l <-> P x /\ Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  rewrite Forall_app, Forall_cons'. firstorder.
Qed.
(* end hide *)

Lemma AtLeast_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      forall m : nat,
        AtLeast P m l -> exists m1 m2 : nat,
          AtLeast P m1 l1 /\ AtLeast P m2 l2 /\ m = m1 + m2.
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma Exactly_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      forall m : nat,
        Exactly P m l <-> exists m1 m2 : nat,
          Exactly P m1 l1 /\ Exactly P m2 l2 /\
          (P x /\ m = S (m1 + m2) \/ ~ P x /\ m = m1 + m2).
(* begin hide *)
Proof.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  split.
Abort.
(* end hide *)

Lemma incl_splitAt :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
        | None => True
        | Some (l1, _, l2) => incl l1 l /\ incl l2 l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      split.
        apply incl_nil.
        apply incl_cons'.
      specialize (IHt n'). destruct (splitAt n' t).
        destruct p, p. destruct IHt as (IH1 & IH2). split.
          apply incl_cons, IH1.
          apply incl_cons'', IH2.
        assumption.
Qed.
(* end hide *)