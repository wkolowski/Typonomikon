Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(** * [rmFirst] *)

(* Połączenie [takeWhile], [find], [dropWhile] i [removeFirst].
   Ciekawe, dlaczego wcześniej tego nie zauważyłem. *)

Print takeWhile.
Print find.
Print dropWhile.
Print removeFirst.

(* begin hide *)
Fixpoint rmFirst
  {A : Type} (p : A -> bool) (l : list A) : option (list A * A * list A) :=
match l with
    | [] => None
    | h :: t =>
        if p h
        then Some ([], h, t)
        else
          match rmFirst p t with
              | None => None
              | Some (b, x, e) => Some (h :: b, x, e)
          end
end.

Fixpoint rmLast
  {A : Type} (p : A -> bool) (l : list A) : option (list A * A * list A) :=
match l with
    | [] => None
    | h :: t =>
        match rmLast p t with
            | None => if p h then Some ([], h, t) else None
            | Some (b, x, e) => Some (h :: b, x, e)
        end
end.
(* end hide *)

Lemma rmFirst_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    match rmFirst p l with
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
      destruct (rmFirst p t) eqn: Heq.
        destruct p0, p0. decompose [and] IHt; clear IHt.
          rewrite <- H3, ?H, H0. cbn. repeat split. assumption.
        intros. inv H.
          assumption.
          apply IHt. assumption.
Qed.
(* end hide *)

Lemma rmFirst_wut :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> l = b ++ x :: e.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. inv H. cbn. f_equal. apply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma isEmpty_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    inv H.
    reflexivity.
Qed.
(* end hide *)

Lemma length_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> length b + length e < length l.
(* begin hide *)
Proof.
  intros. apply rmFirst_wut in H. subst. rewrite length_app. cbn.
  rewrite <- plus_n_Sm. apply le_n.
Qed.
(* end hide *)

Lemma rmFirst_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    rmFirst p (snoc x l) =
    match rmFirst p l with
        | None => if p x then Some (l, x, []) else None
        | Some (b, y, e) => Some (b, y, snoc x e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h).
      reflexivity.
      rewrite IHt. destruct (rmFirst p t).
        destruct p0, p0. reflexivity.
        destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    rmFirst p (l1 ++ l2) =
    match rmFirst p l1, rmFirst p l2 with
        | Some (b, x, e), _ => Some (b, x, e ++ l2)
        | _, Some (b, x, e) => Some (l1 ++ b, x, e)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (rmFirst p l2).
      destruct p0, p0. 1-2: reflexivity.
    destruct (p h).
      reflexivity.
      rewrite IHt. destruct (rmFirst p t).
        destruct p0, p0. reflexivity.
        destruct (rmFirst p l2).
          destruct p0, p0. all: reflexivity.
Qed.
(* end hide *)

Lemma rmLast_snoc' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    rmLast p (l ++ [x]) =
    if p x
    then Some (l, x, [])
    else
      match rmLast p l with
          | None => None
          | Some (b, y, e) => Some (b, y, e ++ [x])
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. destruct (p x) eqn: Hpx.
      reflexivity.
      destruct (rmLast p t) eqn: Heq.
        destruct p0, p0. reflexivity.
        destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_rev_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    rmFirst p l =
    match rmLast p (rev l) with
        | None => None
        | Some (b, x, e) => Some (rev e, x, rev b)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite rmLast_snoc', Hph, rev_inv. cbn. reflexivity.
      rewrite rmLast_snoc', Hph, IHt. destruct (rmLast p (rev t)).
        destruct p0, p0. rewrite rev_app. cbn. all: reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    rmFirst p (rev l) =
    match rmLast p l with
        | None => None
        | Some (b, x, e) => Some (rev e, x, rev b)
    end.
(* begin hide *)
Proof.
  intros. rewrite rmFirst_rev_aux, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    rmFirst p (map f l) =
    match rmFirst (fun x : A => p (f x)) l with
        | None => None
        | Some (b, x, e) => Some (map f b, f x, map f e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p (f h)).
      reflexivity.
      rewrite IHt. destruct (rmFirst _ t).
        destruct p0, p0. cbn. all: reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_join :
  forall (A : Type) (p : A -> bool) (lla : list (list A)),
    rmFirst p (join lla) =
    match rmFirst (any p) lla with
        | None => None
        | Some (bl, l, el) =>
            match rmFirst p l with
                | None => None
                | Some (b, x, e) => Some (join bl ++ b, x, e ++ join el)
            end
    end.
(* begin hide *)
Proof.
  induction lla as [| hl tl]; cbn.
    reflexivity.
    rewrite rmFirst_app, IHtl. induction hl as [| h t]; cbn.
      destruct (rmFirst (any p) tl).
        destruct p0, p0. destruct (rmFirst p l1).
          destruct p0, p0. 1-3: reflexivity.
      destruct (p h) eqn: Hph; cbn.
        rewrite Hph. reflexivity.
        destruct (rmFirst p t).
          destruct p0, p0. destruct (any p t); cbn.
            rewrite Hph. destruct (rmFirst p t).
              destruct p0, p0. inv IHt. reflexivity.
              inv IHt.
            destruct (rmFirst (any p) tl).
              destruct p0, p0. destruct (rmFirst p l3).
                destruct p0, p0. inv IHt. cbn. reflexivity.
                inv IHt.
              inv IHt.
          destruct (rmFirst (any p) tl).
            destruct p0, p0. destruct (rmFirst p l1).
              destruct p0, p0. destruct (any p t).
                cbn. rewrite Hph. destruct (rmFirst p t).
                  destruct p0, p0. inv IHt. reflexivity.
                  inv IHt.
                destruct (rmFirst p l1).
                  destruct p0, p0. inv IHt. cbn. rewrite H0. reflexivity.
                  inv IHt.
              destruct (any p t).
                cbn. rewrite Hph. destruct (rmFirst p t).
                  destruct p0, p0. inv IHt.
                  reflexivity.
                destruct (rmFirst p l1).
                  destruct p0, p0. inv IHt.
                  reflexivity.
            destruct (any p t).
              cbn. rewrite Hph. destruct (rmFirst p t).
                destruct p0, p0. inv IHt.
                1-2: reflexivity.
Restart.
  Ltac rec_destr x :=
  match x with
      | context [match ?y with _ => _ end] => rec_destr y
      | _ => let H := fresh "H" in destruct x eqn: H
  end.
  induction lla as [| hl tl]; cbn.
    reflexivity.
    rewrite rmFirst_app, IHtl. induction hl as [| h t]; cbn.
      all: repeat (match goal with
          | H : context [match ?x with _ => _ end] |- _ => rec_destr x
          | |- context [match ?x with _ => _ end] => rec_destr x
      end; cbn in *); try congruence.
Qed.
(* end hide *)

(* TODO: bind *)

Lemma rmFirst_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    rmFirst p (replicate n x) =
    if andb (leb 1 n) (p x)
    then Some ([], x, replicate (n - 1) x)
    else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct (p x) eqn: Hpx.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. cbn. destruct n'; cbn; rewrite ?Hpx; reflexivity.
Qed.
(* end hide *)

(* TODO: iterate *)

Lemma rmFirst_any :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> any p l = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. inv H. eapply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma rmFirst_all :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      all p l = andb (beq_nat (length b) 0) (all p e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_find :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> find p l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_removeFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      removeFirst p l = Some (x, b ++ e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. erewrite IHt; reflexivity.
Qed.
(* end hide *)

(* TODO: findIndex *)

Lemma count_rmFirst_l :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> count p b = 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. cbn. rewrite Hph.
          eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma count_rmFirst_r :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      count p e < length l - length b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. cbn. apply le_n_S. apply count_length.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. cbn. apply IHt. reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    rmFirst p (filter p l) =
    match filter p l with
        | [] => None
        | h :: t => Some ([], h, t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite Hph. reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma filter_rmFirst_l :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> filter p b = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. cbn. rewrite Hph.
          eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma takeWhile_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      takeWhile (fun x : A => negb (p x)) l = b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. f_equal. eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma dropWhile_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      dropWhile (fun x : A => negb (p x)) l = x :: e.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma pmap_rmFirst :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    match
      rmFirst
        (fun x : A => match f x with None => false | Some b => p b end)
        l
    with
        | None => True
        | Some (b, x, e) =>
            exists y : B, f x = Some y /\
              rmFirst p (pmap f l) = Some (pmap f b, y, pmap f e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    destruct (f h) eqn: Heq.
      destruct (p b) eqn: Hpb; cbn; rewrite ?Hpb.
        exists b. split; trivial.
        destruct (rmFirst _ t); trivial.
          destruct p0, p0; cbn in *.
            destruct IHt as (y & IH1 & IH2).
              exists y. rewrite IH1, IH2, Heq. split; reflexivity.
      destruct (rmFirst _ t); trivial.
        destruct p0, p0, IHt as (y & IH1 & IH2).
          exists y. cbn. rewrite IH1, IH2, Heq. split; reflexivity.
Qed.
(* end hide *)

(* TODO: intersperse, groupBy *)

Lemma elem_rmFirst_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    rmFirst p l = None -> forall x : A, elem x l -> p x = false.
(* begin hide *)
Proof.
  induction 2; cbn in H.
    destruct (p x).
      inv H.
      reflexivity.
    destruct (p h).
      inv H.
      apply IHelem. destruct (rmFirst p t).
        destruct p0, p0. inv H.
        reflexivity.
Qed.
(* end hide *)

Lemma elem_rmFirst_Some :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> 
      forall y : A, elem y l <-> elem y b \/ y = x \/ elem y e.
(* begin hide *)
Proof.
  intros. apply rmFirst_wut in H.
  rewrite H, elem_app, elem_cons'. reflexivity.
Qed.
(* end hide *)

Lemma elem_rmFirst :
  forall (A : Type) (p : A -> bool) (l : list A),
    match rmFirst p l with
        | None => forall x : A, elem x l -> p x = false
        | Some (b, x, e) =>
            forall y : A, elem y l <-> elem y b \/ y = x \/ elem y e
    end.
(* begin hide *)
Proof.
  intros. destruct (rmFirst p l) eqn: Heq.
    destruct p0, p0. eapply elem_rmFirst_Some. eassumption.
    apply elem_rmFirst_None. assumption.
Qed.
(* end hide *)

Lemma In_rmFirst :
  forall (A : Type) (p : A -> bool) (x y : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      In y l <-> In y b \/ y = x \/ In y e.
(* begin hide *)
Proof.
  intros. rewrite ?In_elem. apply elem_rmFirst with p. assumption.
Qed.
(* end hide *)

Lemma Dup_cons :
  forall (A : Type) (x : A) (l : list A),
    Dup (x :: l) <-> elem x l \/ Dup l.
(* begin hide *)
Proof.
  split; intros.
    inv H; [left | right]; assumption.
    destruct H; constructor; assumption.
Qed.
(* end hide *)

Lemma Dup_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      Dup l <-> Dup b \/ Dup e \/ elem x b \/ elem x e \/
        exists y : A, elem y b /\ elem y e.
(* begin hide *)
Proof.
(*  split.
    intro H0. revert b x e H. induction H0; cbn; intros.
      destruct (p h).
        inv H0. do 3 right. left. assumption.
        destruct (rmFirst p t) eqn: Heq.
          destruct p0, p0. 1-2: inv H0.
            rewrite (elem_rmFirst _ _ _ _ _ _ Heq) in H.
              decompose [or] H; clear H.
                left. constructor; assumption.
                subst. do 2 right. do 2 left.
                do 4 right. exists h. split; [constructor | assumption].
      destruct (p h).
        inv H. right. left. assumption.
        destruct (rmFirst p t) eqn: Heq.
          destruct p0, p0. 1-2: inv H.
            decompose [or ex and] (IHDup _ _ _ eq_refl); clear IHDup.
              left. right. assumption.
              right. left. assumption.
              do 2 right. left. right. assumption.
              do 3 right. left. assumption.
              do 4 right. exists x0. split; [right | idtac]; assumption.
  revert b x e H. induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. decompose [or ex and] H0; clear H0.
        inv H.
        right. assumption.
        inv H.
        constructor; assumption.
        inv H1.
      destruct (rmFirst p t) eqn: Heq.
        destruct p0, p0. 1-2: inv H. decompose [or ex and] H0; clear H0.
          inv H.
            right. eapply IHt.
*)
  intros. apply rmFirst_wut in H. subst.
  rewrite Dup_app. rewrite Dup_cons. firstorder.
    inv H0; firstorder.
    do 2 right. exists x. split; [assumption | left].
    do 2 right. exists x0. split; try right; assumption.
Qed.
(* end hide *)

(* TODO: NoDup, Rep *)

Lemma Exists_rmFirst :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      rmFirst p l = Some (b, x, e) ->
        Exists P l <-> Exists P b \/ P x \/ Exists P e.
(* begin hide *)
Proof.
  intros. apply rmFirst_wut in H0.
  rewrite H0, Exists_app, Exists_cons.
  reflexivity.
Qed.
(* end hide *)

Lemma Forall_rmFirst :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      rmFirst p l = Some (b, x, e) ->
        Forall P l <-> Forall P b /\ P x /\ Forall P e.
(* begin hide *)
Proof.
  intros. apply rmFirst_wut in H0.
  rewrite H0, Forall_app, Forall_cons'.
  reflexivity.
Qed.
(* end hide *)

Lemma Exactly_rmFirst :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool)
    (n : nat)(x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      rmFirst p l = Some (b, x, e) ->
        Exactly P n l <->
        exists n1 n2 : nat,
          Exactly P n1 b /\ Exactly P n2 e /\
          if p x then S (n1 + n2) = n else n1 + n2 = n.
(* begin hide *)
Proof.
  intros. apply rmFirst_wut in H0. subst. split; intro.
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

(* TODO: AtLeast, AtMost *)

Lemma incl_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      incl b l /\ elem x l /\ incl e l.
(* begin hide *)
Proof.
  intros. apply rmFirst_wut in H. subst. repeat split.
    apply incl_app_l, incl_refl.
    rewrite elem_app. right. left.
    apply incl_app_r. constructor. assumption.
Qed.
(* end hide *)

(* TODO: sublist *)

(* TODO: z palindromami chyba nie będzie nic ciekawego *)