Require Import D5.

(* begin hide *)
Fixpoint rev {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => snoc h (rev t)
end.
(* end hide *)

Lemma isEmpty_rev :
  forall (A : Type) (l : list A),
    isEmpty (rev l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    apply isEmpty_snoc.
Qed.
(* end hide *)

Lemma length_rev :
  forall (A : Type) (l : list A),
    length (rev l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma snoc_rev :
  forall (A : Type) (l : list A) (x : A),
    snoc x (rev l) = rev (x :: l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma rev_snoc :
  forall (A : Type) (x : A) (l : list A),
    rev (snoc x l) = x :: rev l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma rev_app :
  forall (A : Type) (l1 l2 : list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intro.
    rewrite app_nil_r. reflexivity.
    rewrite IHt1, snoc_app, snoc_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_rev :
  forall (A : Type) (l : list A),
    rev (rev l) = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite rev_snoc, IHt. reflexivity.
Qed.
(* end hide *)

(* GRUBA KRESKA ================================================= *)

Lemma map_rev :
  forall (A B : Type) (f : A -> B) (l : list A),
    map f (rev l) = rev (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite map_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma rev_join :
  forall (A : Type) (l : list (list A)),
    rev (join l) = join (rev (map rev l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite rev_app, join_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma rev_bind :
  forall (A B : Type) (f : A -> list B) (l : list A),
    rev (bind f l) = bind (fun x : A => rev (f x)) (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite rev_app, IHt, bind_snoc. reflexivity.
Qed.
(* end hide *)

Lemma rev_replicate :
  forall (A : Type) (n : nat) (x : A),
    rev (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn', snoc_replicate. cbn. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma iter_out :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iter f n (f x) = f (iter f n x).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

Lemma map_iterate_inv :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      map g (iterate f n (f x)) = iterate f n x.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite H, IHn'; trivial.
Qed.

Lemma rev_iterate_aux :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      rev (iterate g n (iter f n x)) = iterate f n (f x).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite <- map_iterate, <- map_rev, IHn', map_iterate_inv,
    snoc_iterate.
      cbn. reflexivity.
      all: assumption.
Qed.

Lemma rev_iterate_aux' :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      iterate f (S n) x = rev (iterate g (S n) (iter f n x)).
Proof.
  induction n as [| n']; cbn in *; intros.
    reflexivity.
    rewrite IHn'. rewrite ?iter_out, ?H. rewrite <- IHn'. cbn.
      do 2 f_equal. apply rev_iterate_aux. all: assumption.
Qed.
(* end hide *)

Lemma rev_iterate :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      rev (iterate f n x) = iterate g n (iter f (n - 1) x).
(* begin hide *)
Proof.
  destruct n; intros.
    cbn. reflexivity.
    rewrite (rev_iterate_aux' _ _ _ n _ H), rev_rev. 
      cbn. rewrite <- minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma last_rev :
  forall (A : Type) (l : list A),
    last (rev l) = head l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite last_snoc. reflexivity.
Qed.
(* end hide *)

Lemma head_rev :
  forall (A : Type) (l : list A),
    head (rev l) = last l.
(* begin hide *)
Proof.
  intros. rewrite <- last_rev, rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma tail_rev :
  forall (A : Type) (l : list A),
    tail (rev l) =
    match init l with
        | None => None
        | Some t => Some (rev t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite tail_snoc. destruct (rev t); cbn in *.
      destruct (init t).
        inversion IHt.
        reflexivity.
      destruct (init t); cbn; inversion IHt; subst. reflexivity.
Qed.
(* end hide *)

Lemma init_rev :
  forall (A : Type) (l : list A),
    init (rev l) =
    match tail l with
        | None => None
        | Some t => Some (rev t)
    end.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l) at 2. rewrite tail_rev.
  destruct (init (rev l)); rewrite ?rev_rev; reflexivity.
Qed.
(* end hide *)

Lemma rev_uncons :
  forall (A : Type) (x : A) (l l' : list A),
    uncons l = Some (x, l') -> Some (rev l') = init (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; inv H.
    rewrite init_snoc. reflexivity.
Qed.
(* end hide *)

Lemma rev_unsnoc :
  forall (A : Type) (x : A) (l l' : list A),
    unsnoc l = Some (x, l') -> Some (rev l') = tail (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; inv H.
    destruct (unsnoc t) eqn: H.
      destruct p. inv H1. rewrite tail_snoc, <- (IHt _ eq_refl).
        cbn. reflexivity.
      inv H1. destruct t; inv H; cbn.
        reflexivity.
        destruct (unsnoc t); try destruct p; inv H1.
Qed.
(* end hide *)

(* TODO *) Lemma nth_snoc_lt :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    n < length l -> nth n (snoc x l) = nth n l.
(* begin hide *)
Proof.
  induction n as [| n'];
  destruct l as [| h t];
  cbn; intro H; inv H.
    reflexivity.
    reflexivity.
    apply IHn'. red. rewrite H1. constructor.
    apply IHn'. red. eapply le_trans.
      2: eassumption.
      do 2 constructor.
Qed.
(* end hide *)

Lemma nth_snoc_eq :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    n = length l -> nth n (snoc x l) = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
    reflexivity.
    all: inv H. apply IHn'. reflexivity.
Qed.
(* end hide *)

Lemma nth_rev_aux :
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> nth n l = nth (length l - S n) (rev l).
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
    1,3: reflexivity.
    rewrite <- minus_n_O, nth_snoc_eq.
      2: rewrite length_rev. 1-2: reflexivity.
      rewrite nth_snoc_lt.
        apply IHn', lt_S_n, H.
        rewrite length_rev. lia.
Qed.
(* end hide *)

Lemma nth_rev :
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> nth n (rev l) = nth (length l - S n) l.
(* begin hide *)
Proof.
  intros. rewrite nth_rev_aux, rev_rev; rewrite length_rev.
    reflexivity.
    assumption.
Qed.
(* begin hide *)

Lemma insert_rev_aux :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    insert l n x = rev (insert (rev l) (length l - n) x).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      replace (S (length t)) with (length (snoc h (rev t))).
        rewrite insert_length, ?rev_snoc, rev_rev. reflexivity.
        rewrite length_snoc, length_rev. reflexivity.
      rewrite ?IHt, snoc_app_singl, insert_app, length_rev.
        assert (length t - n' <= length t).
          apply Nat.le_sub_l.
          apply leb_correct in H. rewrite H.
            rewrite rev_app. cbn. reflexivity.
Qed.
(* end hide *)

Lemma insert_rev :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    insert (rev l) n x = rev (insert l (length l - n) x).
(* begin hide *)
Proof.
  intros. rewrite insert_rev_aux, rev_rev, length_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    rev (insert l n x) = insert (rev l) (length l - n) x.
(* begin hide *)
Proof.
  intros. pose (insert_rev _ (rev l)).
  rewrite rev_rev in e.
  rewrite e, rev_rev, length_rev. reflexivity.
Qed.
(* end hide *)

Lemma remove_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      remove n l =
      match remove (length l - S n) (rev l) with
          | None => None
          | Some (h, t) => Some (h, rev t)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite <- minus_n_O, <- length_rev, remove_length_snoc, rev_rev.
        reflexivity.
      rewrite (IHt _ (lt_S_n _ _ H)), remove_snoc_lt.
        destruct (remove (length t - S n') (rev t)).
          destruct p. rewrite rev_snoc. 1-2: reflexivity.
        rewrite length_rev. lia. (* TODO *)
Qed.
(* end hide *)

Lemma remove_rev :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      remove n (rev l) =
      match remove (length l - S n) l with
          | None => None
          | Some (h, t) => Some (h, rev t)
      end.
(* begin hide *)
Proof.
  intros. rewrite remove_rev_aux, rev_rev; rewrite length_rev.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma drop_snoc :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n <= length l -> drop n (snoc x l) = snoc x (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      apply IHt. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma take_snoc :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n <= length l -> take n (snoc x l) = take n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      f_equal. apply IHt. apply le_S_n. assumption.
Qed.
(* end hide *)

(* begin hide *)
Lemma take_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    take n l = rev (drop (length (rev l) - n) (rev l)).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [ |n'].
      rewrite drop_length'.
        reflexivity.
        rewrite length_snoc, length_rev, <- minus_n_O. apply le_n.
      rewrite IHt, length_snoc, drop_snoc; cbn.
        rewrite rev_snoc. reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma take_rev :
  forall (A : Type) (l : list A) (n : nat),
    take n (rev l) = rev (drop (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_take :
  forall (A : Type) (l : list A) (n : nat),
    rev (take n l) = drop (length l - n) (rev l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_rev, length_rev. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma drop_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    drop n l = rev (take (length (rev l) - n) (rev l)).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [ |n'].
      rewrite take_length'.
        rewrite rev_snoc, rev_rev. reflexivity.
        rewrite length_snoc, length_rev, <- minus_n_O. apply le_n.
      rewrite IHt, length_snoc, take_snoc; cbn.
        reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma drop_rev :
  forall (A : Type) (l : list A) (n : nat),
    drop n (rev l) = rev (take (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite drop_rev_aux, rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_drop :
  forall (A : Type) (l : list A) (n : nat),
    drop n (rev l) = rev (take (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite drop_rev_aux, rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma zip_not_rev :
  exists (A B : Type) (la : list A) (lb : list B),
    zip (rev la) (rev lb) <> rev (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists [true; false; true], [false; true].
  cbn. inversion 1.
Qed.
(* end hide *)

Lemma zipWith_not_rev :
  exists (A B C : Type) (f : A -> B -> C) (la : list A) (lb : list B),
    zipWith f (rev la) (rev lb) <> rev (zipWith f la lb).
(* begin hide *)
Proof.
  exists bool, bool, (prod bool bool),
         pair, [true; false; true], [false; true].
  cbn. inversion 1.
Qed.
(* end hide *)

Lemma rev_unzip :
  forall (A B : Type) (l : list (A * B)) (la : list A) (lb : list B),
    unzip l = (la, lb) -> unzip (rev l) = (rev la, rev lb).
(* begin hide *)
Proof.
  induction l as [| [ha ta] t]; cbn; intros.
    inv H. cbn. reflexivity.
    destruct (unzip t). inv H. rewrite unzip_snoc, (IHt _ _ eq_refl).
      cbn. reflexivity.
Qed.
(* end hide *)

Lemma rev_unzipWith :
  forall (A B C : Type) (f : A -> B * C) (l : list A),
    unzipWith f (rev l) =
      let (la, lb) := unzipWith f l in (rev la, rev lb).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (unzipWith f t), (f h) eqn: Heq.
      rewrite unzipWith_spec, map_snoc, map_rev, unzip_snoc, IHt, Heq in *.
        cbn. reflexivity.
Qed.
(* end hide *)

Lemma any_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p (rev l) = any p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite any_snoc, IHt, ?Bool.orb_assoc, Bool.orb_comm. reflexivity.
Qed.
(* end hide *)

Lemma all_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p (rev l) = all p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite all_snoc, IHt, Bool.andb_comm. reflexivity.
Qed.
(* end hide *)

Lemma find_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    find p (rev l) = findLast p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite find_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma findLast_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    findLast p (rev l) = find p l.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l), find_rev, rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p (rev l) =
    match removeLast p l with
        | Some (x, l) => Some (x, rev l)
        | None => None
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite removeFirst_snoc, IHt. destruct (removeLast p t).
      destruct p0. cbn. reflexivity.
      destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma removeLast_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeLast p (rev l) =
    match removeFirst p l with
        | None => None
        | Some (x, l) => Some (x, rev l)
    end.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l) at 2. rewrite removeFirst_rev.
  destruct (removeLast p (rev l)).
    destruct p0. rewrite rev_rev. all: reflexivity.
Qed.
(* end hide *)

Lemma count_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p (rev l) = count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite count_snoc, IHt. destruct (p h); cbn.
      rewrite plus_comm. cbn. reflexivity.
      apply plus_0_r.
Qed.
(* end hide *)

Lemma filter_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    filter p (rev l) = rev (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite filter_snoc. destruct (p h); cbn; rewrite IHt; reflexivity.
Qed.
(* end hide *)

Lemma findIndices_rev_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    rev (findIndices p (rev l)) =
    map (fun n : nat => length l - S n) (findIndices p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite findIndices_snoc, length_rev. destruct (p h); cbn.
      all: rewrite ?rev_snoc, <- ?minus_n_O, map_map, IHt; reflexivity.
Qed.
(* end hide *)

Lemma findIndices_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndices p (rev l) =
    rev (map (fun n : nat => length l - S n) (findIndices p l)).
(* begin hide *)
Proof.
  intros. rewrite <- findIndices_rev_aux, rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    rev (findIndices p l) =
    map (fun n : nat => length l - S n) (findIndices p (rev l)).
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l) at 1.
  rewrite findIndices_rev_aux, length_rev.
  reflexivity.
Qed.
(* end hide *)

Lemma last_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    last (findIndices p l) =
    match findIndex p (rev l) with
        | None => None
        | Some n => Some (length l - S n)
    end.
(* begin hide *)
Proof.
  intros.
  rewrite <- head_rev, <- (rev_rev _ l) at 1.
  rewrite findIndices_rev_aux, <- head_findIndices.
  destruct (findIndices p (rev l)); cbn.
    reflexivity.
    rewrite length_rev. reflexivity.
Qed.
(* end hide *)

Lemma init_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    init (findIndices p l) =
    match removeLast p l with
        | None => None
        | Some (_, l') => Some (findIndices p l')
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite init_map. destruct (findIndices p t) eqn: Heq; cbn in *.
        destruct (removeLast p t).
          destruct p0. inversion IHt.
          rewrite Heq. reflexivity.
        destruct (init l), (removeLast p t); cbn.
          destruct p0. cbn. rewrite Hph. inversion IHt; subst. cbn.
            reflexivity.
          inversion IHt.
          destruct p0. cbn. rewrite Hph. inversion IHt; subst; cbn.
            reflexivity.
          inversion IHt.
      rewrite init_map. destruct (findIndices p t) eqn: Heq; cbn in *.
        destruct (removeLast p t).
          destruct p0. inversion IHt.
          reflexivity.
        destruct (init l), (removeLast p t); cbn.
          destruct p0. cbn. rewrite Hph. inversion IHt; subst; cbn.
            reflexivity.
          inversion IHt.
          destruct p0. cbn. rewrite Hph. inversion IHt; subst; cbn.
            reflexivity.
          inversion IHt.
Qed.
(* end hide *)

Lemma pmap_snoc :
  forall (A B : Type) (f : A -> option B) (x : A) (l : list A),
    pmap f (snoc x l) =
    match f x with
        | None => pmap f l
        | Some b => snoc b (pmap f l)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct (f x); reflexivity.
    destruct (f x), (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_rev :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f (rev l) = rev (pmap f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_snoc. destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma intersperse_rev :
  forall (A : Type) (x : A) (l : list A),
    intersperse x (rev l) = rev (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite intersperse_snoc. destruct (rev t) eqn: Heq.
      apply (f_equal rev) in Heq. rewrite rev_rev in Heq.
        cbn in Heq. rewrite Heq. cbn. reflexivity.
      rewrite IHt. destruct (intersperse x t); cbn.
        cbn in IHt. destruct (intersperse x l); inversion IHt.
          reflexivity.
Qed.
(* end hide *)

(** PREDYKATY *)

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

Lemma In_rev :
  forall (A : Type) (x : A) (l : list A),
    In x (rev l) <-> In x l.
(* begin hide *)
Proof.
  intros. rewrite ?In_elem in *. apply elem_rev.
Qed.
(* end hide *)

(* TODO: być może dobry przykład do zilustrowania reguły
         wlog (bez straty ogólności)? *)

Lemma NoDup_rev :
  forall (A : Type) (l : list A),
    NoDup (rev l) <-> NoDup l.
(* begin hide *)
Proof.
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

Lemma Incl_rev :
  forall (A : Type) (l : list A), Incl (rev l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. rewrite <- elem_rev. assumption.
Qed.
(* end hide *)

(* begin hide *)
Inductive Palindrome {A : Type} : list A -> Prop :=
    | Palindrome_nil : Palindrome []
    | Palindrome_singl :
        forall x : A, Palindrome [x]
    | Palindrome_1 :
        forall (x : A) (l : list A),
          Palindrome l -> Palindrome (x :: snoc x l).
(* end hide *)

(* begin hide *)

Lemma Palindrome_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (x :: snoc x l).
(* begin hide *)
Proof.
  constructor. assumption.
Qed.
(* end hide *)

Lemma Palindrome_rev :
  forall (A : Type) (l : list A),
    Palindrome l <-> Palindrome (rev l).
(* begin hide *)
Proof.
  intro. assert (forall l : list A, Palindrome l -> Palindrome (rev l)).
    induction 1; cbn.
      1-2: constructor.
      rewrite rev_snoc. constructor. assumption.
    split; intro.
      apply H, H0.
      rewrite <- rev_rev. apply H, H0.
Qed.
(* end hide *)

Lemma Palindrome_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    Palindrome l -> Palindrome (map f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    1-2: constructor.
    rewrite map_snoc. constructor. assumption.
Qed.
(* end hide *)

Lemma snoc_inj :
  forall (A : Type) (x : A) (l1 l2 : list A),
    snoc x l1 = snoc x l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; destruct l2 as [| h2 t2]; cbn; intros.
    reflexivity.
    apply (f_equal length) in H. cbn in H. rewrite length_snoc in H. inv H.
    inv H. destruct t; inv H2.
    inv H. f_equal. apply IHt. assumption.
Qed.
(* end hide *)

(* Palindromowa indukcja *)
Lemma list_palindrome_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall x : A, P [x]) ->
    (forall (x y : A) (l : list A), P l -> P (x :: snoc y l)) ->
      forall l : list A, P l.
Proof.
  fix IH 6. destruct l as [| h t].
    assumption.
    destruct (init_decomposition A t); subst.
      apply H0.
      destruct H2 as (h' & t' & H1' & H2' & H3'). rewrite H3'.
        rewrite <- snoc_app_singl. apply H1. apply IH; assumption.
Admitted.
(* end hide *)

Lemma Palindrome_spec :
  forall (A : Type) (l : list A),
    Palindrome l <-> l = rev l.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      1-2: reflexivity.
      rewrite rev_snoc, <- IHPalindrome; cbn. reflexivity.
    induction l as [| x | x y l'] using list_palindrome_ind; cbn; intros.
      1-2: constructor.
      rewrite rev_snoc in H. cbn in H. inv H.
        constructor. apply IHl'. apply snoc_inj in H2. assumption.
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
      rewrite pmap_snoc. rewrite Heq. constructor. assumption.
      rewrite pmap_snoc. rewrite Heq. assumption.
Qed.
(* end hide *)