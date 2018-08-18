Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(*Require Import CoqBookPL.wd.Option.*)

(* begin hide *)
Fixpoint replace
  {A : Type} (l : list A) (n : nat) (x : A) : option (list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some (x :: t)
    | h :: t, S n' =>
        match replace t n' x with
            | None => None
            | Some l => Some (h :: l)
        end
end.
(* end hide *)

Lemma isEmpty_replace_Some :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      isEmpty l' = isEmpty l.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    inversion H.
    destruct n; cbn in *.
      inversion H. cbn. reflexivity.
      destruct (replace l n x); inversion H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma length_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> length l' = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inversion H. cbn. rewrite (IHt _ _ _ Heq). reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma replace_length :
  forall (A : Type) (l : list A) (x : A),
    replace l (length l) x = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma replace_length_lt :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      exists l' : list A, replace l n x = Some l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      exists (x :: t). reflexivity.
      destruct (IHt _ x (lt_S_n _ _ H)) as [l' IH].
        exists (h :: l'). rewrite IH. reflexivity.
Qed.
(* end hide *)

Lemma replace_length_ge :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    length l <= n -> replace l n x = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inversion H.
      rewrite (IHt _ _ (le_S_n _ _ H)). reflexivity.
Qed.
(* end hide *)

Lemma replace_snoc_eq :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    n = length l -> replace (snoc x l) n y = Some (snoc y l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite H. reflexivity.
    destruct n as [| n']; cbn.
      inversion H.
      apply eq_add_S in H. rewrite IHt.
        reflexivity.
        assumption.
Qed.
(* end hide *)

(*Require Import CoqBookPL.wd.Opcje.*)

Lemma replace_snoc_neq :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    n <> length l ->
      replace (snoc x l) n y =
      match replace l n y with
          | None => None
          | Some l' => Some (snoc x l')
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    contradiction H. 1-3: reflexivity.
    Search (S _ <> _).
    rewrite Nat.succ_inj_wd_neg in H. rewrite (IHt _ _ _ H).
      destruct (replace t n' y); reflexivity.
Qed.
(* end hide *)

Lemma replace_snoc :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    replace (snoc x l) n y =
    if beq_nat n (length l)
    then Some (snoc y l)
    else
      match replace l n y with
          | None => None
          | Some l' => Some (snoc x l')
      end.
(* begin hide *)
Proof.
  intros. destruct (n =? length l) eqn: Heq.
    apply beq_nat_true in Heq. rewrite Heq.
      apply replace_snoc_eq. reflexivity.
    apply beq_nat_false in Heq.
      apply replace_snoc_neq. assumption.
Qed.
(* end hide *)

Lemma replace_app :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    replace (l1 ++ l2) n x =
    match replace l1 n x, replace l2 (n - length l1) x with
        | None, None => None
        | Some l', _ => Some (l' ++ l2)
        | _, Some l' => Some (l1 ++ l')
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (replace l2 n x); reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (replace t n' x); cbn.
        reflexivity.
        destruct (replace l2 (n' - length t) x); reflexivity.
Qed.
(* end hide *)

Lemma replace_spec :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    replace l n x =
    if S n <=? length l
    then Some (take n l ++ x :: drop (S n) l)
    else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (length t); cbn.
        reflexivity.
        destruct (n' <=? n); reflexivity.
Qed.
(* end hide *)

Lemma replace_spec' :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      replace l n x = Some (take n l ++ x :: drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec.
  apply leb_correct in H. rewrite H. reflexivity.
Qed.
(* end hide *)

Lemma replace_rev_aux :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      replace l n x =
      match replace (rev l) (length l - S n) x with
          | None => None
          | Some l' => Some (rev l')
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite <- snoc_app_singl, <- minus_n_O, replace_snoc,
        length_rev, <- beq_nat_refl, rev_snoc, rev_inv. reflexivity.
      rewrite replace_app, (IHt _ _ (lt_S_n _ _ H)).
        destruct (replace (rev t) (length t - S n') x) eqn: Heq.
          rewrite rev_app. cbn. reflexivity.
          rewrite replace_spec' in Heq.
            inv Heq.
            rewrite length_rev. unfold lt. omega.
Qed.
(* end hide *)

Definition omap {A B: Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Lemma replace_rev :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    n < length l ->
      replace (rev l) n x = omap rev (replace l (length l - S n) x).
(* begin hide *)
Proof.
  intros. rewrite (replace_rev_aux _ (rev l));
  rewrite ?rev_inv, length_rev.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma map_replace :
  forall (A B : Type) (f : A -> B) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Some (map f l') = replace (map f l) n (f x).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq.
        rewrite <- (IHt _ _ _ Heq). inv H. cbn. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma replace_join :
  forall (A : Type) (ll : list (list A)) (n : nat) (x : A) (l : list A),
    replace (join ll) n x = Some l ->
      exists n m : nat,
        match nth n ll with
            | None => False
            | Some l' =>
                match replace l' m x with
                    | None => False
                    | Some l'' =>
                        match replace ll n l'' with
                            | None => False
                            | Some ll' => join ll' = l
                        end
                end
        end.
(* begin hide *)
Proof.
  induction ll as [| hl tl]; cbn; intros.
    inv H.
    rewrite replace_app in H. destruct (replace hl n x) eqn: Heq.
      inv H. exists 0. cbn. exists n. rewrite Heq. reflexivity.
      destruct (replace (join tl) (n - length hl) x) eqn: Heq'; inv H.
        destruct (IHtl _ _ _ Heq') as (n' & m & IH).
          exists (S n'), m. cbn. destruct (nth n' tl).
            destruct (replace l m x).
              destruct (replace tl n' l1).
                cbn. rewrite IH. reflexivity.
                contradiction.
              contradiction.
            contradiction.
Qed.
(* end hide *)

(* TODO: bind *)

Lemma replace_replicate :
  forall (A : Type) (l l' : list A) (n m : nat) (x y : A),
    replace (replicate n x) m y =
    if n <=? m
    then None
    else Some (replicate m x ++ y :: replicate (n - S m) x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. destruct (n' <=? m'); reflexivity.
Qed.
(* end hide *)

Lemma replace_iterate :
  forall (A : Type) (f : A -> A) (l : list A) (n m : nat) (x y : A),
    replace (iterate f n x) m y =
    if n <=? m
    then None
    else Some (iterate f m x ++
               y :: iterate f (n - S m) (iter f (S m) x)).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. destruct (n' <=? m'); reflexivity.
Qed.
(* end hide *)

Lemma head_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    replace l n x = Some l' ->
      head l' =
      match n with
          | 0 => Some x
          | _ => head l
      end.
(* begin hide *)
Proof.
  destruct l, n; cbn; intros; inv H.
    cbn. reflexivity.
    destruct (replace l n x); inv H1. cbn. reflexivity.
Qed.
(* end hide *)

Lemma tail_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      tail l' =
      match n with
          | 0 => tail l
          | S n' =>
              match tail l with
                  | None => None
                  | Some t => replace t n' x
              end
      end.
(* begin hide *)
Proof.
  destruct l, n; cbn; intros; inv H.
    cbn. reflexivity.
    destruct (replace l n x); inv H1. cbn. reflexivity.
Qed.
(* end hide *)

Lemma nth_replace :
  forall (A : Type) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' ->
      nth m l' =
      if n =? m then Some x else nth m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct m as [| m']; reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. destruct m as [| m']; cbn.
          reflexivity.
          apply IHt. assumption.
        inv H.
Qed.
(* end hide *)

Lemma replace_length_aux :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> length l = length l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H.
        cbn. f_equal. apply (IHt _ _ _ Heq).
Qed.
(* end hide *)

Lemma last_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      last l' =
      if n =? length l - 1
      then Some x
      else last l.
(* begin hide *)
Proof.
  intros. rewrite (last_nth A l).
  rewrite <- (nth_replace A l l').
    rewrite last_nth. do 2 f_equal.
      apply replace_length_aux in H. rewrite H. reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma init_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      init l' =
      if n =? length l - 1
      then init l
      else
        match init l with
            | None => None
            | Some i => replace i n x
        end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    rewrite <- minus_n_O. destruct (n =? length t) eqn: Heq.
      apply beq_nat_true in Heq. subst. destruct t; cbn in *.
        inv H.
Abort.
(* end hide *)

(* TODO: uncons, unsnoc *)

(*
Lemma replace_insert :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    match insert l n x with
        | None => True
        | Some l' => replace l' n y = insert l n y
    end.
(* begin hide *)
Proof.
Abort.
(* end hide *)
*)

Lemma take_replace :
  forall (A : Type) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' ->
      take m l' =
      if m <=? n
      then take m l
      else take n l ++ x :: take (m - S n) (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct m; cbn.
        reflexivity.
        rewrite <- minus_n_O. reflexivity.
      destruct m as [| m']; cbn.
        reflexivity.
        destruct (replace t n' x) eqn: Heq; inv H.
          rewrite (IHt _ _ _ _ Heq). destruct (m' <=? n'); reflexivity.
Qed.
(* end hide *)

Lemma drop_replace :
  forall (A : Type) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' ->
      drop m l' =
      if n <? m
      then drop m l
      else take (n - m) (drop m l) ++ x :: drop (S n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct m as [| m']; reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H.
        destruct m as [| m']; cbn.
          specialize (IHt _ n' 0 _ Heq). cbn in IHt.
            rewrite IHt, <- minus_n_O. reflexivity.
          rewrite (IHt _ _ _ _ Heq). destruct m' as [| m']; cbn.
            reflexivity.
            destruct (n' <=? m'); cbn; reflexivity.
Qed.
(* end hide *)

(* TODO: w drugą stronę dla [take] i [drop] *)

(* TODO: splitAt *)

Lemma replace_zip :
  forall
    (A B : Type) (la la' : list A) (lb lb' : list B)
    (n : nat) (a : A) (b : B),
      replace la n a = Some la' ->
      replace lb n b = Some lb' ->
        replace (zip la lb) n (a, b) = Some (zip la' lb').
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct lb; inv H0. cbn. reflexivity.
      destruct (replace ta n' a) eqn: Heqa; inv H.
        destruct lb as [| hb tb]; cbn in *.
          inv H0.
          destruct (replace tb n' b) eqn: Heqb; inv H0.
            rewrite (IHta _ _ _ _ _ _ Heqa Heqb). reflexivity.
Qed.
(* end hide *)

Lemma replace_zipWith :
  forall
    (A B C : Type) (f : A -> B -> C) (la la' : list A) (lb lb' : list B)
    (n : nat) (a : A) (b : B),
      replace la n a = Some la' ->
      replace lb n b = Some lb' ->
        replace (zipWith f la lb) n (f a b) = Some (zipWith f la' lb').
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct lb; inv H0. cbn. reflexivity.
      destruct (replace ta n' a) eqn: Heqa; inv H.
        destruct lb as [| hb tb]; cbn in *.
          inv H0.
          destruct (replace tb n' b) eqn: Heqb; inv H0.
            rewrite (IHta _ _ _ _ _ _ Heqa Heqb). reflexivity.
Qed.
(* end hide *)

Lemma any_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      any p l' =
      orb (any p (take n l)) (orb (p x) (any p (drop (S n) l))).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H.
        cbn. rewrite (IHt _ _ _ Heq), Bool.orb_assoc. reflexivity.
Qed.
(* end hide *)

Lemma all_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      all p l' =
      andb (all p (take n l)) (andb (p x) (all p (drop (S n) l))).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H.
        cbn. rewrite (IHt _ _ _ Heq), Bool.andb_assoc. reflexivity.
Restart.
  intros. rewrite replace_spec in H.
  destruct (S n <=? length l); inv H.
  rewrite all_app. cbn. reflexivity.
Qed.
(* end hide *)

Lemma find_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      find p l' =
      match find p (take n l), p x with
          | Some y, _ => Some y
          | _, true => Some x
          | _, _ => find p (drop (S n) l)
      end.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (S n <=? length l); inv H.
  rewrite find_app. cbn. reflexivity.
Qed.
(* end hide *)

Lemma replace_findLast :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
    findLast p l' =
    match findLast p (drop (S n) l), p x with
        | Some y, _ => Some y
        | _, true => Some x
        | _, _ => findLast p (take n l)
    end.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (S n <=? length l); inv H.
  rewrite <- find_rev, rev_app, find_app, ?find_rev.
  destruct l; cbn.
    destruct (p x); reflexivity.
    destruct (findLast p (drop n l)), (p x); reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      removeFirst p l' =
      match removeFirst p (take n l), p x, removeFirst p (drop (S n) l) with
          | Some (y, l''), _, _ => Some (y, l'' ++ x :: drop (S n) l)
          | _, true, _ => Some (x, take n l ++ drop (S n) l)
          | _, _, Some (y, l'') => Some (y, take n l ++ x :: l'')
          | _, _, _ => None
      end.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (S n <=? length l); inv H.
  rewrite removeFirst_app. cbn.
    destruct (removeFirst p (take n l)).
      reflexivity.
      destruct (p x).
        reflexivity.
        destruct l; cbn.
          reflexivity.
          destruct (removeFirst p (drop n l)).
            destruct p0. cbn. all: reflexivity.
Qed.
(* end hide *)

Lemma removeLast_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    removeLast p (l1 ++ l2) =
    match removeLast p l2, removeLast p l1 with
        | Some (y, l'), _ => Some (y, l1 ++ l')
        | _, Some (y, l') => Some (y, l' ++ l2)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (removeLast p l2).
      destruct p0. 1-2: reflexivity.
    rewrite IHt. destruct (removeLast p l2) eqn: Heq.
      destruct p0. reflexivity.
      destruct (removeLast p t).
        destruct p0. cbn. reflexivity.
        destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma removeLast_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
    removeLast p l' =
    match removeLast p (drop (S n) l), p x, removeLast p (take n l) with
        | Some (y, l''), _ , _ => Some (y, take n l ++ x :: l'')
        | _, true, _ => Some (x, take n l ++ drop (S n) l)
        | _, _, Some (y, l'') => Some (y, l'' ++ x :: drop (S n) l)
        | _, _, _ => None
    end.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (S n <=? length l); inv H.
  rewrite removeLast_app. cbn. destruct l; cbn.
    destruct (p x); reflexivity.
    destruct (removeLast p (drop n l)); cbn.
      destruct p0. reflexivity.
      destruct (p x); reflexivity.
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

Lemma replace_count :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace_filter :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace_findIndices :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

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

Lemma replace_spec'' :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> l' = take n l ++ x :: drop (S n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      inv H. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H.
        rewrite (IHt _ _ _ Heq). reflexivity.
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

(* TODO: the same stuff for in *)
(*
Lemma Dup_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Dup l' <-> Dup l \/ elem x (take n l) \/ elem x (drop (S n) l).
(* begin hide *)
Proof.
  split; revert l' n x H.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n']; cbn.
        inv H. inv H0.
          do 2 right. assumption.
          left. right. assumption.
        destruct (replace t n' x) eqn: Heq; inv H. inv H0.
          pose (elem_replace A t l n' x h Heq H1). destruct o.
            rewrite <- (app_take_drop A n' t), elem_app in H.
              destruct H.
                right. left.
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)
*)
Definition Classically (A : Type) : Type :=
  (forall P : Prop, P \/ ~ P) -> A.

Notation "f $ x" := (f x) (at level 100, only parsing).

Ltac cls := progress unfold Classically; intro LEM.

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

Lemma replace_eq :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      l = l' <-> nth n l = Some x.
(* begin hide *)
Proof.
  split; revert l' n x H.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. inv H2. cbn. reflexivity.
        destruct (replace t n' x) eqn: Heq; inv H.
          inv H2. cbn. apply (IHt _ _ _ Heq eq_refl).
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n']; cbn in *.
        inv H. inv H0. reflexivity.
        destruct (replace t n' x) eqn: Heq; inv H.
          rewrite (IHt _ _ _ Heq H0). reflexivity.
Qed.
(* end hide *)

(* TODO: sublist, incl (chyba nic ciekawego nie ma) *)

Lemma nth_app_l :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 <= n -> nth n (l1 ++ l2) = nth (n - length l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite <- minus_n_O. reflexivity.
    destruct n as [| n']; cbn.
      inv H.
      apply IHt1, le_S_n, H.
Qed.
(* end hide *)

Lemma replace_Palindrome :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> Palindrome l ->
      Palindrome l' <-> length l = 1 /\ n = 0 \/ nth n l = Some x.
(* begin hide *)
Proof.
  split.
    revert l' n x H. induction H0; cbn; intros.
      inv H.
      destruct n as [| n']; cbn.
        left. split; reflexivity.
        inv H.
      destruct n as [| n']; cbn.
        inv H. inv H1.
          apply (f_equal length) in H3.
            rewrite length_app, plus_comm in H3. cbn in H3. inv H3.
          apply (f_equal last) in H3. rewrite ?last_app in H3.
            cbn in H3. right. symmetry. assumption.
        right. destruct (replace (l ++ [x]) n' x0) eqn: Heq; inv H. inv H1.
          apply length_replace in Heq. rewrite length_app, plus_comm in Heq.
            cbn in Heq. inv Heq.
          destruct (beq_nat n' (length l)) eqn: Heq'.
            apply beq_nat_true in Heq'. subst. rewrite nth_app_l.
              rewrite minus_diag. cbn. rewrite <- snoc_app_singl in Heq.
                rewrite replace_snoc_eq in Heq.
                  inv Heq. rewrite snoc_app_singl in H1.
                    apply (f_equal last) in H1. rewrite ?last_app in H1.
                    inv H1. reflexivity.
                reflexivity.
              reflexivity.
            assert (n' < length l).
              admit.
              rewrite <- snoc_app_singl, replace_snoc_neq in Heq.
                destruct (replace l n' x0) eqn: Heq''.
                  inv Heq. apply (f_equal last) in H3.
                  rewrite snoc_app_singl, ?last_app in H3. inv H3.
Abort.
(* end hide *)