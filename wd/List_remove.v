Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(** ** [remove] *)

(** Czemu [remove] ma taki dziwny typ? *)

Fixpoint remove
  {A : Type} (n : nat) (l : list A) {struct l} : option (A * list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some (h, t)
    | h :: t, S n' =>
        match remove n' t with
            | None => None
            | Some (x, l') => Some (x, h :: l')
        end
end.

Definition remove'
  {A : Type} (n : nat) (l : list A) : list A :=
match remove n l with
    | None => l
    | Some (_, l') => l'
end.

Definition remove''
  {A : Type} (n : nat) (l : list A) : option (list A) :=
match remove n l with
    | None => None
    | Some (_, l') => Some l'
end.

Lemma remove'_S_cons :
  forall (A : Type) (n : nat) (h : A) (t : list A),
    remove' (S n) (h :: t) = h :: remove' n t.
(* begin hide *)
Proof.
  intros. unfold remove'. cbn. destruct (remove n t).
    destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_isEmpty_true :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty l = true -> remove n l = None.
(* begin hide *)
Proof.
  destruct l.
    reflexivity.
    inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_remove_not_None :
  forall (A : Type) (l : list A) (n : nat),
    remove n l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma length_remove :
  forall (A : Type) (h : A) (l t : list A) (n : nat),
    remove n l = Some (h, t) -> length l = S (length t).
(* begin hide *)
Proof.
  induction l as [| h' t']; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H; subst. reflexivity.
      destruct (remove n' t') eqn: Heq.
        destruct p. inversion H; subst. cbn.
          rewrite (IHt' _ _ Heq). reflexivity.
        inversion H.
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
  induction l as [| h t]; cbn.
    destruct n; inversion 1.
    destruct n as [| n']; cbn; intros.
      reflexivity. Require Import Arith.
      apply lt_S_n in H. rewrite (IHt _ H). destruct (remove n' t).
        destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_length_ge :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> remove n l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inversion H.
      apply le_S_n in H. rewrite (IHt _ H). reflexivity.
Qed.
(* end hide *)

Lemma remove_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    remove n (l1 ++ l2) =
    match remove n l1 with
        | Some (h, t) => Some (h, t ++ l2)
        | None =>
            match remove (n - length l1) l2 with
                | Some (h, t) => Some (h, l1 ++ t)
                | None => None
            end
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (remove n l2).
      destruct p. 1-2: reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (remove n' t).
        destruct p. reflexivity.
        destruct (remove (n' - length t) l2).
          destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_app_lt :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n < length l1 ->
      remove n (l1 ++ l2) =
      match remove n l1 with
          | None => None
          | Some (h, t) => Some (h, t ++ l2)
      end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      reflexivity.
      apply lt_S_n in H. rewrite (IHt _ _ H).
        destruct (remove n' t).
          destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_app_ge :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 <= n ->
      remove n (l1 ++ l2) =
      match remove (n - length l1) l2 with
          | None => None
          | Some (h, t) => Some (h, l1 ++ t)
      end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (remove n l2).
      destruct p. 1-2: reflexivity.
    destruct n as [| n'].
      inversion H.
      apply le_S_n in H. rewrite (IHt _ _ H).
        destruct (remove (n' - length t) l2) eqn: Heq; cbn; rewrite Heq.
          destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove'_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    n < length l1 ->
      remove' n (l1 ++ l2) = remove' n l1 ++ l2.
(* begin hide *)
Proof.
  intros. unfold remove'. rewrite remove_app_lt.
    destruct (remove n l1).
      destruct p. 1-2: reflexivity.
    assumption.
Qed.
(* end hide *)


Lemma remove_app' :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 <= n ->
      remove' n (l1 ++ l2) = l1 ++ remove' (n - length l1) l2.
(* begin hide *)
Proof.
  intros. unfold remove'. rewrite remove_app_ge.
    destruct (remove (n - length l1) l2).
      destruct p. 1-2: reflexivity.
    assumption.
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
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      destruct t.
        cbn. reflexivity.
        rewrite remove_app_lt. cbn in *.
          rewrite (IHt 0), <- minus_n_O.
            destruct (length t); cbn.
              reflexivity.
              destruct (remove n t).
                destruct p; cbn. 1-2: reflexivity.
            apply le_n_S, le_0_n.
          rewrite length_rev; cbn. apply le_n_S, le_0_n.
      destruct (rev t) eqn: Heq; cbn.
        apply (f_equal rev) in Heq. rewrite rev_inv in Heq.
          rewrite Heq in H. cbn in H. apply lt_S_n in H.
          destruct n'; inversion H.
Abort.
(* end hide *)

Lemma remove_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    remove n (map f l) =
    match remove n l with
        | None => None
        | Some (x, l') => Some (f x, map f l')
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      reflexivity.
      rewrite IHt. destruct (remove n' t).
        destruct p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma remove_replicate :
  forall (A : Type) (n m : nat) (x : A),
    m < n -> remove m (replicate n x) = Some (x, replicate (n - 1) x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct m; inversion H.
    destruct m as [| m'].
      rewrite <- minus_n_O. reflexivity.
      apply lt_S_n in H. rewrite (IHn' _ _ H). destruct n'; cbn.
        destruct m'; inversion H.
        rewrite <- minus_n_O. reflexivity.
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
      rewrite nth_nil in H. inversion H.
      destruct n as [| n']; cbn in *.
        inversion H; subst. reflexivity.
        rewrite (IHt _ _ H). reflexivity.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct n as [| n'].
        inversion H; subst; clear H. cbn. reflexivity.
        cbn. apply IHt. destruct (remove n' t).
          destruct p. inversion H; subst; clear H.
            destruct t; cbn; reflexivity.
          inversion H.
Qed.
(* end hide *)

Lemma remove_filter :
  forall (A : Type) (p : A -> bool) (l l' : list A) (x : A) (n : nat),
    remove n (filter p l) = Some (x, l') ->
      exists m : nat,
      match remove m l with
          | None => False
          | Some (y, l'') => x = y /\ l' = filter p l''
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h) eqn: Hph.
      destruct n as [| n']; cbn in *.
        inversion H; subst; clear H. exists 0. split; reflexivity.
        destruct (remove n' (filter p t)) eqn: Heq.
          destruct p0. inversion H; subst; clear H.
            destruct (IHt _ _ _ Heq) as [m IH].
              exists (S m). destruct (remove m t).
                destruct p0, IH. cbn. rewrite Hph, H0. split; trivial.
                assumption.
          inversion H.
      destruct (IHt _ _ _ H) as (m & IH). exists (S m).
        destruct (remove m t).
          destruct p0. cbn. rewrite Hph. assumption.
          assumption.
Qed.
(* end hide *)

Lemma remove_zip :
  forall (A B : Type) (la : list A) (lb : list B) (n : nat),
    remove n (zip la lb) =
    match remove n la, remove n lb with
        | Some (a, la'), Some (b, lb') => Some ((a, b), zip la' lb')
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (remove n' ta); try destruct p; reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (remove n' ta), (remove n' tb);
          try destruct p; try destruct p0; cbn; reflexivity.
Qed.
(* end hide *)

Lemma remove_zipWith :
  forall (A B C : Type) (f : A -> B -> C)
    (la : list A) (lb : list B) (n : nat),
      remove n (zipWith f la lb) =
      match remove n la, remove n lb with
          | Some (a, la'), Some (b, lb') =>
              Some (f a b, zipWith f la' lb')
          | _, _ => None
      end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (remove n' ta); try destruct p; reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (remove n' ta), (remove n' tb);
          try destruct p; try destruct p0; cbn; reflexivity.
Qed.
(* end hide *)

Lemma elem_remove_nth :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    elem x l -> nth n l <> Some x ->
    match remove n l with
        | None => True
        | Some (_, l') =>  elem x l'
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n']; cbn in *.
      inversion H; subst; clear H.
        contradiction H0. reflexivity.
        assumption.
      inversion H; subst; clear H.
        destruct (remove n' t).
          destruct p. left.
          trivial.
        specialize (IHt _ H3 H0). destruct (remove n' t).
          destruct p. right. assumption.
          trivial.
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
      rewrite <- minus_n_O. assumption.
      specialize (IHAtLeast m'). destruct (remove m' t).
        destruct p. destruct n as [| n']; cbn in *.
          constructor.
          rewrite <- minus_n_O in *. constructor; assumption.
        trivial.
    destruct m as [| m']; cbn in *.
      apply AtLeast_le with n.
        assumption.
        destruct n as [| n']; cbn.
          apply le_n.
          rewrite <- minus_n_O. apply le_S, le_n.
      specialize (IHAtLeast m'). destruct (remove m' t).
        destruct p. constructor. assumption.
        trivial.
Qed.
(* end hide *)

Lemma incl_remove :
  forall (A : Type) (l : list A) (n : nat),
    match remove n l with
        | None => True
        | Some (_, l') => incl l' l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      apply incl_cons'.
      specialize (IHt n'). destruct (remove n' t).
        destruct p. apply incl_cons, IHt.
        trivial.
Qed.
(* end hide *)