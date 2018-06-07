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
    match remove n l1, remove n l2 with
        | None, None => None
        | None, Some (h, t) => Some (h, l1 ++ t)
        | Some (h, t), _ => Some (h, t ++ l2)
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (remove n l2); try destruct p; reflexivity.
    destruct (remove n l2).
      destruct n as [| n']; cbn.
        reflexivity.
        rewrite IHt. destruct (remove n' t).
          destruct p0. reflexivity.
          destruct (remove n' l2).
            destruct p0, p.
Abort.
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
      match remove n l2 with
          | None => None
          | Some (h, t) => Some (h, l1 ++ t)
      end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (remove n l2).
      destruct p. 1-2: reflexivity.
    destruct n as [| n'].
      inversion H.
      apply le_S_n in H. rewrite (IHt _ _ H).
        destruct (remove n' l2).
          destruct p.
Abort.
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
    destruct (remove (n - length l1) l2). cbn. reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma remove_rev :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      remove n (rev l) =
      let '(x, l') := remove (length l - S n) l in (x, rev l').
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      destruct t.
        cbn. reflexivity.
        rewrite remove_app_lt. cbn in *.
          specialize (IHt 0 ltac:(omega)). rewrite <- minus_n_O in IHt.
          match goal with
              | H : context [let '(_, _) := ?x in _] |- _ => destruct x
          end.
          rewrite IHt. cbn. reflexivity.
        cbn. rewrite length_app, plus_comm. cbn. omega.
      apply lt_S_n in H. rewrite remove_app_lt.
Abort.
(* end hide *)

Lemma remove_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    remove n (map f l) =
    match remove n l with
        | (None, l) => (None, map f l)
        | (Some x, l') => (Some (f x), map f l')
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      reflexivity.
      rewrite IHt. destruct (remove n' t), o; cbn.
        1-2: reflexivity.
Qed.
(* end hide *)

Lemma remove_replicate :
  forall (A : Type) (n m : nat) (x : A),
    n < m -> remove n (replicate m x) = (Some x, replicate (m - 1) x).
(* begin hide *)
Proof.
  intros A n m. revert n.
  induction m as [| m']; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      rewrite <- minus_n_O. reflexivity.
      apply lt_S_n in H. rewrite (IHm' _ _ H). destruct m'.
        destruct n'; inversion H.
        cbn. rewrite <- minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma remove_nth_take_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x <->
    remove n l = (Some x, take n l ++ drop (S n) l).
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
          inversion H; subst; clear H. destruct t; cbn; reflexivity.
Qed.
(* end hide *)

Lemma remove_filter :
  forall (A : Type) (p : A -> bool) (l l' : list A) (x : A) (n : nat),
    remove n (filter p l) = (Some x, l') ->
      exists m : nat,
      match remove m l with
          | (None, _) => False
          | (Some y, l'') => x = y /\ l' = filter p l''
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h) eqn: Hph.
      destruct n as [| n']; cbn in *.
        inversion H; subst; clear H. exists 0. split; reflexivity.
        destruct (remove n' (filter p t)) eqn: Heq.
          inversion H; subst; clear H. destruct (IHt _ _ _ Heq) as [m IH].
          exists (S m). destruct (remove m t), o.
            destruct IH. cbn. rewrite Hph, H0. split; trivial.
            assumption.
      destruct (IHt _ _ _ H) as [m IH], (remove m t) eqn: Heq, o.
        exists (S m). destruct IH. rewrite Heq. cbn. rewrite H0, Hph.
          split; trivial.
        contradiction.
Qed.
(* end hide *)

Lemma remove_zip :
  forall (A B : Type) (la : list A) (lb : list B) (n : nat),
    remove n (zip la lb) =
    match remove n la, remove n lb with
        | (Some a, la'), (Some b, lb') => (Some (a, b), zip la' lb')
        | _, _ => (None, zip la lb)
    end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (remove n' ta), o; reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (remove n' ta), (remove n' tb), o, o0;
          cbn; reflexivity.
Qed.
(* end hide *)

Lemma remove_zipWith :
  forall (A B C : Type) (f : A -> B -> C)
    (la : list A) (lb : list B) (n : nat),
      remove n (zipWith f la lb) =
      match remove n la, remove n lb with
          | (Some a, la'), (Some b, lb') =>
              (Some (f a b), zipWith f la' lb')
          | _, _ => (None, zipWith f la lb)
      end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (remove n' ta), o; reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (remove n' ta), (remove n' tb), o, o0;
          cbn; reflexivity.
Qed.
(* end hide *)

Lemma elem_remove_nth :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    elem x l -> nth n l <> Some x ->
      let '(_, l') := remove n l in elem x l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in *.
      inversion H; subst; clear H.
        contradiction H0. reflexivity.
        assumption.
      inversion H; subst; clear H.
        destruct (remove n' t). left.
        specialize (IHt _ H3 H0). destruct (remove n' t). right. assumption.
Qed.
(* end hide *)

Lemma Forall_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P l ->
    match remove n l with
        | (None, l') => Forall P l'
        | (Some x, l') => P x /\ Forall P l'
    end.
(* begin hide *)
Proof.
  intros A P l n H. revert n.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n'].
      split; assumption.
      specialize (IHForall n'). destruct (remove n' t), o.
        destruct IHForall. split; try constructor; assumption.
        constructor; assumption.
Qed.
(* end hide *)

Lemma Exists_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P l ->
    match remove n l with
        | (None, l') => Exists P l'
        | (Some x, l') => ~ P x -> Exists P l'
    end.
(* begin hide *)
Proof.
  intros A P l n H. revert n.
  induction H; cbn; intros.
    destruct n as [| n'].
      intro. contradiction.
      destruct (remove n' t), o; constructor; assumption.
    destruct n as [| n'].
      intro. assumption.
      specialize (IHExists n'). destruct (remove n' t), o.
        intro. right. apply IHExists, H0.
        right. assumption.
Qed.
(* end hide *)

Lemma AtLeast_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (m : nat),
    AtLeast P m l -> forall n : nat, AtLeast P (m - 1) (remove' n l).
(* begin hide *)
Proof.
  induction 1; cbn; intro m.
    constructor.
    rewrite <- minus_n_O. destruct n as [| n'].
      constructor.
      destruct m as [| m']; cbn in *.
        assumption.
        rewrite remove'_S_cons. constructor.
          assumption.
          rewrite <- minus_n_O in IHAtLeast. apply IHAtLeast.
    destruct n as [| n']; cbn.
      constructor.
      rewrite <- minus_n_O. destruct m as [| m']; cbn in *.
        apply (AtLeast_le _ _ (S n') n').
          assumption.
          apply le_S, le_n.
        rewrite remove'_S_cons. rewrite <- minus_n_O in IHAtLeast.
          constructor. apply IHAtLeast.
Qed.
(* end hide *)

Lemma incl_remove :
  forall (A : Type) (l : list A) (n : nat),
    let '(_, l') := remove n l in incl l' l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply incl_refl.
    destruct n as [| n'].
      apply incl_cons'.
      specialize (IHt n'). destruct (remove n' t). apply incl_cons, IHt.
Qed.
(* end hide *)
