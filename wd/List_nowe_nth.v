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

(* TODO: nazwy *)
Lemma nth_snoc_lt :
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

Lemma nth_snoc_length :
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

Lemma nth_spec :
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

