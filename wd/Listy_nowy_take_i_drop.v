Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(* begin hide *)
Fixpoint take {A : Type} (n : nat) (l : list A) {struct l} : list A :=
match l, n with
    | [], _ => []
    | _, 0 => []
    | h :: t, S n' => h :: take n' t
end.

Fixpoint drop {A : Type} (n : nat) (l : list A) {struct l} : list A :=
match l, n with
    | [], _ => []
    | _, 0 => l
    | h :: t, S n' => drop n' t
end.

Require Import Arith.

Lemma isEmpty_take :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty (take n l) = orb (beq_nat 0 n) (isEmpty l).
(* begin hide *)
Proof.
  destruct n as [| n'], l as [| h t]; cbn; intros; trivial.
Qed.
(* end hide *)

Lemma isEmpty_drop :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty (drop n l) = leb (length l) n.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn.
    1-3: reflexivity.
    apply IHt.
Qed.
(* end hide *)

Lemma take_nil :
  forall (A : Type) (n : nat),
    take n [] = @nil A.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma drop_nil :
  forall (A : Type) (n : nat),
    drop n [] = @nil A.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma take_cons :
  forall (A : Type) (n : nat) (h : A) (t : list A),
    take (S n) (h :: t) = h :: take n t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma drop_cons :
  forall (A : Type) (n : nat) (h : A) (t : list A),
    drop (S n) (h :: t) = drop n t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma take_0 :
  forall (A : Type) (l : list A),
    take 0 l = [].
(* begin hide *)
Proof. destruct l; reflexivity. Qed.
(* end hide *)

Lemma drop_0 :
  forall (A : Type) (l : list A),
    drop 0 l = l.
(* begin hide *)
Proof. destruct l; reflexivity. Qed.
(* end hide *)

Lemma take_length :
  forall (A : Type) (l : list A),
    take (length l) l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma take_length' :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> take n l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inversion H.
      apply le_S_n in H. rewrite (IHt _ H). reflexivity.
Qed.
(* end hide *)

Lemma drop_length :
  forall (A : Type) (l : list A),
    drop (length l) l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma drop_length' :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> drop n l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    1-2: reflexivity.
    inversion H.
    apply IHt, le_S_n. assumption.
Qed.
(* end hide *)

Lemma length_take :
  forall (A : Type) (l : list A) (n : nat),
    length (take n l) = min (length l) n.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma length_drop :
  forall (A : Type) (l : list A) (n : nat),
    length (drop n l) = length l - n.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma take_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    take n (map f l) = map f (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma drop_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    drop n (map f l) = map f (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma take_take_min :
  forall (A : Type) (l : list A) (n m : nat),
    take m (take n l) = take (min n m) l.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n, m; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma take_take_comm :
  forall (A : Type) (n m : nat) (l : list A),
    take m (take n l) = take n (take m l).
(* begin hide *)
Proof.
  intros. rewrite !take_take_min, Nat.min_comm. reflexivity.
Qed.
(* end hide *) 

Lemma drop_drop_plus :
  forall (A : Type) (l : list A) (n m : nat),
    drop m (drop n l) = drop (n + m) l.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n, m; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma drop_S_drop :
  forall (A : Type) (n m : nat) (l : list A),
    drop (S m) (drop n l) = drop m (drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite ?drop_drop_plus. rewrite <- plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma drop_drop_comm :
  forall (A : Type) (n m : nat) (l : list A),
    drop m (drop n l) = drop n (drop m l).
(* begin hide *)
Proof.
  intros. rewrite !drop_drop_plus. f_equal. apply plus_comm.
Qed.
(* end hide *)

Lemma take_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    take n (l1 ++ l2) = take n l1 ++ take (n - length l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; destruct n; cbn;
  rewrite ?IHt, ?take_0; reflexivity.
Qed.
(* end hide *)

Lemma take_app_l :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n <= length l1 -> take n (l1 ++ l2) = take n l1.
(* begin hide *)
Proof.
  induction l1 as [| h t]; destruct n; cbn; rewrite ?take_0.
    1,3: reflexivity.
    inversion 1.
    intro. apply le_S_n in H. rewrite (IHt _ _ H). reflexivity.
Qed.
(* end hide *)

(*Lemma take_app_r :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 < n ->
      take n (l1 ++ l2) = l1 ++ take (n - length l1) l2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H.
    destruct l1; cbn.
      reflexivity.
      rewrite IHn'.
        reflexivity.
        apply lt_S_n. assumption.
Qed.
(* end hide *)
*)

Lemma drop_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    drop n (l1 ++ l2) = drop n l1 ++ drop (n - length l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; destruct n; cbn;
  rewrite ?IHt, ?drop_0; reflexivity.
Qed.
(* end hide *)

Lemma drop_app_l :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n <= length l1 -> drop n (l1 ++ l2) = drop n l1 ++ l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    inversion H. rewrite drop_0. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      apply le_S_n in H. apply (IHt _ _ H).
Restart.
  intros. rewrite drop_app. rewrite <- Nat.sub_0_le in H.
  rewrite H, drop_0. reflexivity.
Qed.
(* end hide *)

Lemma drop_app_r :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 < n -> drop n (l1 ++ l2) = drop (n - length l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. reflexivity.
    destruct n as [| n']; cbn.
      inversion H.
      apply lt_S_n in H. apply (IHt _ _ H).
Qed.
(* end hide *)

(* begin hide *)
Lemma take_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    take n l = rev (drop (length (rev l) - n) (rev l)).
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt.
    1-2: reflexivity.
    rewrite drop_app, ?length_app, ?length_rev, <- ?minus_n_O.
      cbn. rewrite drop_length'.
        rewrite plus_comm. rewrite Nat.add_sub. reflexivity.
        rewrite length_rev, plus_comm. apply le_S. reflexivity.
    rewrite drop_app, ?length_app, ?length_rev. rewrite plus_comm.
      cbn. rewrite <- Nat.sub_add_distr. rewrite plus_comm.
      rewrite Nat.sub_add_distr. rewrite Nat.sub_diag. cbn.
      rewrite rev_app. cbn. reflexivity.
Restart.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite <- minus_n_O. rewrite drop_length. cbn. reflexivity.
      rewrite IHt, length_app, plus_comm. cbn. rewrite drop_app_l.
        rewrite rev_app. cbn. reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma take_rev :
  forall (A : Type) (l : list A) (n : nat),
    take n (rev l) = rev (drop (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_inv. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma drop_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    drop n l = rev (take (length (rev l) - n) (rev l)).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite <- minus_n_O, take_length, rev_app, rev_inv. cbn. reflexivity.
      rewrite IHt, length_app, plus_comm. cbn. rewrite take_app_l.
        reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma drop_rev :
  forall (A : Type) (l : list A) (n : nat),
    drop n (rev l) = rev (take (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite drop_rev_aux, !rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma take_drop :
  forall (A : Type) (l : list A) (n m : nat),
    take m (drop n l) = drop n (take (n + m) l).
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n, m; cbn;
  rewrite ?IHt, ?take_0; reflexivity.
Qed.
(* end hide *)

Lemma take_replicate :
  forall (A : Type) (n m : nat) (x : A),
    take m (replicate n x) = replicate (min n m) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma drop_replicate :
  forall (A : Type) (n m : nat) (x : A),
    drop m (replicate n x) = replicate (n - m) x.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

(*
Lemma removeFirst_take' :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A) (l l' : list A),
    removeFirst p (take' n l) = Some (x, l') ->
      removeFirst p l = Some (x, l' ++ drop n l).
Proof.
  intros A p n x l. revert n x.
  functional induction @removeFirst A p l;
  destruct n as [| n']; cbn; intros; inv H; rewrite e0 in H1; inv H1.
    admit.
    destruct (removeFirst p (take' n' t)) eqn: Heq.
      admit.
      inv H0.
    destruct (removeFirst p (take' n' t)) eqn: Heq.
      destruct p0. inv H0. rewrite (IHo _ _ _ Heq) in e1. inv e1.
        cbn. reflexivity.
      inv H0.
Admitted.
(* end hide *)

*)