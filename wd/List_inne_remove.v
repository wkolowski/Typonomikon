Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(** ** [remove] *)

Fixpoint remove
  {A : Type} (n : nat) (l : list A) {struct l}
  : option (A * list A * list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some (h, [], t)
    | h :: t, S n' =>
        match remove n' t with
            | None => None
            | Some (x, l1, l2) => Some (x, h :: l1, l2)
        end
end.

Lemma remove_spec :
  forall (A : Type) (l : list A) (n : nat),
    match remove n l with
        | None => length l <= n
        | Some (x, l1, l2) => l = l1 ++ x :: l2
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      reflexivity.
      specialize (IHt n'). destruct (remove n' t).
        destruct p, p. cbn. rewrite <- IHt. reflexivity.
        apply le_n_S. assumption.
Qed.
(* end hide *)

Require Import Arith. 

Lemma remove_isEmpty_true :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty l = true -> remove n l = None.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inversion H.
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

Lemma remove_length_lt :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A,
      remove n l = Some (x, take n l, drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      exists h. reflexivity.
      apply lt_S_n in H. destruct (IHt _ H) as [x IH].
        exists x. rewrite IH. cbn. reflexivity.
Qed.
(* end hide *)

Lemma remove_length_ge :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> remove n l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      inversion H.
      apply le_S_n in H. rewrite (IHt _ H). reflexivity.
Qed.
(* end hide *)

Lemma remove_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    remove n (l1 ++ l2) =
    match remove n l1 with
        | Some (x, l11, l12) => Some (x, l11, l12 ++ l2)
        | None =>
            match remove (n - length l1) l2 with
                | Some (x, l21, l22) => Some (x, l1 ++ l21, l22)
                | None => None
            end
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (remove n l2).
      destruct p, p. 1-2: reflexivity.
    destruct n as [| n'].
      reflexivity.
      rewrite IHt. destruct (remove n' t).
        destruct p, p. reflexivity.
        cbn. destruct (remove (n' - length t) l2).
          destruct p, p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma remove_app_lt :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n < length l1 ->
      remove n (l1 ++ l2) =
      match remove n l1 with
          | None => None
          | Some (x, l11, l12) => Some (x, l11, l12 ++ l2)
      end.
(* begin hide *)
Proof.
  intros. rewrite remove_app.
  destruct (remove_length_lt _ l1 n H).
  rewrite H0. reflexivity.
Qed.
(* end hide *)

Lemma remove_app_ge :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 <= n ->
      remove n (l1 ++ l2) =
      match remove (n - length l1) l2 with
          | None => None
          | Some (x, l21, l22) => Some (x, l1 ++ l21, l22)
      end.
(* begin hide *)
Proof.
  intros. rewrite remove_app, remove_length_ge.
    destruct (remove (n - length l1) l2).
      destruct p, p. 1-2: reflexivity.
    assumption.
Qed.
(* end hide *)

Require Import Omega.

Lemma remove_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      remove n l =
      match remove (length l - S n) (rev l) with
          | None => None
          | Some (x, l1, l2) => Some (x, rev l2, rev l1)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite remove_app, remove_length_ge.
        1-2: rewrite length_rev, <- minus_n_O.
          cbn. rewrite minus_diag, rev_app, rev_inv. cbn. reflexivity.
        reflexivity.
      rewrite IHt, remove_app; clear IHt.
        destruct (remove (length t - S n') (rev t)) eqn: Heq.
          destruct p, p. rewrite rev_app. cbn. reflexivity.
          destruct t; cbn in *.
            omega.
            destruct
              (remove_length_lt A (rev t ++ [a]) (length t - n'))
            as [x H'].
              rewrite length_app, length_rev. cbn. omega.
              congruence.
        apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma remove_rev :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      remove n (rev l) =
      match remove (length l - S n) l with
          | None => None
          | Some (x, l1, l2) => Some (x, rev l2, rev l1)
      end.
(* begin hide *)
Proof.
  intros. rewrite <- length_rev in H.
  rewrite (remove_rev_aux _ _ _ H).
  rewrite length_rev, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma remove_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    remove n (map f l) =
    match remove n l with
        | None => None
        | Some (x, l1, l2) => Some (f x, map f l1, map f l2)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (remove n' t).
        destruct p, p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma remove_replicate :
  forall (A : Type) (n m : nat) (x : A),
    m < n ->
      remove m (replicate n x) =
      Some (x, replicate m x, replicate (n - S m) x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct m; inversion H.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      apply lt_S_n in H. rewrite (IHn' _ _ H). reflexivity.
Qed.
(* end hide *)

Lemma remove_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    m < n ->
      remove m (iterate f n x) =
      Some (iter f m x,
            iterate f m x ++
            (iterate f (n - S m) (iter f (S m) x))).
