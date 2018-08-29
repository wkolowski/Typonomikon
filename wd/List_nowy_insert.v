Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(* begin hide *)
Fixpoint insert
  {A : Type} (l : list A) (n : nat) (x : A) : option (list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some (x :: h :: t)
    | h :: t, S n' =>
        match insert t n' x with
            | None => None
            | Some l => Some (h :: l)
        end
end.
(* end hide *)

Compute insert (iterate S 5 0) 4 42.

(* Trzeba się zastanowić, czy taki insert ma faktycznie sens. *)

Lemma insert_0 :
  forall (A : Type) (l : list A) (x : A),
    insert l 0 x = if isEmpty l then None else Some (x :: l).
(* begin hide *)
Proof.
  destruct l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_insert :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    insert l n x = Some l' -> isEmpty l' = false.
(* begin hide *)
Proof.
  destruct l, n; cbn; intros.
    1-3: inv H. cbn. reflexivity.
    destruct (insert l n x); inv H. cbn. reflexivity.
Qed.
(* end hide *)

(* TODO:

Lemma length_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    length (insert l n x) = S (length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma insert_length :
  forall (A : Type) (l : list A) (x : A),
    insert l (length l) x = snoc x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma insert_snoc :
  forall (A : Type) (l : list A) (x : A),
    insert l (length l) x = snoc x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma insert_app :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    insert (l1 ++ l2) n x =
    if leb n (length l1)
    then insert l1 n x ++ l2
    else l1 ++ insert l2 (n - length l1) x.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct n, l2; reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?IHt. destruct (n' <=? length t); reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma insert_rev_aux :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    insert l n x = rev (insert (rev l) (length l - n) x).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      replace (S (length t)) with (length (rev t ++ [h])).
        rewrite insert_snoc, snoc_app, rev_app, rev_snoc, rev_inv.
          cbn. reflexivity.
        rewrite length_app, length_rev, plus_comm. cbn. reflexivity.
      rewrite ?IHt, insert_app, length_rev.
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
  intros. rewrite insert_rev_aux. rewrite rev_inv, length_rev.
  reflexivity.
Qed.
(* end hide *)

Lemma rev_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    rev (insert l n x) = insert (rev l) (length l - n) x.
(* begin hide *)
Proof.
  intros. pose (insert_rev _ (rev l)).
  rewrite rev_inv in e.
  rewrite e, rev_inv, length_rev. reflexivity.
Qed.
(* end hide *)

Lemma map_insert :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat) (x : A),
    map f (insert l n x) = insert (map f l) n (f x).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

(* TODO: [join], [bind] *)

Lemma insert_replicate :
  forall (A : Type) (n m : nat) (x : A),
    insert (replicate n x) m x = replicate (S n) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

(* TODO: [iterate] *)

Lemma head_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    head (insert l n x) =
    match l, n with
        | [], _ => Some x
        | _, 0 => Some x
        | _, _ => head l
    end.
(* begin hide *)
Proof.
  destruct l, n; reflexivity.
Qed.
(* end hide *)

Lemma tail_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    tail (insert l n x) =
    match l, n with
        | [], _ => Some []
        | _, 0 => Some l
        | h :: t, S n' => Some (insert t n' x)
    end.
(* begin hide *)
Proof.
  destruct l, n; reflexivity.
Qed.
(* end hide *)

Lemma last_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    last (insert l n x) =
    if isEmpty l
    then Some x
    else if leb (S n) (length l) then last l else Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn in *.
      reflexivity.
      specialize (IHt n' x). rewrite ?IHt.
        destruct (insert t n' x) eqn: Heq; cbn in *.
          apply (f_equal isEmpty) in Heq.
            rewrite isEmpty_insert in Heq. inversion Heq.
          destruct t; reflexivity.
Qed.
(* end hide *)

(* TODO: init *)

Lemma nth_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n <= length l -> nth n (insert l n x) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    1,3: reflexivity.
    inversion H.
    apply le_S_n in H. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma nth_insert' :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n (insert l n x) =
    if leb n (length l) then Some x else None.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    1,3: reflexivity.
    rewrite nth_nil. reflexivity.
    apply IHt.
Qed.
(* end hide *)
*)