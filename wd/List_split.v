Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(* begin hide *)
Fixpoint split
  {A : Type} (l : list A) (n : nat) : option (list A * A * list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some ([], h, t)
    | h :: t, S n' =>
        match split t n' with
            | None => None
            | Some (b, x, e) => Some (h :: b, x, e)
        end
end.
(* end hide *)

Lemma split_spec :
  forall (A : Type) (l : list A) (n : nat),
    match split l n with
        | None => length l <= n
        | Some (b, x, e) => l = b ++ x :: e
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      reflexivity.
      specialize (IHt n'). destruct (split t n').
        destruct p, p. rewrite IHt. cbn. reflexivity.
        apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma split_isEmpty_true :
  forall (A : Type) (l : list A),
    isEmpty l = true -> forall n : nat, split l n = None.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inv H.
Qed.
(* end hide *)

Lemma split_isEmpty_false :
  forall (A : Type) (l : list A) (n : nat),
    split l n <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma split_length :
  forall (A : Type) (l : list A) (n : nat),
    split l n <> None <-> n < length l.
(* begin hide *)
Proof.
  split; revert n.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct n as [| n'].
        apply le_n_S, le_0_n.
        apply lt_n_S, IHt. destruct (split t n'); congruence.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inversion 1.
        destruct (split t n') eqn: Heq.
          destruct p, p. congruence.
          intro. apply (IHt _ (lt_S_n _ _ H)). assumption.
Qed.
(* end hide *)

Lemma split_snoc :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    split (snoc x l) n =
    if n <? length l
    then
      match split l n with
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
          destruct (split t n').
            destruct p, p. 1-2: reflexivity.
            destruct (n' =? S n); reflexivity.
Qed.
(* end hide *)

Lemma split_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    split (l1 ++ l2) n =
    match split l1 n with
        | Some (b, x, e) => Some (b, x, e ++ l2)
        | None =>
            match split l2 (n - length l1) with
                | Some (b, x, e) => Some (l1 ++ b, x, e)
                | None => None
            end
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (split l2 n).
      destruct p, p. 1-2: reflexivity.
    destruct n as [| n'].
      reflexivity.
      rewrite IHt. destruct (split t n').
        destruct p, p. reflexivity.
        cbn. destruct (split l2 (n' - length t)).
          destruct p, p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma split_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    split (map f l) n =
    match split l n with
        | None => None
        | Some (b, x, e) => Some (map f b, f x, map f e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (split t n').
        destruct p, p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma split_replicate :
  forall (A : Type) (n m : nat) (x : A),
    split (replicate n x) m =
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

Lemma split_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    split (iterate f n x) m =
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

