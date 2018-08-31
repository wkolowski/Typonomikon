Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(* TODO: findIndex, takeWhile, dropWhile *)

Definition Classically (A : Type) : Type :=
  (forall P : Prop, P \/ ~ P) -> A.

Notation "f $ x" := (f x) (at level 100, only parsing).

Ltac cls := progress unfold Classically; intro LEM.

(* TODO: Dup (bez NoDup) *)

Lemma Dup_replace :
  Classically $
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Dup l -> Dup l' \/ ~ elem x l.
(* begin hide *)
Proof.
  cls. induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. inv H0.
        destruct (LEM (x = h)).
          subst. left. constructor. assumption.
          destruct (LEM (elem x t)).
            left. constructor. assumption.
            right. intro. inv H2; contradiction.
        left. right. assumption.
      destruct (replace t n' x) eqn: Heq.
        inv H. inv H0.
          destruct (LEM (elem h l)).
            left. constructor. assumption.
Restart.
  cls. intros. rewrite Dup_spec in *.
  destruct H0 as (s & l1 & l2 & l3 & Hs). subst.
Abort.
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