Require Import D5.

Function intertwine {A : Type} (l1 l2 : list A) : list A :=
match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: intertwine t1 t2
end.

Lemma intertwine_nil_r :
  forall {A : Type} (l : list A),
    intertwine l [] = l.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma len_intertwine :
  forall {A : Type} (l1 l2 : list A),
    length (intertwine l1 l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite plus_0_r. reflexivity.
      rewrite IHt1, plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma map_intertwine :
  forall {A B : Type} (f : A -> B) (l1 l2 : list A),
    map f (intertwine l1 l2) = intertwine (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      reflexivity.
      rewrite IHt1. reflexivity.
Qed.
(* end hide *)

(* TODO: intertwine z replicate, filter, pmap etc. *)

Lemma any_intertwine :
  forall {A : Type} (p : A -> bool) (l1 l2 : list A),
    any p (intertwine l1 l2) = any p l1 || any p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite orb_false_r. reflexivity.
      rewrite IHt1, <- !orb_assoc. f_equal.
        rewrite orb_assoc. rewrite (orb_comm (p h2)).
        rewrite !orb_assoc. reflexivity.
Qed.
(* end hide *)

Lemma all_intertwine :
  forall {A : Type} (p : A -> bool) (l1 l2 : list A),
    all p (intertwine l1 l2) = all p l1 && all p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite andb_true_r. reflexivity.
      rewrite IHt1, <- !andb_assoc. f_equal.
        rewrite andb_assoc. rewrite (andb_comm (p h2)).
        rewrite !andb_assoc. reflexivity.
Qed.
(* end hide *)

Lemma count_intertwine :
  forall {A : Type} (p : A -> bool) (l1 l2 : list A),
    count p (intertwine l1 l2) = count p l1 + count p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite plus_0_r. reflexivity.
      {
        rewrite IHt1.
        destruct (p h1) eqn: ph1, (p h2) eqn: ph2; cbn.
        all: try rewrite plus_n_Sm; reflexivity.
      }
Qed.
(* end hide *)

Lemma Exists_intertwine :
  forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Exists P (intertwine l1 l2) <->
    Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  split; revert l2.
    induction l1 as [| h1 t1]; cbn.
      right. assumption.
      destruct l2 as [| h2 t2]; cbn; intro.
        left. assumption.
        inv H.
          left. constructor. assumption.
          inv H1.
            right. constructor. assumption.
            destruct (IHt1 _ H0).
              left. right. assumption.
              right. right. assumption.
    induction l1 as [| h1 t1]; cbn.
      destruct 1.
        inv H.
        assumption.
      destruct l2 as [| h2 t2]; cbn; intros [].
        assumption.
        inv H.
        inv H.
          left. assumption.
          right. right. apply IHt1. left. assumption.
        inv H.
          right. left. assumption.
          right. right. apply IHt1. right. assumption.
Qed.
(* end hide *)

Lemma Forall_intertwine :
  forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Forall P (intertwine l1 l2) <->
    Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  split; revert l2.
    induction l1 as [| h1 t1]; cbn.
      split; [constructor | assumption].
      destruct l2 as [| h2 t2]; cbn; intro.
        split; [assumption | constructor].
        inv H. inv H3. destruct (IHt1 _ H4).
          split; constructor; assumption.
    induction l1 as [| h1 t1]; cbn; intros l2 [].
      assumption.
      destruct l2 as [| h2 t2].
        assumption.
        inv H; inv H0. repeat constructor.
          1-2: assumption.
          apply IHt1. split; assumption.
Qed.
(* end hide *)

Lemma elem_Exists :
  forall {A : Type} {x : A} {l : list A},
    elem x l <-> Exists (fun y => x = y) l.
Proof.
  split; induction 1; subst; constructor; auto; fail.
Qed.

Lemma Dup_intertwine :
  forall {A : Type} (l1 l2 : list A),
    Dup (intertwine l1 l2) <->
    Dup l1 \/ Dup l2 \/ exists x : A, elem x l1 /\ elem x l2.
(* begin hide *)
Proof.
  intros.
  functional induction intertwine l1 l2.
    firstorder; inv H.
    firstorder; inv H; inv H0.
    {
      rewrite !Dup_cons, !elem_cons', !IHl,
              !elem_Exists, !Exists_intertwine, <- !elem_Exists.
      firstorder; subst; cbn in *.
        do 2 right. exists h2. split; constructor.
        do 2 right. exists h1. split; constructor; assumption.
        do 2 right. exists h2. split; constructor; assumption.
        do 2 right. exists x. split; constructor; assumption.
        inv H3; inv H4; eauto. eauto 7.
    }
Qed.
(* end hide *)

(* TODO: AtLeast, Exactly, AtMost *)