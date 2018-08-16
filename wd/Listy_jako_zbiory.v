Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Arith.
Require Import Omega.

Require Import CoqBookPL.book.X3.

(** ** Zawieranie *)

Definition incl {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 -> elem x l2.

(** Przyjrzyjmy się powyższej definicji. Intuicyjnie można ją rozumieć tak,
    że [incl l1 l2] zachodzi, gdy każdy element listy [l1] choć raz występuje
    też na liście [l2]. Udowodnij, że relacja ta ma poniższe właściwości. *)

Lemma incl_nil :
  forall (A : Type) (l : list A), incl [] l.
(* begin hide *)
Proof.
  unfold incl; intros. inversion H.
Qed.
(* end hide *)

Lemma incl_nil_conv :
  forall (A : Type) (l : list A),
    incl l [] -> l = [].
(* begin hide *)
Proof.
  unfold incl; intros. destruct l as [| h t].
    reflexivity.
    specialize (H h ltac:(left)). inversion H.
Qed.
(* end hide *)

Lemma incl_cons :
  forall (A : Type) (h : A) (t1 t2 : list A),
    incl t1 t2 -> incl (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  unfold incl; intros.
  inversion H0; subst; clear H0.
    left.
    right. apply H, H3.
Qed.
(* end hide *)

Lemma incl_cons' :
  forall (A : Type) (h : A) (t : list A),
    incl t (h :: t).
(* begin hide *)
Proof.
  inversion 1; subst.
    right. left.
    do 2 right. assumption.
Qed.
(* end hide *)

Lemma incl_cons'' :
  forall (A : Type) (h : A) (t l : list A),
    incl l t -> incl l (h :: t).
(* begin hide *)
Proof.
  unfold incl; intros. right. apply H, H0.
Qed.
(* end hide *)

Lemma incl_cons_conv :
  exists (A : Type) (x : A) (l1 l2 : list A),
    incl (x :: l1) (x :: l2) /\ ~ incl l1 l2.
(* begin hide *)
Proof.
  exists unit, tt, [tt], []. unfold incl. split; intros.
    inv H.
      constructor.
      assumption.
    intro. specialize (H tt ltac:(left)). inv H.
Qed.
(* end hide *)

Lemma incl_refl :
  forall (A : Type) (l : list A), incl l l.
(* begin hide *)
Proof.
  unfold incl. trivial.
Qed.
(* end hide *)

Lemma incl_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    incl l1 l2 -> incl l2 l3 -> incl l1 l3.
(* begin hide *)
Proof.
  unfold incl; intros. apply H0, H, H1.
Qed.
(* end hide *)

Lemma incl_snoc :
  forall (A : Type) (x : A) (l : list A),
    incl l (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply incl_nil.
    apply incl_cons. assumption.
Qed.
(* end hide *)

Lemma incl_singl_snoc :
  forall (A : Type) (x : A) (l : list A),
    incl [x] (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply incl_refl.
    apply incl_cons''. assumption.
Qed.
(* end hide *)

Lemma incl_snoc_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    incl l1 l2 -> incl (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    apply incl_singl_snoc.
    unfold incl in *. intros x' H'. inversion H'; subst.
      rewrite elem_snoc. left. apply H. left.
      apply IHt.
        intros. apply H. right. assumption.
        assumption.
Qed.
(* end hide *)

Lemma incl_app_l :
  forall (A : Type) (l l1 l2 : list A),
    incl l l1 -> incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_app_l, H, H0.
Qed.
(* end hide *)

Lemma incl_app_r :
  forall (A : Type) (l l1 l2 : list A),
    incl l l2 -> incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_app_r, H, H0.
Qed.
(* end hide *)

Lemma incl_app_l_conv :
  forall (A : Type) (l1 l2 : list A),
    incl (l1 ++ l2) l1 -> incl l2 l1.
(* begin hide *)
Proof.
  unfold incl; intros. apply H, elem_app_r, H0.
Qed.
(* end hide *)

Lemma incl_app_r_conv :
  forall (A : Type) (l1 l2 : list A),
    incl (l1 ++ l2) l2 -> incl l1 l2.
(* begin hide *)
Proof.
  unfold incl; intros. apply H, elem_app_l, H0.
Qed.
(* end hide *)

Lemma incl_app_sym :
  forall (A : Type) (l1 l2 l : list A),
    incl (l1 ++ l2) l -> incl (l2 ++ l1) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply H. rewrite elem_app in *.
  destruct H0; [right | left]; assumption.
Qed.
(* end hide *)

Lemma incl_rev :
  forall (A : Type) (l : list A), incl (rev l) l.
(* begin hide *)
Proof.
  unfold incl; intros. rewrite <- elem_rev. assumption.
Qed.
(* end hide *)

Lemma incl_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    incl l1 l2 -> incl (map f l1) (map f l2).
(* begin hide *)
Proof.
  unfold incl; intros. rewrite elem_map_conv in *.
  destruct H0 as [x' [H1 H2]]. exists x'. split.
    assumption.
    apply H, H2.
Qed.
(* end hide *)

Lemma incl_join :
  forall (A : Type) (ll : list (list A)) (l : list A),
    elem l ll -> incl l (join ll).
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_join. exists l. split; assumption.
Qed.
(* end hide *)

Lemma incl_replicate :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    elem x l -> incl (replicate n x) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_replicate in H0.
  destruct H0. subst. assumption.
Qed.
(* end hide *)

Lemma incl_replicate' :
  forall (A : Type) (n m : nat) (x : A),
    n <> 0 -> incl (replicate m x) (replicate n x).
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_replicate in H0.
  destruct H0. subst. apply elem_replicate. split; trivial.
Qed.
(* end hide *)

Lemma incl_nth :
  forall (A : Type) (l1 l2 : list A),
    incl l1 l2 <->
    forall (n1 : nat) (x : A), nth n1 l1 = Some x ->
      exists n2 : nat, nth n2 l2 = Some x.
(* begin hide *)
Proof.
  unfold incl; split; intros.
    apply nth_elem_Some in H0. specialize (H _ H0). induction H.
      exists 0. cbn. reflexivity.
      destruct (IHelem H0) as [n2 IH]. exists (S n2). cbn. assumption.
    apply nth_elem_conv in H0. destruct H0 as [n Hn].
      destruct (H _ _ Hn) as [n2 Hn2]. apply nth_elem_Some in Hn2. assumption.
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

Lemma incl_take :
  forall (A : Type) (n : nat) (l : list A),
    incl (take n l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_take in H. assumption.
Qed.
(* end hide *)

Lemma incl_drop :
  forall (A : Type) (n : nat) (l : list A),
    incl (drop n l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_drop in H. assumption.
Qed.
(* end hide *)

Lemma incl_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl (filter p l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_filter in H. destruct H. assumption.
Qed.
(* end hide *)

Lemma incl_filter_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl l (filter p l) <-> filter p l = l.
(* begin hide *)
Proof.
  unfold incl. split.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      case_eq (p h); intros; rewrite H0 in *.
        rewrite IHt.
          reflexivity.
          intros. specialize (H x ltac:(right; assumption)).
            inversion H; subst; clear H.
              rewrite elem_filter. split; assumption.
              assumption.
        specialize (H h ltac:(left)). rewrite elem_filter in H.
          destruct H. congruence.
    intros -> *. trivial.
Qed.
(* end hide *)

Lemma incl_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl (takeWhile p l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_takeWhile in H. destruct H. assumption.
Qed.
(* end hide *)

(* begin hide *)
Lemma incl_takeWhile_conv_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl l (takeWhile p l) -> all p l = true.
Proof.
  unfold incl. intros.
  assert (forall x : A, elem x l -> p x = true).
    intros. destruct (elem_takeWhile _ _ _ _ (H _ H0)). assumption.
    clear H. induction l as [| h t]; cbn.
      reflexivity.
      destruct (p h) eqn: Hph; cbn.
        apply IHt. intros. apply H0. right. assumption.
        rewrite <- Hph, H0.
          reflexivity.
          left.
Qed.
(* end hide *)

Lemma incl_takeWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl l (takeWhile p l) <-> takeWhile p l = l.
(* begin hide *)
Proof.
  split; intros.
    apply all_takeWhile'. apply incl_takeWhile_conv_aux, H.
    rewrite H. apply incl_refl.
Qed.
(* end hide *)

Lemma incl_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl (dropWhile p l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_dropWhile in H. assumption.
Qed.
(* end hide *)

Lemma incl_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    incl (map Some (pmap f l)) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply incl_refl.
    destruct (f h); cbn; rewrite ?IHt.
      apply incl_cons. assumption.
      apply incl_cons''. assumption.
Qed.
(* end hide *)

Lemma incl_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    incl l1 (intersperse x l2) -> incl l1 (x :: l2).
(* begin hide *)
Proof.
  unfold incl; intros.
  specialize (H _ H0). rewrite elem_intersperse in H.
  decompose [and or] H; subst; [right | left]; assumption.
Qed.
(* end hide *)

Lemma incl_intersperse_conv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    2 <= length l2 -> incl l1 (x :: l2) -> incl l1 (intersperse x l2).
(* begin hide *)
Proof.
  unfold incl; intros.
  specialize (H0 _ H1). rewrite elem_intersperse.
  inversion H0; subst; firstorder.
Qed.
(* end hide *)

(** Zbiorowa równoważność *)

Definition SetEquiv {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 <-> elem x l2.

Lemma SetEquiv_incl :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <-> incl l1 l2 /\ incl l2 l1.
(* begin hide *)
Proof.
  unfold SetEquiv, incl. firstorder.
Qed.
(* end hide *)

(* Odtąd TODO *)

Lemma SetEquiv_refl :
  forall (A : Type) (l : list A), SetEquiv l l.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_sym :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <-> SetEquiv l2 l1.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    SetEquiv l1 l2 -> SetEquiv l2 l3 -> SetEquiv l1 l3.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_nil_l :
  forall (A : Type) (l : list A),
    SetEquiv [] l -> l = [].
(* begin hide *)
Proof.
  unfold SetEquiv. destruct l as [| h t]; intros.
    reflexivity.
    assert (elem h []).
      rewrite H. left.
      inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_nil_r :
  forall (A : Type) (l : list A),
    SetEquiv l [] -> l = [].
(* begin hide *)
Proof.
  intros. apply SetEquiv_nil_l. rewrite SetEquiv_sym. assumption.
Qed.
(* end hide *)

Lemma SetEquiv_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_cons'. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_cons_conv :
  exists (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv (x :: l1) (x :: l2) /\ ~ SetEquiv l1 l2.
(* begin hide *)
Proof.
  exists unit, tt, [tt], []. unfold SetEquiv. firstorder.
    destruct x. constructor.
    destruct x. constructor.
    intro. assert (elem tt []).
      rewrite <- H. constructor.
      inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_cons' :
  exists (A : Type) (x : A) (l : list A),
    ~ SetEquiv l (x :: l).
(* begin hide *)
Proof.
  exists unit, tt, []. unfold SetEquiv. intro.
  assert (elem tt []).
    rewrite H. constructor.
    inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_snoc_cons :
  forall (A : Type) (x : A) (l : list A),
    SetEquiv (snoc x l) (x :: l).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite elem_snoc, elem_cons'. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_snoc. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_comm :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv (l1 ++ l2) (l2 ++ l1).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_l :
  forall (A : Type) (l1 l2 l : list A),
    SetEquiv l1 l2 -> SetEquiv (l ++ l1) (l ++ l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_r :
  forall (A : Type) (l1 l2 l : list A),
    SetEquiv l1 l2 -> SetEquiv (l1 ++ l) (l2 ++ l).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_rev :
  forall (A : Type) (l : list A), SetEquiv (rev l) l.
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite elem_rev. reflexivity.
Qed.
(* end hide *)

Lemma SetEquiv_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (map f l1) (map f l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_map_conv. firstorder.
Qed.
(* end hide *)

(*Lemma SetEquiv_join :
  forall (A : Type) (ll : list (list A)) (l : list A),
    SetEquiv (join ll)
(* begin hide *)
Proof.
  unfold SetEquiv; intros. apply elem_join. exists l. split; assumption.
Qed.
(* end hide *)
*)

Lemma SetEquiv_replicate :
  forall (A : Type) (n : nat) (x : A),
    SetEquiv (replicate n x) (if isZero n then [] else [x]).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. destruct n; cbn.
    reflexivity.
    rewrite elem_cons', elem_replicate. split; intros.
      decompose [and or] H; subst; constructor.
      inv H.
        left. reflexivity.
        inv H2.
Qed.
(* end hide *)

Lemma SetEquiv_replicate' :
  forall (A : Type) (n m : nat) (x : A),
    m <> 0 -> n <> 0 -> SetEquiv (replicate m x) (replicate n x).
(* begin hide *)
Proof.
  intros. eapply SetEquiv_trans.
    apply SetEquiv_replicate.
    apply SetEquiv_sym. eapply SetEquiv_trans.
      apply SetEquiv_replicate.
      destruct n, m; try contradiction; cbn. apply SetEquiv_refl.
Qed.
(* end hide *)

Lemma SetEquiv_nth :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <->
    forall n : nat, exists m : nat, nth n l1 = nth m l2.
(* begin hide *)
Proof.
  split; revert l2.
    induction l1 as [| h1 t1]; cbn; intros.
      apply SetEquiv_nil_l in H. subst. exists 42.
        rewrite ?nth_nil. reflexivity.
      destruct l2 as [| h2 t2].
        apply SetEquiv_nil_r in H. inv H.
Abort.
(* end hide *)

(*Lemma SetEquiv_remove :
  exists (A : Type) (l1 l1' l2 l2' : list A) (n1 n2 : nat),
    remove match remove n l with
        | None => True
        | Some (_, l') => SetEquiv l' l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      apply SetEquiv_cons'.
      specialize (IHt n'). destruct (remove n' t).
        destruct p. apply SetEquiv_cons, IHt.
        trivial.
Qed.
(* end hide *)
*)

Lemma SetEquiv_take :
  forall (A : Type) (n : nat) (l : list A),
    SetEquiv (take n l) l <-> incl (drop n l) (take n l).
(* begin hide *)
Proof.
  split; revert l.
    induction n as [| n']; cbn; intros.
      apply SetEquiv_nil_l in H. subst. apply incl_refl.
      destruct l as [| h t]; cbn.
        apply incl_refl.
Abort.
(* end hide *)

Lemma SetEquiv_drop :
  forall (A : Type) (n : nat) (l : list A),
    SetEquiv (drop n l) l <-> incl (take n l) (drop n l).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma SetEquiv_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (filter p l) l <-> all p l = true.
(* begin hide *)
Proof.
  split.
    intros. rewrite SetEquiv_incl in H. destruct H.
      rewrite incl_filter_conv in H0. rewrite <- H0, all_filter.
        reflexivity.
    induction l as [| h t]; cbn; intros.
      apply SetEquiv_refl.
      destruct (p h) eqn: Hph; cbn in *.
        apply SetEquiv_cons, IHt, H.
        congruence.
Qed.
(* end hide *)

Lemma SetEquiv_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (takeWhile p l) l <-> all p l = true.
(* begin hide *)
Proof.
  split.
    intros. rewrite SetEquiv_incl in H. destruct H.
      rewrite incl_takeWhile_conv in H0. rewrite <- H0, all_takeWhile.
        reflexivity.
    induction l as [| h t]; cbn; intros.
      apply SetEquiv_refl.
      destruct (p h) eqn: Hph; cbn in *.
        apply SetEquiv_cons, IHt, H.
        congruence.
Qed.
(* end hide *)

Lemma SetEquiv_dropWhile :
  exists (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (dropWhile p l) l /\ any p l = true.
(* begin hide *)
Proof.
  exists bool, id, [true; false; true; false]. cbn. split.
    unfold SetEquiv. firstorder; destruct x; repeat constructor.
    reflexivity.
Qed.
(* end hide *)

Lemma SetEquiv_pmap :
  exists (A B : Type) (f : A -> option B) (l : list A),
    ~ SetEquiv (map Some (pmap f l)) (map f l).
(* begin hide *)
Proof.
  exists bool, unit, (fun b : bool => if b then Some tt else None),
         [true; false].
    cbn. unfold SetEquiv. intro. assert (elem None [Some tt]).
      rewrite H. repeat constructor.
      inv H0. inv H3.
Qed.
(* end hide *)

Lemma SetEquiv_intersperse :
  forall (A : Type) (x : A) (l : list A),
    2 <= length l -> SetEquiv (intersperse x l) (x :: l).
(* begin hide *)
Proof.
  intros A x l. functional induction @intersperse A x l; cbn; intros.
    inv H.
    destruct t; cbn in *.
      inv H. inv H1.
      destruct (intersperse x t); inv e0.
    destruct t; cbn in *.
      inv H. inv H1.
      destruct t; cbn in *.
        inv e0. unfold SetEquiv. intro. rewrite ?elem_cons'. firstorder.
        destruct (intersperse x t) eqn: Heq.
          inv e0. destruct t.
            unfold SetEquiv. intro. rewrite ?elem_cons'. firstorder.
            cbn in Heq. destruct (intersperse x t); inv Heq.
          inv e0. specialize (IHl0 ltac:(omega)). unfold SetEquiv in *.
            intro. specialize (IHl0 x0). rewrite ?elem_cons' in *.
              destruct IHl0 as [IHl1 IHl2]; decompose [or and] IHl1;
              decompose [or] IHl2. split; intro.
                decompose [or] H0; clear H0.
                  1-3: firstorder. Focus 4.
Admitted.
(* end hide *)

Lemma SetEquiv_intersperse_conv :
  forall (A : Type) (x : A) (l : list A),
    SetEquiv (intersperse x l) (x :: l) -> 2 <= length l \/ elem x l.
(* begin hide *)
Proof.
Abort.
(* end hide *)

Ltac se := repeat (cbn in *;
match goal with
    | H : SetEquiv [] _ |- _ => apply SetEquiv_nil_l in H; inv H
    | H : SetEquiv _ [] |- _ => apply SetEquiv_nil_r in H; inv H
    | H : ?P |- ?P => assumption
    | |- SetEquiv [] [] => apply SetEquiv_refl
end).

Lemma SetEquiv_singl :
  forall (A : Type) (l : list A) (x : A),
    SetEquiv [x] l -> forall y : A, elem y l -> y = x.
(* begin hide *)
Proof.
  intros. apply SetEquiv_incl in H. destruct H. clear H.
  unfold incl in H1. specialize (H1 _ H0). inv H1.
    reflexivity.
    inv H3.
Qed.
(* end hide *)

Lemma SetEquiv_pres_intersperse :
  exists (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 /\ ~ SetEquiv (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  exists bool, false, [true], [true; true]. cbn. split.
    unfold SetEquiv. firstorder.
      inv H.
        repeat constructor.
        inv H2.
      repeat (inv H; [repeat constructor | rename H2 into H]). inv H.
    intro. assert (elem false [true]).
      unfold SetEquiv in H. rewrite H. repeat constructor.
      inv H0. inv H3.
Qed.
(* end hide *)