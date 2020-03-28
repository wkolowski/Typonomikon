Require Import D5.

(** ** [exists] *)

(** Można zadać sobie pytanie: skoro predykaty takie jak [elem] czy
    [exists] można zdefiniować zarówno induktywnie jak i przez rekursję,
    który sposób jest lepszy?

    Odpowiedź jest prosta: jeżeli możesz użyć rekursji, zrób to. *)

Fixpoint elem {A : Type} (x : A) (l : list A) : Prop :=
match l with
    | [] => False
    | h :: t => x = h \/ elem x t
end.

Fixpoint all {A : Type} (P : A -> Prop) (l : list A) : Prop :=
match l with
    | [] => True
    | h :: t => P h /\ all P t
end.

Lemma all_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    all P l <-> Forall P l.
Proof.
  induction l as [| h t]; cbn.
    rewrite Forall_nil. reflexivity.
    rewrite Forall_cons, IHt. reflexivity.
Qed.

Fixpoint exactly
  {A : Type} (P : A -> Prop) (n : nat) (l : list A) : Prop :=
match l, n with
    | [], 0 => True
    | [], _ => False
    | h :: t, 0 => ~ P h /\ exactly P 0 t
    | h :: t, S n' =>
        (P h /\ exactly P n' t) \/ (~ P h /\ exactly P n t)
end.

Lemma exactly_spec :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    exactly P n l <-> Exactly P n l.
Proof.
  intros. revert n.
  induction l as [| h t]; cbn.
    destruct n; cbn.
      firstorder. apply Ex_0.
      firstorder. inversion H.
    destruct n as [| n']; cbn.
      rewrite IHt, Exactly_0_cons. reflexivity.
      rewrite !IHt, Exactly_S_cons. reflexivity.
Qed.

(* begin hide *)
Fixpoint ex {A : Type} (P : A -> Prop) (l : list A) : Prop :=
match l with
    | [] => False
    | h :: t => P h \/ ex P t
end.
(* end hide *)

Lemma ex_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l <-> exists x : A, elem x l /\ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder.
    firstorder congruence.
Qed.
(* end hide *)

Lemma ex_nil :
  forall (A : Type) (P : A -> Prop),
    ex P [] <-> False.
(* begin hide *)
Proof.
  split; inversion 1.
Qed.
(* end hide *)

Lemma ex_cons :
  forall (A : Type) (P : A -> Prop) (h : A) (t : list A),
    ex P (h :: t) <-> P h \/ ex P t.
(* begin hide *)
Proof.
  split.
    inversion 1; subst; [left | right]; assumption.
    destruct 1; [left | right]; assumption.
Qed.
(* end hide *)

Lemma ex_length :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l -> 1 <= length l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    destruct 1.
    intros _. apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma ex_snoc :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    ex P (snoc x l) <-> ex P l \/ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder.
    rewrite IHt. firstorder.
Qed.
(* end hide *)

Lemma ex_app :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    ex P (l1 ++ l2) <-> ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    firstorder.
    rewrite IHt1. tauto.
Qed.
(* end hide *)

Lemma ex_rev :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P (rev l) <-> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite ex_app, IHt. cbn. tauto.
Qed.
(* end hide *)

Lemma ex_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    ex P (map f l) -> ex (fun x : A => P (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    tauto.
Qed.
(* end hide *)

Lemma ex_join :
  forall (A : Type) (P : A -> Prop) (ll : list (list A)),
    ex P (join ll) <->
    ex (fun l : list A => ex  P l) ll.
(* begin hide *)
Proof.
  induction ll as [| h t]; cbn; intros.
    reflexivity.
    rewrite ex_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma ex_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    ex P (replicate n x) <-> 1 <= n /\ P x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    firstorder. inversion H.
    firstorder.
Qed.
(* end hide *)

Lemma ex_nth :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l <->
    exists (n : nat) (x : A), nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder congruence.
    rewrite IHt. split.
      destruct 1.
        exists 0, h. split; trivial.
        destruct H as (n & x & H1 & H2).
          exists (S n), x. split; assumption.
      destruct 1 as (n & x & H1 & H2). destruct n as [| n'].
        left. congruence.
        right. exists n', x. split; assumption.
Qed.
(* end hide *)

Lemma ex_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P l ->
    match remove n l with
        | None => True
        | Some (x, l') => ~ P x -> ex P l'
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 2.
    destruct n as [| n'].
      firstorder.
      destruct 1.
        case_eq (remove n' t).
          intros [a la] eq Hnot. cbn. left. assumption.
          trivial.
        case_eq (remove n' t).
          intros [a la] eq Hnot. cbn. specialize (IHt n' H).
            rewrite eq in IHt. right. apply IHt. assumption.
          trivial.
Qed.
(* end hide *)

Lemma ex_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P (take n l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      inversion H.
      cbn in H. firstorder.
Qed.
(* end hide *)

Lemma ex_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P (drop n l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      cbn in H. assumption.
      right. apply (IHt _ H).
Qed.
(* end hide *)

Lemma ex_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P l -> ex P (take n l) \/ ex P (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. assumption.
    destruct n as [| n']; cbn.
      right. assumption.
      firstorder.
Qed.
(* end hide *)

Lemma ex_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      ex P l <-> P x \/ ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 2.
    destruct n as [| n']; cbn; inversion 1; subst.
      cbn. tauto.
      case_eq (splitAt n' t); intros.
        destruct p, p. rewrite (IHt _ _ _ _ H0).
          rewrite H0 in H1. inversion H1; subst. cbn. tauto.
        rewrite H0 in H1. inversion H1.
Restart.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  rewrite ex_app, ex_cons. firstorder.
Qed.
(* end hide *)

Lemma ex_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat) (x : A),
    ex P (insert l n x) <-> P x \/ ex P l.
(* begin hide *)
Proof.
  intros.
  rewrite <- (app_take_drop _ l n) at 2.
  rewrite insert_spec, !ex_app, ex_cons.
  tauto.
Qed.
(* end hide *)

Lemma ex_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      ex P l' <->
      ex P (take n l) \/ P x \/ ex P (drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (n <? length l).
    inversion H; subst. rewrite ex_app, ex_cons. reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma ex_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (filter p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h); cbn in H; firstorder.
Qed.
(* end hide *)

Lemma ex_filter_conv :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P l ->
      ex P (filter p l) \/
      ex P (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 1.
    destruct (p h); cbn; firstorder.
Qed.
(* end hide *)

Lemma ex_filter_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ ex P (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    assumption.
    specialize (IHt H). specialize (H h). destruct (p h); cbn in *.
      firstorder.
      contradiction.
Qed.
(* end hide *)

Lemma ex_partition :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      ex P l <-> ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H.
  inversion H; subst; clear H. split; intro.
    apply ex_filter_conv. assumption.
    destruct H; apply ex_filter in H; assumption.
Qed.
(* end hide *)

Lemma ex_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (takeWhile p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  try destruct (p h); inversion H; subst; clear H.
    left. assumption.
    right. apply IHt, H0.
Qed.
(* end hide *)

Lemma ex_takeWhile_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ ex P (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    assumption.
    specialize (IHt H). specialize (H h).
      destruct (p h); cbn in *; firstorder.
Qed.
(* end hide *)

Lemma ex_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (dropWhile p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h); firstorder.
Qed.
(* end hide *)

Lemma ex_takeWhile_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P l -> ex P (takeWhile p l) \/ ex P (dropWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 1.
    destruct (p h); cbn; firstorder.
Qed.
(* end hide *)

Lemma ex_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        ex P l <-> ex P b \/ P x \/ ex P e.
(* begin hide *)
Proof.
  intros. apply span_spec in H0.
  rewrite H0, ex_app, ex_cons.
  reflexivity.
Qed.
(* end hide *)

Lemma ex_interesting :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (hb : B) (tb : list B),
    ex (fun a : A => ex (fun b : B => P (a, b)) tb) la ->
    ex (fun a : A => ex (fun b : B => P (a, b)) (hb :: tb)) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn.
    contradiction.
    intros. destruct H.
      left. right. assumption.
      right. cbn in IHta. apply IHta. assumption.
Qed.
(* end hide *)

Lemma ex_zip :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (lb : list B),
    ex P (zip la lb) ->
      ex (fun a : A => ex (fun b : B => P (a, b)) lb) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    assumption.
    induction lb as [| hb tb]; inversion H; subst; clear H.
      left. left. assumption.
      specialize (IHta _ H0). right.
        apply ex_interesting. assumption.
Qed.
(* end hide *)

Lemma ex_pmap :
  forall (A B : Type) (f : A -> option B) (P : B -> Prop) (l : list A),
    ex P (pmap f l) <->
      ex (fun x : A => match f x with | Some b => P b | _ => False end) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite IHt.
      reflexivity.
      tauto.
Qed.
(* end hide *)

Lemma ex_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    ex P (intersperse x l) <->
    ex P l \/ (P x /\ 2 <= length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    firstorder lia.
    destruct (intersperse x t) eqn: eq; cbn in *.
      rewrite IHt. firstorder. destruct t; cbn in eq.
        inversion H2. inversion H4.
        destruct (intersperse x t); inversion eq.
      rewrite IHt. firstorder. destruct t; cbn in *.
        inversion eq.
        right. split.
          assumption.
          apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)