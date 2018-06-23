Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Function groupBy
  {A : Type} (p : A -> A -> bool) (l : list A) : list (list A) :=
match l with
    | [] => []
    | h :: t =>
        match groupBy p t with
            | [] => [[h]]
            | [] :: gs => [h] :: gs
            | (h' :: t') :: gs =>
                if p h h'
                then (h :: h' :: t') :: gs
                else [h] :: (h' :: t') :: gs
        end
end.

Lemma head_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    ~ head (groupBy p l) = Some [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 1.
    destruct (groupBy p t).
      inversion 1.
      cbn in IHt. destruct l.
        contradiction.
        destruct (p h a); cbn; inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    isEmpty (groupBy p l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l; cbn.
    reflexivity.
    destruct (groupBy p l); cbn.
      reflexivity.
      destruct l0; cbn.
        reflexivity.
        destruct (p a a0); reflexivity.
Restart.
  intros. functional induction @groupBy A p l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    length (groupBy p l) <= length l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l;
  rewrite ?e0 in *; try clear e0; cbn in *.
    apply le_n.
    apply le_n_S, IHl0.
    apply le_S, IHl0.
    apply le_S, IHl0.
    apply le_n_S, IHl0.
Qed.
(* end hide *)

Ltac gb :=
match goal with
    | H : groupBy _ ?l = [] |- _ =>
        apply (f_equal isEmpty) in H;
        rewrite isEmpty_groupBy in H;
        destruct l; inversion H; subst
    | H : groupBy _ _ = [] :: _ |- _ =>
        apply (f_equal head), head_groupBy in H; contradiction
end; cbn; try congruence.

Require Import Arith.

Compute groupBy beq_nat [0; 1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].
Compute groupBy 
  (fun n m => negb (beq_nat n m))
  [0; 1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].

Lemma groupBy_negb :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    groupBy (fun x y => negb (p x y)) l = groupBy p l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    reflexivity.
    gb.
    gb.
    rewrite IHl0, e0, e1.
Abort.
(* end hide *)

Lemma groupBy_decomposition :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    l = [] \/ exists n : nat,
      groupBy p l = take n l :: groupBy p (drop n l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l.
    left. reflexivity.
      gb. right. exists 1. cbn. reflexivity.
      gb.
    destruct IHl0; subst.
      cbn in e0. inversion e0.
      right. destruct H as [n H]. exists (S n). cbn.
        rewrite e0 in H. inversion H. reflexivity.
    destruct IHl0; subst.
      cbn in e0. inversion e0.
      destruct H as [n H]. rewrite e0 in H. inversion H; subst.
        right. exists 1. cbn. rewrite e0. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_cons :
  forall (A : Type) (p : A -> A -> bool) (l h : list A) (t : list (list A)),
    groupBy p l = h :: t -> groupBy p h = [h].
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    inversion H.
    inversion H; subst. cbn. reflexivity.
    gb.
    inversion H; subst; clear H. rewrite e0 in *. cbn in *.
      specialize (IHl0 _ _ eq_refl). cbn in *. destruct (groupBy p t').
        rewrite e1. inversion IHl0. reflexivity.
        destruct l.
          rewrite e1. inversion IHl0. reflexivity.
          destruct (p h' a); rewrite e1; inversion IHl0; reflexivity.
    inversion H; subst; clear H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_app_decomposition :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    groupBy p l = [] \/
    groupBy p l = [l] \/
    exists l1 l2 : list A,
      l = l1 ++ l2 /\
      groupBy p l = groupBy p l1 ++ groupBy p l2.
(* begin hide *)
Proof.
  intros. destruct (groupBy_decomposition A p l).
    left. rewrite H. cbn. reflexivity.
    destruct H as [n H]. rewrite H. do 2 right.
      exists (take n l), (drop n l). split.
        rewrite take_drop_spec. reflexivity.
         apply groupBy_cons in H. rewrite H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_middle :
  forall (A : Type) (p : A -> A -> bool) (l1 l2 : list A) (x y : A),
    p x y = false ->
      groupBy p (l1 ++ x :: y :: l2) =
      groupBy p (l1 ++ [x]) ++ groupBy p (y :: l2).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l1; cbn.
    destruct (groupBy p l2) eqn: Heq.
      rewrite H. reflexivity.
      destruct l; cbn; rewrite ?H.
        reflexivity.
        destruct (p y a); rewrite H; reflexivity.
    gb. destruct (groupBy p l2).
      rewrite H. destruct (p h x); reflexivity.
      destruct l; cbn.
        rewrite H. destruct (p h x); reflexivity.
        destruct (p y a); rewrite H; destruct (p h x); reflexivity.
    rewrite (IHl _ _ _ H). destruct t; cbn.
      destruct (p h x); reflexivity.
      destruct (groupBy p (t ++ [x])), (groupBy p l2); cbn.
        destruct (p h a); reflexivity.
        destruct (p h a); reflexivity.
        destruct l; cbn.
          destruct (p h a); reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
        destruct l; cbn.
          destruct (p h a); reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
    rewrite (IHl _ _ _ H); clear IHl. destruct t; cbn.
      destruct (p h x); reflexivity.
      cbn in *. destruct (groupBy p (t ++ [x])), (groupBy p l2); cbn.
        1-2: destruct (p h a); reflexivity.
        destruct l; cbn; destruct (p h a).
          reflexivity.
          cbn. reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
        destruct l; cbn.
          destruct (p h a); cbn; reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
    rewrite (IHl _ _ _ H); clear IHl. destruct t; cbn.
      destruct (p h x); reflexivity.
      cbn in *. destruct (groupBy p (t ++ [x])), (groupBy p l2); cbn.
        1-2: destruct (p h a); reflexivity.
        destruct l; cbn; destruct (p h a).
          reflexivity.
          cbn. reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
        destruct l; cbn.
          destruct (p h a); cbn; reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
Restart.
  Ltac wut H :=
  match H with
      | context [match ?x with _ => _ end] => wut x
      | _ => destruct H
  end.
  Ltac dst :=
  repeat (cbn in *; match goal with
      | |- ?goal => wut goal
  end); cbn in *; try congruence; gb.

  intros. functional induction @groupBy A p l1; cbn.
    dst.
    gb. dst.
    gb.
    1-2: rewrite (IHl _ _ _ H); clear IHl; destruct t; dst.
Qed.

(* end hide *)

(*Fixpoint unsnoc {A : Type} (l : list A) : option (list A * A) :=
match l with
    | [] => None
    | h :: t =>
        match unsnoc t with
            | None => Some ([], h)
            | Some (l, x) => Some (h :: l, x)
        end
end.

Lemma unsnoc_spec :
  forall (A : Type) (l l' : list A) (x : A),
    unsnoc l = Some (l', x) ->
      init l = Some l' /\ last l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (unsnoc t) eqn: H_unsnoc.
      destruct p. destruct (IHt _ _ eq_refl). rewrite H0, H1. split.
        inversion H. reflexivity.
        destruct t; inversion H; inversion H0. reflexivity.
      inversion H; subst. destruct t; cbn in *.
        split; reflexivity.
        destruct (unsnoc t); try destruct p; inversion H_unsnoc.
Qed.
(* end hide *)
*)

Lemma init_last :
  forall (A : Type) (l l' : list A) (x : A),
    init l = Some l' -> last l = Some x -> l = l' ++ [x].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (init t) eqn: H_init.
      inversion H; subst. destruct (last t) eqn: H_last.
        rewrite (IHt _ _ eq_refl eq_refl). cbn. destruct t; inversion H0.
          inversion H_last.
          reflexivity.
        destruct t.
          inversion H_init.
          inversion H0.
      destruct t.
        inversion H; inversion H0; cbn. reflexivity.
        cbn in *. destruct (init t); inversion H_init.
Qed.
(* end hide *)

Lemma groupBy_app :
  forall (A : Type) (p : A -> A -> bool) (l1 l2 : list A) (x y : A),
    last l1 = Some x -> head l2 = Some y -> p x y = false ->
      groupBy p (l1 ++ l2) = groupBy p l1 ++ groupBy p l2.
(* begin hide *)
Proof.
  intros. destruct (init l1) eqn: Heq.
    destruct l2.
      cbn. rewrite ?app_nil_r. reflexivity.
      rewrite (init_last _ _ _ _ Heq H), <- app_assoc. cbn.
        rewrite groupBy_middle.
          cbn. reflexivity.
          inversion H0. assumption.
    destruct l1; cbn in *.
      inversion H.
      destruct (init l1); inversion Heq.
Qed.
(* end hide *)

(*Lemma groupBy_app' :
  forall (A : Type) (p : A -> A -> bool) (l1 l2 : list A),
    groupBy p (l1 ++ l2) =
    match last l1, head l2 with
        | None, _ => groupBy p l2
        | _, None => groupBy p l1
        | Some x, Some y =>
            if p x y
            then groupBy p l1 ++ groupBy p l2
            else 
*)
(* begin hide *)

Lemma groupBy_rev :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    rev (groupBy p l) = map rev (groupBy p (rev l)).
(* begin hide *)
Proof.
  intros. destruct (groupBy_decomposition _ p l).
    subst. cbn. reflexivity.
    destruct H as [n H]. rewrite H. cbn.
Abort.
(* end hide *)

Lemma groupBy_rev :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    groupBy p (rev l) = rev (map rev (groupBy p l)).
(* begin hide *)
Proof.
  intros.
  functional induction @groupBy A p l; cbn.
    reflexivity.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      destruct t; inversion e0.  cbn. reflexivity.
    apply (f_equal head) in e0. apply head_groupBy in e0.
      contradiction.
Admitted.
(* end hide *)

Lemma groupBy_rev' :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    groupBy p l = rev (map rev (groupBy p (rev l))).
(* begin hide *)
Proof.
  intros. rewrite <- groupBy_rev, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_map :
  forall (A B : Type) (f : A -> B) (p : B -> B -> bool) (l : list A),
    groupBy p (map f l) =
    map (map f) (groupBy (fun x y => p (f x) (f y)) l).
(* begin hide *)
Proof.
  intros. remember (fun _ => _) as p'.
  functional induction @groupBy A p' l;
  rewrite ?e0 in *; cbn in *; rewrite ?IHl0; trivial.
    destruct (p (f h) (f h')); cbn.
      reflexivity.
      congruence.
    destruct (p (f h) (f h')); cbn.
      congruence.
      reflexivity.
Qed.
(* end hide *)

Lemma map_groupBy_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    map (groupBy p) (groupBy p l) =
    map (fun x => [x]) (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    1-2: reflexivity.
    gb.
    rewrite e0 in *. cbn in *. destruct (groupBy p t').
      rewrite e1. inversion IHl0. reflexivity.
      destruct l; cbn.
        rewrite e1. inversion IHl0. reflexivity.
        destruct (p h' a); rewrite e1.
          inversion IHl0. reflexivity.
          inversion IHl0.
    rewrite e0 in *. cbn in *. destruct (groupBy p t').
      inversion IHl0. reflexivity.
      destruct l; inversion IHl0; reflexivity.
Qed.
(* end hide *)

Lemma join_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    join (groupBy p l) = l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    reflexivity.
    gb.
    gb.
    rewrite <- IHl0, e0. cbn. reflexivity.
    rewrite <- IHl0, e0. cbn. reflexivity.
Qed.
(* end hide *)

(* TODO: bind *)

Definition isZero n :=
  match n with | 0 => true | _ => false end.

Lemma groupBy_replicate :
  forall (A : Type) (p : A -> A -> bool) (n : nat) (x : A),
    groupBy p (replicate n x) =
    if isZero n
    then []
    else if p x x then [replicate n x] else replicate n [x].
(* begin hide *)
Proof.
  destruct n as [| n']; cbn; intros.
    reflexivity.
    induction n' as [| n'']; cbn.
      destruct (p x x); reflexivity.
      rewrite IHn''. destruct (p x x) eqn: H; rewrite H; reflexivity.
Qed.
(* end hide *)

Lemma groupBy_take :
  forall (A : Type) (p : A -> A -> bool) (l : list A) (n : nat),
    exists m : nat,
      groupBy p (take n l) = take m (groupBy p l).
(* begin hide *)
Proof.
  intros A p l. functional induction @groupBy A p l; cbn; intros.
    exists 0. rewrite ?take_nil. cbn. reflexivity.
    gb. destruct n as [| n']; cbn.
      exists 0. cbn. reflexivity.
      exists 1. rewrite take_nil. cbn. reflexivity.
    gb.
    destruct n as [| n']; cbn.
      exists 0. cbn. reflexivity.
      rewrite e0 in *. destruct (IHl0 n') as [m IH]. exists (S m).
        cbn. destruct (groupBy p (take n' t)) eqn: Heq.
          apply (f_equal isEmpty) in Heq.
            rewrite isEmpty_groupBy, isEmpty_take in Heq.
              destruct n', t; cbn in Heq; inversion Heq.
                cbn in e0. inversion e0.
                cbn in e0.
Admitted.
(* end hide *)


Lemma any_groupBy :
  forall (A : Type) (q : A -> bool) (p : A -> A -> bool) (l : list A),
    any (any q) (groupBy p l) = any q l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l;
  cbn; rewrite ?Bool.orb_false_r; try rewrite ?e0 in IHl0.
    reflexivity.
    gb.
    rewrite Bool.orb_false_r. reflexivity.
    gb.
    cbn in IHl0. rewrite <- IHl0. rewrite ?Bool.orb_assoc. reflexivity.
    cbn in IHl0. rewrite <- IHl0. reflexivity.
Qed.
(* end hide *)

Lemma all_groupBy :
  forall (A : Type) (q : A -> bool) (p : A -> A -> bool) (l : list A),
    all (all q) (groupBy p l) = all q l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    reflexivity.
    gb.
    rewrite Bool.andb_true_r. reflexivity.
    gb.
    1-2: rewrite ?e0 in IHl0; cbn in *; rewrite <- IHl0.
      rewrite ?Bool.andb_assoc. reflexivity.
      rewrite <- ?Bool.andb_assoc. cbn. reflexivity.
Qed.
(* end hide *)

(*Lemma sum_count_groupBy :
  forall (A : Type) (q : A -> bool) (p : A -> A -> bool) (l : list A),
    foldl plus 
*)

Lemma groupBy_elem_incl :
  forall (A : Type) (p : A -> A -> bool) (l g : list A),
    elem g (groupBy p l) -> incl g l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l;
  try rewrite ?e0 in IHl0.
    inversion H.
    inversion H; subst; clear H.
      gb.
      inversion H2.
    gb.
    inversion H; subst; clear H.
      apply incl_cons, IHl0. left.
      apply incl_cons'', IHl0. right. assumption.
    inversion H; subst; clear H.
      apply incl_cons, incl_nil.
      apply incl_cons'', IHl0. assumption.
Qed.
(* end hide *)

Lemma groupBy_elem :
  forall (A : Type) (p : A -> A -> bool) (x : A) (l : list A),
    elem x l -> exists g : list A, elem x g /\ elem g (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l.
    inversion H.
    gb.
    inversion H; subst; clear H.
      exists [h]. split; constructor.
      inversion H2.
    gb.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists (h :: h' :: t'). split; constructor.
      destruct (IHl0 _ H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists (h :: h' :: t'). split.
            right. assumption.
            left.
          exists g. split; try right; assumption.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists [h]. split; constructor.
      destruct (IHl0 _ H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists (h' :: t'). split.
            assumption.
            right. left.
          exists g. split; repeat right; assumption.
Qed.
(* end hide *)

Lemma groupBy_elem_nil :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    ~ elem [] (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l.
    inversion 1.
    intro. inversion H; subst. inversion H2.
    gb.
    inversion 1; subst. apply IHl0. rewrite e0. right. assumption.
    inversion 1; subst. apply IHl0. rewrite e0. assumption.
Qed.
(* end hide *)
