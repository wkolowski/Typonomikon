Require Import D5.

Function groupBy
  {A : Type} (p : A -> A -> bool) (l : list A) : list (list A) :=
match l with
    | [] => []
    | [x] => [[x]]
    | x :: (y :: l'') as l' =>
        match groupBy p l' with
            | [] => [[x]]
            | l :: ls => if p x y then (x :: l) :: ls else [x] :: l :: ls
        end
end.

Lemma isEmpty_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    isEmpty (groupBy p l) = isEmpty l.
(* begin hide *)
Proof.
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
    1-2: apply le_n.
    apply le_n_S, le_0_n.
    apply le_S. assumption.
    apply le_n_S. assumption.
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
  intros. functional induction @groupBy A p l; cbn.
    left. reflexivity.
    right. left. reflexivity.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. congruence.
    rewrite e0 in IHl0.
      destruct IHl0 as [IH | [IH | (l1 & l2 & IH1 & IH2)]].
        inversion IH.
        inversion IH; subst; clear IH. right. left. reflexivity.
        do 2 right. exists [], (x :: l1 ++ l2). split.
          cbn. rewrite IH1. reflexivity.
          cbn. rewrite <- IH1. rewrite e0, e1. reflexivity.
    rewrite e0 in IHl0.
      destruct IHl0 as [IH | [IH | (l1 & l2 & IH1 & IH2)]].
        inversion IH.
        inversion IH; subst; clear IH. do 2 right.
          exists [x], (y :: l''). split; cbn.
            reflexivity.
            cbn in e0. rewrite e0. reflexivity.
        do 2 right. exists [x], (l1 ++ l2). split.
          cbn. rewrite IH1. reflexivity.
          rewrite <- IH1, e0. cbn. reflexivity.
Qed.
(* end hide *)

(* TODO: app, rev *)

Lemma groupBy_map :
  forall (A B : Type) (f : A -> B) (p : B -> B -> bool) (l : list A),
    groupBy p (map f l) =
    map (map f) (groupBy (fun x y => p (f x) (f y)) l).
(* begin hide *)
Proof.
  intros. remember (fun _ => _) as p'.
  functional induction @groupBy A p' l;
  rewrite ?e0 in *; cbn in *; rewrite ?IHl0; trivial.
    destruct (p (f x) (f y)); cbn.
      reflexivity.
      congruence.
    destruct (p (f x) (f y)); cbn.
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
  intros. functional induction groupBy p l; cbn.
    1-3: reflexivity.
    Focus 2. rewrite e0 in *. cbn in *. rewrite IHl0. reflexivity.
    {
      rewrite ?e0 in IHl0. clear e0. cbn in IHl0.
      inv IHl0. rewrite H0.
Abort.
(* end hide *)

Lemma join_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    join (groupBy p l) = l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    1-2: reflexivity.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      inversion e0.
    rewrite e0 in IHl0. cbn in IHl0. rewrite IHl0. reflexivity.
    rewrite e0 in IHl0. cbn in IHl0. rewrite IHl0. reflexivity.
Qed.
(* end hide *)

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
      rewrite IHn''. destruct (p x x); reflexivity.
Qed.
(* end hide *)

Lemma any_groupBy :
  forall (A : Type) (q : A -> bool) (p : A -> A -> bool) (l : list A),
    any (any q) (groupBy p l) = any q l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l;
  cbn; rewrite ?Bool.orb_false_r; try rewrite ?e0 in IHl0.
    1-2: reflexivity.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. congruence.
    cbn in IHl0. rewrite <- IHl0. rewrite Bool.orb_assoc. reflexivity.
    cbn in IHl0. rewrite <- IHl0. reflexivity.
Qed.
(* end hide *)

Lemma all_groupBy :
  forall (A : Type) (q : A -> bool) (p : A -> A -> bool) (l : list A),
    all (all q) (groupBy p l) = all q l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l;
  cbn; rewrite ?Bool.andb_true_r; try rewrite ?e0 in IHl0.
    1-2: reflexivity.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. congruence.
    cbn in IHl0. rewrite <- IHl0. rewrite Bool.andb_assoc. reflexivity.
    cbn in IHl0. rewrite <- IHl0. reflexivity.
Qed.
(* end hide *)

Ltac inv H := inversion H; subst; clear H.

Lemma groupBy_elem_incl :
  forall (A : Type) (p : A -> A -> bool) (l g : list A),
    elem g (groupBy p l) -> Incl g l.
(* begin hide *)
Proof.
  intros A p l.
  functional induction @groupBy A p l; intros;
  try rewrite ?e0 in IHl0.
    inv H.
    inv H.
      apply Incl_refl.
      inv H2.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. congruence.
    inversion H; subst; clear H.
      apply Incl_cons, IHl0. left. 
      apply Incl_cons'', IHl0. right. assumption.
    inversion H; subst; clear H.
      apply Incl_cons, Incl_nil.
      apply Incl_cons'', IHl0. assumption.
Qed.
(* end hide *)

Lemma groupBy_elem :
  forall (A : Type) (p : A -> A -> bool) (x : A) (l : list A),
    elem x l -> exists g : list A, elem x g /\ elem g (groupBy p l).
(* begin hide *)
Proof.
  intros A p x l. revert x. functional induction @groupBy A p l; intros.
    inversion H.
    inversion H; subst; clear H.
      exists [x]. split; constructor.
      inversion H2.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. congruence.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists (x :: l0). split; constructor.
      destruct (IHl0 _ H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists (x :: l0). split.
            right. assumption.
            left.
          exists g. split; try right; assumption.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists [x]. split; constructor.
      destruct (IHl0 _ H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists l0. split.
            assumption.
            right. left.
          exists g. split; repeat right; assumption.
Qed.
(* end hide *)