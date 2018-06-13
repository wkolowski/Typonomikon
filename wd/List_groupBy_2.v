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

Compute groupBy orb [true; true; false; false; true].

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

(*
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
*)

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
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      destruct t; inversion e0. cbn. destruct (groupBy p l2).
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
Qed.
(* end hide *)

Fixpoint unsnoc {A : Type} (l : list A) : option (list A * A) :=
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

Lemma groupBy_rev :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    groupBy p (rev l) = rev (map rev (groupBy p l)).
(* begin hide *)
Proof.
  intros. remember (rev l) as r.
  functional induction @groupBy A p r;
  apply (f_equal rev) in Heqr;
  rewrite ?rev_inv in Heqr; rewrite <- Heqr; cbn.
    reflexivity.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. destruct t; cbn in *.
        reflexivity.
        congruence.
    apply (f_equal head) in e0. cbn in e0. apply head_groupBy in e0.
      contradiction.
    
    
  rewrite ?e0 in *; try clear e0; cbn in *.
Admitted.
(* end hide *)

Lemma groupBy_rev' :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    groupBy p l = rev (map rev (groupBy p (rev l))).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    1-2: reflexivity.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. congruence.
  rewrite ?e0 in *; try clear e0; cbn in *.
Admitted.
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
  intros. functional induction @groupBy A p l; cbn.
    1-3: reflexivity.
    Focus 2. rewrite e0 in *. cbn in *. rewrite IHl0. reflexivity.
    rewrite ?e0 in IHl0. cbn in IHl0. inversion IHl0; subst; clear IHl0.
      rewrite H0. f_equal. destruct l0.
        reflexivity.
        cbn in *. destruct l''.
          inversion e0; subst. rewrite e1. reflexivity.
          cbn in *. destruct l''.
            destruct (p y a0); inversion e0; subst; rewrite e1; reflexivity.
Abort.

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
      apply incl_refl.
      inversion H2.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. congruence.
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
    inversion H; subst; clear H.
      exists [x0]. split; constructor.
      inversion H2.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      cbn in e0. congruence.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists (x0 :: l0). split; constructor.
      destruct (IHl0 _ H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists (x0 :: l0). split.
            right. assumption.
            left.
          exists g. split; try right; assumption.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists [x0]. split; constructor.
      destruct (IHl0 _ H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists l0. split.
            assumption.
            right. left.
          exists g. split; repeat right; assumption.
Qed.
(* end hide *)

Function splitBy
  {A : Type} (p : A -> bool) (l : list A) : list (list A) :=
match l with
    | [] => []
    | [h] => if p h then [] else [[h]]
    | x :: (y :: t) as t' =>
        if p y
        then [x] :: splitBy p t
        else 
          match splitBy p t' with
             | [] => if p x then [] else [[x]]
             | l :: ls => if p x then l :: ls else (x :: l) :: ls
         end
end.

Compute splitBy isZero [1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].

Lemma splitBy_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = true -> splitBy p (intersperse x l) = map (fun x => [x]) l.
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn.
    reflexivity.
Abort.
(* end hide *)

(* TODO: unsplitBy *)