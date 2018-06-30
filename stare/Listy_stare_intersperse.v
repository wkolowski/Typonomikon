Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Require Import Arith.
Require Import Omega.

(* begin hide *)
Fixpoint intersperse' {A : Type} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | [h] => [h]
    | h :: t => h :: x :: intersperse' x t
end.
(* end hide *)

Functional Scheme intersperse'_ind := Induction for intersperse' Sort Prop.

Lemma intersperse'_spec :
  forall (A : Type) (x : A) (l : list A),
    intersperse' x l = X3.intersperse x l.
Proof.
  intros. functional induction @intersperse' A x l; cbn in *.
    1-2: reflexivity.
    rewrite <- IHl0. destruct _x0; reflexivity.
Qed.

Lemma isEmpty_intersperse' :
  forall (A : Type) (x : A) (l : list A),
    isEmpty (intersperse' x l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h [| h' t]]; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_intersperse' :
  forall (A : Type) (x : A) (l : list A),
    length (intersperse' x l) = 2 * length l - 1.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; cbn in *; trivial.
  rewrite IHl. rewrite plus_0_r, <- minus_n_O, plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma intersperse'_snoc :
  forall (A : Type) (x y : A) (l : list A),
    intersperse' x (snoc y l) =
    if isEmpty l then [y] else snoc y (snoc x (intersperse' x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (snoc y t) as [| h' t'] eqn: Heq.
      apply (f_equal isEmpty) in Heq. cbn in Heq.
        rewrite isEmpty_snoc in Heq. inversion Heq.
      destruct t; cbn in *.
        inversion Heq; subst. reflexivity.
        rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma intersperse'_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    intersperse' x (l1 ++ l2) =
    match l1, l2 with
        | [], _ => intersperse' x l2
        | _, [] => intersperse' x l1
        | h1 :: t1, h2 :: t2 =>
            intersperse' x l1 ++ x :: intersperse' x l2
    end.
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l1; cbn in *.
    reflexivity.
    reflexivity.
    rewrite IHl. destruct l2; reflexivity.
Qed.
(* end hide *)

Lemma intersperse'_rev :
  forall (A : Type) (x : A) (l : list A),
    intersperse' x (rev l) = rev (intersperse' x l).
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; cbn in *; trivial.
  rewrite <- IHl, <- !app_assoc, !intersperse'_app. cbn.
  destruct (rev t); cbn.
    reflexivity.
    rewrite <- app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma intersperse'_map :
  forall (A B : Type) (f : A -> B) (l : list A) (a : A) (b : B),
    f a = b -> intersperse' b (map f l) = map f (intersperse' a l).
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; cbn; trivial; intros.
  rewrite H. cbn in *. rewrite (IHl _ _ H). trivial.
Qed.
(* end hide *)

Lemma intersperse'_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x y : A),
    intersperse' y (iterate f n x) =
    (fix g (n : nat) (x : A) : list A :=
    match n with
        | 0 => []
        | 1 => [x]
        | S (S n') => x :: y :: (f x) :: g n' (f (f x))
    end) n x.
(* begin hide *)
Proof.
  fix 3. destruct n as [| [| n']]; cbn; intros.
    1-2: reflexivity.
    rewrite <- (intersperse'_iterate A f n' (f (f x)) y).
      destruct (iterate f n' (f (f x))); cbn.
        reflexivity.
Abort.
(* end hide *)

Lemma head_intersperse' :
  forall (A : Type) (x : A) (l : list A),
    head (intersperse' x l) = head l.
(* begin hide *)
Proof.
  destruct l as [| h1 [| h2 t]]; reflexivity.
Qed.
(* end hide *)

Lemma any_intersperse' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    any p (intersperse' x l) =
    orb (any p l) (andb (leb 2 (length l)) (p x)).
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l; cbn in *.
    reflexivity.
    rewrite ?Bool.orb_false_r. reflexivity.
    destruct (p h), (p x), (p _x); cbn in *.
      all: try reflexivity.
      rewrite Bool.orb_true_r. reflexivity.
      assumption.
      rewrite IHl0. destruct _x0; cbn; reflexivity.
Qed.
(* end hide *)

Lemma all_intersperse' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all p (intersperse' x l) =
    andb (all p l) (orb (leb (length l) 1) (p x)).
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l; cbn in *.
    reflexivity.
    rewrite ?Bool.andb_true_r. reflexivity.
    destruct (p h), (p x) eqn: Hpx, (p _x) eqn: Hp_x, _x0; cbn in *;
    rewrite ?Hpx, ?Hp_x in *; cbn; trivial.
Qed.
(* end hide *)

Lemma pmap_intersperse' :
  forall (A B : Type) (f : A -> option B) (x : A) (l : list A),
    f x = None -> pmap f (intersperse' x l) = pmap f l.
Proof.
  intros. functional induction @intersperse' A x l; cbn.
    reflexivity.
    destruct (f h); reflexivity.
    cbn in *. rewrite IHl0. destruct (f h); rewrite H; reflexivity.
Qed.
(* end hide *)


Lemma findIndex_intersperse'_true :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A) (n : nat),
    p x = true -> findIndex p (intersperse' x l) = Some n -> n <= 1.
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l; cbn in *.
    inversion H0.
    destruct (p h); inversion H0. apply le_0_n.
    destruct (p h).
      inversion H0. apply le_0_n.
      rewrite H in *. inversion H0. apply le_n.
Qed.
(* end hide *)

Lemma findIndex_intersperse'_true' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = true -> findIndex p (intersperse' x l) =
    match l with
        | [] => None
        | [h] => if p h then Some 0 else None
        | h :: t => if p h then Some 0 else Some 1
    end.
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l; cbn in *.
    reflexivity.
    destruct (p h); reflexivity.
    destruct (p h).
      reflexivity.
      rewrite H. reflexivity.
Qed.
(* end hide *)

Lemma findIndex_intersperse'_false :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A) (n : nat),
    p x = false -> findIndex p l = Some n ->
      findIndex p (intersperse' x l) = Some (2 * n).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0.
    destruct t as [| h' t']; cbn in *.
      destruct (p h); inversion H0; reflexivity.
      destruct (p h).
        inversion H0; reflexivity.
        destruct (p h'); rewrite H.
Restart.
  intros A p x l. functional induction @intersperse' A x l; intros; cbn in *.
    inversion H0.
    destruct (p h); inversion H0. reflexivity.
    destruct (p h) eqn: Hph; rewrite ?H.
      inversion H0. reflexivity.
      destruct (p _x) eqn: H_x.
        rewrite (IHl0 _ H eq_refl). inversion H0. reflexivity.
        destruct (findIndex p _x0) eqn: Heq.
          rewrite (IHl0 _ H eq_refl). inversion H0. f_equal. omega.
          inversion H0.
Qed.
(* end hide *)

Lemma findIndex_intersperse'_false' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = false -> findIndex p l = None ->
      findIndex p (intersperse' x l) = None.
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l; cbn in *.
    reflexivity.
    destruct (p h); assumption.
    destruct (p h).
      assumption.
      rewrite H, IHl0.
        reflexivity.
        destruct (p _x).
          inversion H0.
          destruct (findIndex p _x0).
            inversion H0.
            reflexivity.
Qed.
(* end hide *)

Lemma findIndex_intersperse' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    findIndex p (intersperse' x l) =
    if p x
    then
      match l with
          | [] => None
          | [h] => if p h then Some 0 else None
          | h :: t => if p h then Some 0 else Some 1
      end
    else
      match findIndex p l with
          | None => None
          | Some n => Some (2 * n)
      end.
(* begin hide *)
Proof.
  intros. destruct (p x) eqn: H.
    apply findIndex_intersperse'_true'. assumption.
    destruct (findIndex p l) eqn: H'.
      apply findIndex_intersperse'_false; assumption.
      apply findIndex_intersperse'_false'; assumption.
Qed.
(* end hide *)

Lemma count_intersperse' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    count p (intersperse' x l) =
    count p l + if p x then length l - 1 else 0.
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l; cbn.
    destruct (p x); reflexivity.
    destruct (p x), (p h); reflexivity.
    cbn in *. rewrite IHl0.
      destruct (p x), (p h), (p _x), _x0; cbn in *; omega.
Qed.
(* end hide *)

Lemma filter_intersperse'_false :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = false -> filter p (intersperse' x l) = filter p l.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; cbn in *; intros; trivial.
    rewrite H, (IHl H). reflexivity.
Qed.
(* end hide *)

Lemma elem_intersperse' :
  forall (A : Type) (x y : A) (l : list A),
    elem x (intersperse' y l) <-> elem x l \/ (x = y /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    functional induction @intersperse' A y l; cbn in *.
      inversion 1; subst.
      inversion 1; subst.
        left. assumption.
        inversion H2.
      intro. rewrite !elem_cons' in *. firstorder.
    intro. decompose [and or] H; clear H.
      induction H0; cbn.
        destruct l; left.
        destruct t.
          inversion H0.
          do 2 right. assumption.
      subst. destruct l as [| h1 [| h2 t]]; cbn in *.
        inversion H2.
        inversion H2. inversion H0.
        right; left.
Qed.
(* end hide *)

Lemma In_intersperse' :
  forall (A : Type) (x y : A) (l : list A),
    In x (intersperse' y l) <->
    In x l \/ (x = y /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    functional induction @intersperse' A y l; cbn in *; intros.
      contradiction.
      destruct H; subst.
        do 2 left. reflexivity.
        contradiction.
      firstorder.
    intro. decompose [and or] H; clear H.
      induction l as [| h t]; cbn in *.
        assumption.
        destruct t, H0; subst.
          left. reflexivity.
          inversion H.
          left. reflexivity.
          do 2 right. apply IHt, H.
      subst. destruct l as [| h1 [| h2 t]]; cbn in *.
        inversion H2.
        inversion H2. inversion H0.
        right; left. reflexivity.
Qed.
(* end hide *)

Lemma NoDup_intersperse' :
  forall (A : Type) (x : A) (l : list A),
    NoDup (intersperse' x l) -> length l <= 2.
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l; cbn.
    apply le_0_n.
    apply le_S, le_n.
    destruct _x0; cbn in *.
      apply le_n.
      inversion H. inversion H3. contradiction H6. right; left.
Qed.
(* end hide *)

Lemma Dup_intersperse' :
  forall (A : Type) (x : A) (l : list A),
    Dup (intersperse' x l) -> 2 <= length l.
(* begin hide *)
Proof.
  intros. functional induction @intersperse' A x l; cbn.
    inversion H.
    apply Dup_singl in H. contradiction.
    apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)

(* TODO *)
Lemma Rep_intersperse' :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n (intersperse' y l) <->
    Rep x n l \/ x = y /\ Rep x (S n - length l) l.
(* begin hide *)
Proof.
            Hint Constructors Rep.
  split.
    generalize dependent n; generalize dependent x.
    functional induction @intersperse' A y l; cbn; intros.
      left. assumption.
      left. assumption.
      destruct _x0; cbn in *.
        inv H; auto.
          inv H2; auto. right. cbn. split; auto.
          inv H2; auto. right. cbn. rewrite <- minus_n_O. auto.
        inv H; auto.
          inv H2; auto.
            cbn. destruct (IHl0 y n H1).
              admit.
Abort.
(* end hide *)

Lemma Exists_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Exists P (intersperse' x l) <-> Exists P l \/ (P x /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    functional induction @intersperse' A x l; cbn in *; intros.
      inversion H.
      left. assumption. 
      destruct _x0.
        rewrite !Exists_cons in H. decompose [or] H; clear H.
          do 2 left; assumption.
          right. split; try assumption. apply le_n.
          left; right; left. assumption.
          inversion H0.
        rewrite 2!Exists_cons in H. decompose [or] H; clear H.
          do 2 left. assumption.
          right. split; try assumption. apply le_n_S, le_n_S, le_0_n.
          destruct (IHl0 H1).
            left; right. assumption.
            right. destruct H. split; try assumption. apply le_S, H0.
    functional induction @intersperse' A x l; cbn in *; intros.
      decompose [and or] H; clear H.
        inversion H0.
        inversion H2.
      decompose [and or] H; clear H.
        assumption.
        inversion H2. inversion H0.
      rewrite Exists_cons in H. decompose [and or] H; clear H.
        left. assumption.
        do 2 right. apply IHl0. left. assumption.
        destruct _x0; cbn in *.
          right; left. assumption.
          do 2 right. apply IHl0. right; split.
            assumption.
            apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma Forall_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Forall P (intersperse' x l) <-> Forall P l /\ (2 <= length l -> P x).
(* begin hide *)
Proof.
  split.
    functional induction @intersperse' A x l; intros.
      split.
        assumption.
        inversion 1.
      split.
        assumption.
        inversion 1. inversion H2.
      rewrite !Forall_cons' in *. decompose [and] H; clear H.
        decompose [and or] (IHl0 H3); clear IHl0. auto.
    functional induction @intersperse' A x l; cbn in *; intros.
      constructor.
      destruct H. assumption.
      destruct _x0; rewrite !Forall_cons' in *.
        firstorder.
        decompose [and] H; clear H. edestruct IHl0.
          firstorder.
          destruct H4. firstorder.
Qed.
(* end hide *)

Lemma AtLeast_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    AtLeast P n l -> P x -> AtLeast P (n + (length l - 1)) (intersperse' x l).
(* begin hide *)
Proof.
  intros. generalize dependent n.
  functional induction @intersperse' A x l; cbn in *; intros.
    inversion H. cbn. constructor.
    rewrite plus_0_r. assumption.
    inversion H; subst; clear H; cbn in *.
      constructor 3. constructor.
        assumption.
        specialize (IHl0 0). cbn in IHl0. rewrite <- minus_n_O in *.
          apply IHl0. constructor.
      constructor.
        assumption.
        rewrite <- plus_n_Sm. constructor.
          assumption.
          specialize (IHl0 n0). rewrite <- minus_n_O in *. apply IHl0.
            assumption.
      rewrite <- plus_n_Sm. constructor 3. constructor.
        assumption.
        specialize (IHl0 n). rewrite <- minus_n_O in *. apply IHl0, H3.
Qed.
(* end hide *)

Lemma AtLeast_intersperse'' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    AtLeast P n l -> ~ P x -> AtLeast P n (intersperse' x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    constructor.
    destruct t.
      inversion H0; subst. repeat constructor. assumption.
      repeat constructor; auto.
    destruct t.
      inversion H; subst. constructor.
      repeat constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    Exactly P n l -> P x -> Exactly P (n + (length l - 1)) (intersperse' x l).
(* begin hide *)
Proof.
  intros. generalize dependent n.
  functional induction @intersperse' A x l; cbn in *; intros.
    inversion H. cbn. constructor.
    rewrite plus_0_r. assumption.
    inversion H; subst; clear H; cbn in *.
      constructor.
        assumption.
        rewrite <- plus_n_Sm. constructor.
          assumption.
          specialize (IHl0 n0). cbn in IHl0. rewrite <- minus_n_O in *.
            apply IHl0. assumption.
      constructor 3.
        assumption.
        rewrite <- plus_n_Sm. constructor.
          assumption.
          specialize (IHl0 n). rewrite <- minus_n_O in *. apply IHl0, H5.
Qed.
(* end hide *)

Lemma Exactly_intersperse'' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    Exactly P n l -> ~ P x ->
      Exactly P n (intersperse' x l).
(* begin hide *)
Proof.
  intros. generalize dependent n.
  functional induction @intersperse' A x l; cbn in *; intros.
    inversion H. cbn. constructor.
    assumption.
    inversion H; subst; clear H; cbn in *.
      repeat constructor; try assumption. apply IHl0, H5.
      repeat constructor; try assumption. apply IHl0, H5.
Qed.
(* end hide *)

Lemma incl_intersperse' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    incl l1 (intersperse' x l2) -> incl l1 (x :: l2).
(* begin hide *)
Proof.
  unfold incl; intros.
  specialize (H _ H0). rewrite elem_intersperse' in H.
  decompose [and or] H; subst; [right | left]; assumption.
Qed.
(* end hide *)

Lemma incl_intersperse'_conv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    2 <= length l2 -> incl l1 (x :: l2) -> incl l1 (intersperse' x l2).
(* begin hide *)
Proof.
  unfold incl; intros.
  specialize (H0 _ H1). rewrite elem_intersperse'.
  inversion H0; subst; firstorder.
Qed.
(* end hide *)