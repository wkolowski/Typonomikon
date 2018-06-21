Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Function intersperse {A : Type} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t =>
        match intersperse x t with
            | [] => [h]
            | h' :: t' => h :: x :: h' :: t'
        end
end.

Lemma intersperse_spec :
  forall (A : Type) (x : A) (l : list A),
    intersperse x l = X3.intersperse x l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct t; cbn.
      reflexivity.
      destruct t; reflexivity.
Qed.

Lemma isEmpty_intersperse :
  forall (A : Type) (x : A) (l : list A),
    isEmpty (intersperse x l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma length_intersperse :
  forall (A : Type) (x : A) (l : list A),
    length (intersperse x l) = 2 * length l - 1.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; cbn in *.
    1-2: reflexivity.
    destruct (intersperse x t); cbn in *. Require Import Arith.
      rewrite <- minus_n_O, plus_0_r, <- ?plus_n_Sm in *.
        destruct t; inversion IHl. cbn. reflexivity.
      rewrite IHl. rewrite <- ?plus_n_Sm. rewrite <- minus_n_O.
        reflexivity.
Qed.
(* end hide *)

Lemma intersperse_snoc :
  forall (A : Type) (x y : A) (l : list A),
    intersperse x (snoc y l) =
    if isEmpty l then [y] else snoc y (snoc x (intersperse x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct t; cbn.
      reflexivity.
      destruct (intersperse x t); cbn; reflexivity.
Qed.
(* end hide *)

Lemma intersperse_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    intersperse x (l1 ++ l2) =
    match l1, l2 with
        | [], _ => intersperse x l2
        | _, [] => intersperse x l1
        | h1 :: t1, h2 :: t2 =>
            intersperse x l1 ++ x :: intersperse x l2
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. destruct t, l2; cbn.
      1,3: reflexivity.
      destruct (intersperse x l2); reflexivity.
      destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma intersperse_rev :
  forall (A : Type) (x : A) (l : list A),
    intersperse x (rev l) = rev (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite intersperse_app. destruct (rev t) eqn: Heq.
      apply (f_equal rev) in Heq. rewrite rev_inv in Heq.
        cbn in Heq. rewrite Heq. cbn. reflexivity.
      rewrite IHt. destruct (intersperse x t); cbn.
        cbn in IHt. destruct (intersperse x l); inversion IHt.
        rewrite <- ?app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma intersperse_map :
  forall (A B : Type) (f : A -> B) (l : list A) (a : A) (b : B),
    f a = b -> intersperse b (map f l) = map f (intersperse a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite (IHt _ _ H). destruct (intersperse a t); cbn.
      reflexivity.
      rewrite H. reflexivity.
Qed.
(* end hide *)

Lemma head_intersperse :
  forall (A : Type) (x : A) (l : list A),
    head (intersperse x l) = head l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma last_intersperse :
  forall (A : Type) (x : A) (l : list A),
    last (intersperse x l) = last l.
(* begin hide *)
Proof.
  intros. pose (H := intersperse_rev _ x (rev l)).
  rewrite rev_inv in H.
  rewrite H, last_rev, head_intersperse, head_rev.
  reflexivity.
Qed.
(* end hide *)

Lemma tail_intersperse :
  forall (A : Type) (x : A) (l : list A),
    tail (intersperse x l) =
    match tail l with
        | None => None
        | Some [] => Some []
        | Some (h :: t) => Some (x :: intersperse x t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct t; cbn in *.
      reflexivity.
      destruct (intersperse x t).
Abort.
(* end hide *)

(* TODO: init *)

Lemma nth_intersperse_even :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l ->
      nth (2 * n) (intersperse x l) = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      destruct (intersperse x t); reflexivity.
      destruct (intersperse x t).
        rewrite nth_nil. destruct t; cbn in *.
          rewrite nth_nil. reflexivity.
          apply lt_S_n in H. specialize (IHt _ H).
            rewrite nth_nil in IHt. destruct n'; cbn in *; inversion IHt.
              reflexivity.
        rewrite <- plus_n_Sm. cbn. rewrite <- IHt.
          cbn. reflexivity.
          apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_intersperse_odd :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    0 < n -> n < length l ->
      nth (2 * n - 1) (intersperse x l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H0.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        destruct n; cbn in *.
          inversion H.
          destruct n; cbn in *.
            inversion H0. inversion H2.
            inversion H0. inversion H2.
        destruct (intersperse x t); inversion Heq.
      destruct t; cbn in *.
        inversion Heq.
        destruct n as [| n']; cbn.
          inversion H.
          destruct n' as [| n'']; cbn.
            reflexivity.
            rewrite <- IHt with (S n'').
              cbn. rewrite <- ?plus_n_Sm, <- minus_n_O, ?plus_0_r.
                cbn. reflexivity.
              apply le_n_S, le_0_n.
              apply lt_S_n. assumption.
Qed.
(* end hide *)

(* TODO: insert, remove *)

Lemma take_intersperse :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    1 < n -> 1 < length l ->
      take (2 * n) (intersperse x l) =
      intersperse x (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite ?take_nil. cbn. reflexivity.
    destruct (intersperse x t).
      destruct n as [| [| n']]; cbn.
        1-2: reflexivity.
        destruct t; cbn.
          reflexivity.
          destruct t; cbn in *.
Abort.
(* end hide *)

(* TODO drop, zip, unzip, zipWith *)

(*Lemma pmap_intersperse :
  forall (A B : Type) (f : A -> option B) (x : A) (l : list A),
    f x = None ->
      pmap f (intersperse x l) = pmap f l.
(* begin hide *)
Proof.
  

Qed.
(* end hide *)
*)

Lemma any_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    any p (intersperse x l) =
    orb (any p l) (andb (leb 2 (length l)) (p x)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn.
      destruct t; cbn in *.
        rewrite ?Bool.orb_false_r. reflexivity.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t) eqn: Heq'; inv Heq.
          destruct t; cbn in *.
            rewrite ?Bool.orb_false_r.
              destruct (p h), (p a), (p x); reflexivity.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (any p t); reflexivity.
          destruct t; cbn in *.
            inv Heq'.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (any p t); reflexivity.
Qed.
(* end hide *)

Lemma all_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all p (intersperse x l) =
    andb (all p l) (orb (leb (length l) 1) (p x)).
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn in *.
    reflexivity.
    destruct t; cbn in *.
      rewrite ?Bool.andb_true_r. reflexivity.
      rewrite e0 in *. cbn in *. destruct t; cbn in *.
        inversion e0.
        rewrite (IHl0 p). rewrite Bool.andb_assoc. reflexivity.
    rewrite e0 in *. cbn in *. rewrite IHl0. destruct t; cbn.
      inversion e0.
      destruct t; cbn.
        rewrite ?Bool.andb_true_r.
          destruct (p h), (p x), (p a); reflexivity.
        destruct (p h), (p x), (p a), (p a0), (all p t); reflexivity.
Restart.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn.
      destruct t; cbn in *.
        rewrite ?Bool.andb_true_r. reflexivity.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t) eqn: Heq'; inv Heq.
          destruct t; cbn in *.
            rewrite ?Bool.andb_true_r.
              destruct (p h), (p a), (p x); reflexivity.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (all p t); reflexivity.
          destruct t; cbn in *.
            inv Heq'.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (all p t); reflexivity.
Qed.
(* end hide *)

Lemma findIndex_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    findIndex p (intersperse x l) =
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
  induction l as [| h t]; cbn.
    destruct (p x); reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn in *.
      destruct t; cbn in *.
        destruct (p h), (p x); reflexivity.
        destruct (intersperse x t); inversion Heq.
      destruct (p h), (p x), (p a) eqn: Hpa, t;
      cbn in *; try reflexivity; try inversion Heq.
        destruct (p a0); cbn.
          reflexivity.
          destruct (findIndex p t); inversion IHt.
        destruct (findIndex p l); cbn in *.
          destruct (intersperse x t); inversion Heq; subst.
            rewrite Hpa in *. destruct (findIndex p t).
              inversion IHt; cbn. Require Import Omega. f_equal. omega.
              inversion IHt.
            rewrite Hpa in *.
              destruct (findIndex p t); inversion IHt.
                f_equal. omega.
          destruct (intersperse x t); inversion Heq; subst;
          rewrite Hpa in *.
            destruct (findIndex p t); inversion IHt. reflexivity.
            destruct (findIndex p t); inversion IHt. reflexivity.
Qed.
(* end hide *)

Lemma count_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    count p (intersperse x l) =
    count p l + if p x then length l - 1 else 0.
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn.
    destruct (p x); reflexivity.
    destruct (p h), (p x), t; cbn; try reflexivity.
      admit.
      admit.
      admit.
      admit.
    rewrite e0 in IHl0. cbn in *. specialize (IHl0 p).
    destruct (p h), (p x), (p h') eqn: Hph';
    cbn in *; rewrite IHl0; try omega.
Abort.
(* end hide *)

Lemma filter_intersperse_false :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = false -> filter p (intersperse x l) = filter p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite <- (IHt H). destruct (intersperse x t); cbn in *.
      destruct (p h); reflexivity.
      destruct (p h), (p x), (p a); congruence.
Qed.
(* end hide *)

Lemma elem_intersperse :
  forall (A : Type) (x y : A) (l : list A),
    elem x (intersperse y l) <-> elem x l \/ (x = y /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (intersperse y t) eqn : Heq.
        inversion H; subst.
          do 2 left.
          inversion H2.
        inversion H; subst.
          do 2 left.
          inversion H2; subst.
            destruct t; cbn in *.
              inversion Heq.
              right. split; trivial. omega.
            destruct (IHt H3).
              left. right. assumption.
              destruct H0. right. split; [assumption | omega].
    destruct 1.
      induction H; cbn.
        destruct (intersperse y l); left.
        destruct (intersperse y t).
          inversion IHelem.
          do 2 right. assumption.
      destruct H; subst. destruct l as [| h [| h' t]]; cbn.
        1-2: cbn in H0; omega.
        destruct (intersperse y t); cbn.
          right. left.
          right. left.
Qed.
(* end hide *)

Lemma In_intersperse :
  forall (A : Type) (x y : A) (l : list A),
    In x (intersperse y l) <->
    In x l \/ (x = y /\ 2 <= length l).
(* begin hide *)
Proof.
  intros. rewrite ?In_elem. apply elem_intersperse.
Qed.

Lemma NoDup_intersperse :
  forall (A : Type) (x : A) (l : list A),
    NoDup (intersperse x l) -> length l <= 2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        apply le_S, le_n.
        destruct (intersperse x t); inversion Heq.
      inversion H. inversion H3. subst. specialize (IHt H7).
        destruct t as [| w1 [| w2 z]]; cbn in *.
          inversion Heq.
          apply le_n.
          destruct (intersperse x z).
            inversion Heq. subst. contradiction H6. right. left.
            inversion Heq; subst. contradiction H6. right. left.
Qed.
(* end hide *)

Lemma Dup_intersperse :
  forall (A : Type) (x : A) (l : list A),
    Dup (intersperse x l) -> 2 <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (intersperse x t) eqn: Heq.
      inversion H; inversion H1.
      destruct t; cbn in *.
        inversion Heq.
        apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma Rep_intersperse :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n (intersperse y l) <->
    Rep x n l \/ x = y /\ Rep x (S n - length l) l.
(* begin hide *)
Proof.
            Hint Constructors Rep.
  split; revert n.
    induction l as [| h t]; cbn; intros.
      inversion H; subst. left. constructor.
      destruct (intersperse y t) eqn: Heq.
        inv H.
          left. constructor.
          inv H2. left. do 2 constructor.
          inv H2. left. constructor.
        inv H.
          left. constructor.
          inv H2.
Admitted.
(* end hide *)

Lemma Exists_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Exists P (intersperse x l) <->
    Exists P l \/ (P x /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (intersperse x t) eqn: Heq.
        inv H.
          do 2 left. assumption.
          inv H1.
        inv H.
          do 2 left. assumption.
          inv H1.
            right. split; try assumption. destruct t; cbn in *.
              inv Heq.
              apply le_n_S, le_n_S, le_0_n.
            destruct (IHt H0).
              left. right. assumption.
              right. destruct H. split.
                assumption.
                destruct t; cbn in *.
                  inv H1.
                  apply le_n_S, le_n_S, le_0_n.
    destruct 1.
      induction H; cbn.
        destruct (intersperse x t); left; assumption.
        destruct (intersperse x t).
          inv IHExists.
          do 2 right. assumption.
      destruct H. destruct l as [| h [| h' t]]; cbn.
        inv H0.
        inv H0. inv H2.
        destruct (intersperse x t); cbn.
          right. left. assumption.
          right. left. assumption.
Qed.
(* end hide *)

Lemma Forall_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Forall P (intersperse x l) <->
    Forall P l /\ (2 <= length l -> P x).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      split; [constructor | inversion 1].
      destruct (intersperse x t) eqn: Heq.
        inv H. destruct (IHt H3). split.
          constructor; assumption.
          intro. apply H0. destruct t as [| h' [| h'' t']]; cbn in *.
            inv H1. inv H5.
            inv Heq.
            apply le_n_S, le_n_S, le_0_n.
        inv H. inv H3. destruct (IHt H4). split.
          constructor; assumption.
          intro. assumption.
    destruct 1. induction H; cbn in *.
      constructor.
      destruct (intersperse x t) eqn: Heq.
        repeat constructor; assumption.
        constructor; [assumption | constructor].
          apply H0. destruct t; cbn in *.
            inv Heq.
            apply le_n_S, le_n_S, le_0_n.
          apply IHForall. intro. apply H0. destruct t; cbn in *.
            inv Heq.
            omega.
Qed.
(* end hide *)

Lemma AtLeast_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    P x -> AtLeast P (length l - 1) (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        constructor.
        destruct (intersperse x t); inv Heq.
      constructor. destruct t; cbn in *; constructor.
        assumption.
        rewrite <- minus_n_O in IHt. apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    AtLeast P n l -> P x ->
      AtLeast P (n + (length l - 1)) (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    apply AtLeast_intersperse. assumption.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        inv H0. cbn. repeat constructor; assumption.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        rewrite <- plus_n_Sm. constructor.
          assumption.
          constructor.
            assumption.
            rewrite <- minus_n_O in IHAtLeast. apply IHAtLeast, H1.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        inv H. cbn. constructor.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        rewrite <- plus_n_Sm. apply AL_skip. constructor.
          assumption.
          rewrite <- minus_n_O in IHAtLeast. apply IHAtLeast, H0.
Qed.
(* end hide *)

Lemma AtLeast_intersperse'' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    AtLeast P n l -> ~ P x -> AtLeast P n (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          inv H0. constructor.
          destruct (intersperse x t); inv Heq.
      constructor.
        assumption.
        apply AL_skip. apply IHAtLeast, H1.
    destruct (intersperse x t) eqn: Heq.
      constructor. destruct t; cbn in *.
        inv H. constructor.
        destruct (intersperse x t); inv Heq.
      do 2 constructor. apply IHAtLeast, H0.
Qed.
(* end hide *)

Lemma Exactly_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    Exactly P n l -> P x ->
      Exactly P (n + (length l - 1)) (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          specialize (IHExactly H1). inv IHExactly. constructor.
          destruct (intersperse x t); inv Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          inv Heq.
          rewrite <- plus_n_Sm. constructor.
            assumption.
            rewrite <- minus_n_O in IHExactly. apply IHExactly, H1.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        constructor; [assumption | apply IHExactly, H1].
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t); inv Heq.
          constructor.
            assumption.
            rewrite <- plus_n_Sm. constructor.
              assumption.
              rewrite <- minus_n_O in *. apply IHExactly, H1.
          constructor.
            assumption.
            rewrite <- plus_n_Sm. constructor.
              assumption.
              rewrite <- minus_n_O in IHExactly. apply IHExactly, H1.
Restart.
  intros. revert dependent n.
  functional induction @intersperse A x l; cbn; intros.
    inv H. constructor.
    destruct t; cbn in *.
      rewrite plus_0_r. assumption.
      destruct (intersperse x t); inv e0.
    destruct t; cbn in *.
      inv e0.
      rewrite <- plus_n_Sm. inv H.
        cbn. do 2 try constructor; try assumption.
          rewrite <- minus_n_O in IHl0.
            destruct (intersperse x t); inv e0; apply IHl0; assumption.
        apply Ex_skip; try constructor; try assumption.
          rewrite <- minus_n_O in IHl0.
            destruct (intersperse x t); inv e0; apply IHl0; assumption.
Qed.
(* end hide *)

Lemma Exactly_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    Exactly P n l -> ~ P x ->
      Exactly P n (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    specialize (IHExactly H1). destruct (intersperse x t).
      constructor; assumption.
      do 2 try constructor; assumption.
    specialize (IHExactly H1). destruct (intersperse x t).
      inv IHExactly. repeat constructor; assumption.
      do 2 try constructor; try assumption.
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