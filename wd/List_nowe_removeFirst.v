Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(** * [rmFirst] *)

(* Połączenie [takeWhile], [find], [dropWhile] i [removeFirst].
   Ciekawe, dlaczego wcześniej tego nie zauważyłem. *)

Print takeWhile.
Print find.
Print dropWhile.
Print removeFirst.

(* begin hide *)
Fixpoint rmFirst
  {A : Type} (p : A -> bool) (l : list A) : option (list A * A * list A) :=
match l with
    | [] => None
    | h :: t =>
        if p h
        then Some ([], h, t)
        else
          match rmFirst p t with
              | None => None
              | Some (b, x, e) => Some (h :: b, x, e)
          end
end.

Fixpoint rmLast
  {A : Type} (p : A -> bool) (l : list A) : option (list A * A * list A) :=
match l with
    | [] => None
    | h :: t =>
        match rmLast p t with
            | None => if p h then Some ([], h, t) else None
            | Some (b, x, e) => Some (h :: b, x, e)
        end
end.
(* end hide *)

Lemma rmFirst_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    match rmFirst p l with
        | None => forall x : A, elem x l -> p x = false
        | Some (b, x, e) =>
            b = takeWhile (fun x : A => negb (p x)) l /\
            Some x = find p l /\
            x :: e = dropWhile (fun x : A => negb (p x)) l /\
            Some (x, b ++ e) = removeFirst p l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph; cbn.
      repeat split; reflexivity.
      destruct (rmFirst p t) eqn: Heq.
        destruct p0, p0. decompose [and] IHt; clear IHt.
          rewrite <- H3, ?H, H0. cbn. repeat split. assumption.
        intros. inv H.
          assumption.
          apply IHt. assumption.
Qed.
(* end hide *)

Lemma rmFirst_wut :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> l = b ++ x :: e.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. inv H. cbn. f_equal. apply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma isEmpty_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    inv H.
    reflexivity.
Qed.
(* end hide *)

Lemma length_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> length b + length e < length l.
(* begin hide *)
Proof.
  intros. apply rmFirst_wut in H. subst. rewrite length_app. cbn.
  rewrite <- plus_n_Sm. apply le_n.
Qed.
(* end hide *)

Lemma rmFirst_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    rmFirst p (snoc x l) =
    match rmFirst p l with
        | None => if p x then Some (l, x, []) else None
        | Some (b, y, e) => Some (b, y, snoc x e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h).
      reflexivity.
      rewrite IHt. destruct (rmFirst p t).
        destruct p0, p0. reflexivity.
        destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    rmFirst p (l1 ++ l2) =
    match rmFirst p l1, rmFirst p l2 with
        | Some (b, x, e), _ => Some (b, x, e ++ l2)
        | _, Some (b, x, e) => Some (l1 ++ b, x, e)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (rmFirst p l2).
      destruct p0, p0. 1-2: reflexivity.
    destruct (p h).
      reflexivity.
      rewrite IHt. destruct (rmFirst p t).
        destruct p0, p0. reflexivity.
        destruct (rmFirst p l2).
          destruct p0, p0. all: reflexivity.
Qed.
(* end hide *)

Lemma rmLast_snoc' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    rmLast p (l ++ [x]) =
    if p x
    then Some (l, x, [])
    else
      match rmLast p l with
          | None => None
          | Some (b, y, e) => Some (b, y, e ++ [x])
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. destruct (p x) eqn: Hpx.
      reflexivity.
      destruct (rmLast p t) eqn: Heq.
        destruct p0, p0. reflexivity.
        destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_rev_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    rmFirst p l =
    match rmLast p (rev l) with
        | None => None
        | Some (b, x, e) => Some (rev e, x, rev b)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite rmLast_snoc', Hph, rev_inv. cbn. reflexivity.
      rewrite rmLast_snoc', Hph, IHt. destruct (rmLast p (rev t)).
        destruct p0, p0. rewrite rev_app. cbn. all: reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    rmFirst p (rev l) =
    match rmLast p l with
        | None => None
        | Some (b, x, e) => Some (rev e, x, rev b)
    end.
(* begin hide *)
Proof.
  intros. rewrite rmFirst_rev_aux, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    rmFirst p (map f l) =
    match rmFirst (fun x : A => p (f x)) l with
        | None => None
        | Some (b, x, e) => Some (map f b, f x, map f e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p (f h)).
      reflexivity.
      rewrite IHt. destruct (rmFirst _ t).
        destruct p0, p0. cbn. all: reflexivity.
Qed.
(* end hide *)

(* TODO: join, bind *)

Lemma rmFirst_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    rmFirst p (replicate n x) =
    if andb (leb 1 n) (p x)
    then Some ([], x, replicate (n - 1) x)
    else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct (p x) eqn: Hpx.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. cbn. destruct n'; cbn; rewrite ?Hpx; reflexivity.
Qed.
(* end hide *)

(* TODO: iterate *)

Lemma rmFirst_any :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> any p l = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. inv H. eapply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma rmFirst_all :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      all p l = andb (beq_nat (length b) 0) (all p e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_find :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> find p l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_removeFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      removeFirst p l = Some (x, b ++ e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. erewrite IHt; reflexivity.
Qed.
(* end hide *)

(* TODO: findIndex *)

Lemma count_rmFirst_l :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> count p b = 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. cbn. rewrite Hph.
          eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma count_rmFirst_r :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      count p e < length l - length b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. cbn. apply le_n_S. apply count_length.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. cbn. apply IHt. reflexivity.
Qed.
(* end hide *)

Lemma rmFirst_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    rmFirst p (filter p l) =
    match filter p l with
        | [] => None
        | h :: t => Some ([], h, t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite Hph. reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma filter_rmFirst_l :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> filter p b = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. cbn. rewrite Hph.
          eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma takeWhile_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      takeWhile (fun x : A => negb (p x)) l = b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. f_equal. eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma dropWhile_rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) ->
      dropWhile (fun x : A => negb (p x)) l = x :: e.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. reflexivity.
      destruct (rmFirst p t).
        destruct p0, p0. all: inv H. eapply IHt. reflexivity.
Qed.
(* end hide *)

(*
Lemma pmap_rmFirst :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    rmFirst p (pmap f l) =
    match
      rmFirst
        (fun x : A => match f x with None => false | Some b => p b end)
        l
    with
        | None => None
        | Some (b, x, e) => Some (pmap f b, f x, pmap f e)
    end.
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)
*)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)

Lemma rmFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    rmFirst p l = Some (b, x, e) -> .
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.

Qed.
(* end hide *)



Lemma rmLast_rev_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    rmLast p l =
    match rmFirst p (rev l) with
        | None => None
        | Some (b, x, e) => Some (rev e, x, rev b)
    end.
(* begin hide *)
Proof.
  intros. rewrite rmFirst_rev. destruct (rmLast p l).
    destruct p0, p0. rewrite ?rev_inv. all: reflexivity.
Qed.
(* end hide *)

Lemma rmLast_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    match rmLast p l with
        | None => forall x : A, elem x l -> p x = false
        | Some (b, x, e) =>
            x :: rev b = rev (dropWhile p l) /\
            e = rev (takeWhile p l) /\
            Some x = findLast p l /\
            Some (x, b ++ e) = removeLast p l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (rmLast p t) eqn: Heq.
      destruct p0, p0. decompose [and] IHt; clear IHt.
        destruct (p h) eqn: Hph; cbn; subst. Focus 2.
          repeat split.
Abort.
(* end hide *)