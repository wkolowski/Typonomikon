Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(* begin hide *)
Fixpoint rev {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => snoc h (rev t)
end.
(* end hide *)

Lemma isEmpty_rev :
  forall (A : Type) (l : list A),
    isEmpty (rev l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    apply isEmpty_snoc.
Qed.
(* end hide *)

Lemma length_rev :
  forall (A : Type) (l : list A),
    length (rev l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma snoc_rev :
  forall (A : Type) (l : list A) (x : A),
    snoc x (rev l) = rev (x :: l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma rev_snoc :
  forall (A : Type) (x : A) (l : list A),
    rev (snoc x l) = x :: rev l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma rev_app :
  forall (A : Type) (l1 l2 : list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intro.
    rewrite app_nil_r. reflexivity.
    rewrite IHt1, snoc_app, snoc_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_rev :
  forall (A : Type) (l : list A),
    rev (rev l) = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite rev_snoc, IHt. reflexivity.
Qed.
(* end hide *)

(* GRUBA KRESKA ================================================= *)

Lemma map_rev :
  forall (A B : Type) (f : A -> B) (l : list A),
    map f (rev l) = rev (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite map_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma rev_join :
  forall (A : Type) (l : list (list A)),
    rev (join l) = join (rev (map rev l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite rev_app, join_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma rev_bind :
  forall (A B : Type) (f : A -> list B) (l : list A),
    rev (bind f l) = bind (fun x : A => rev (f x)) (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite rev_app, IHt, bind_snoc. reflexivity.
Qed.
(* end hide *)

Lemma rev_replicate :
  forall (A : Type) (n : nat) (x : A),
    rev (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn', snoc_replicate. cbn. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma iter_out :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iter f n (f x) = f (iter f n x).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

Lemma map_iterate_inv :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      map g (iterate f n (f x)) = iterate f n x.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite H, IHn'; trivial.
Qed.

Lemma rev_iterate_aux :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      rev (iterate g n (iter f n x)) = iterate f n (f x).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite <- map_iterate, <- map_rev, IHn', map_iterate_inv,
    snoc_iterate.
      cbn. reflexivity.
      all: assumption.
Qed.

Lemma rev_iterate_aux' :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      iterate f (S n) x = rev (iterate g (S n) (iter f n x)).
Proof.
  induction n as [| n']; cbn in *; intros.
    reflexivity.
    rewrite IHn'. rewrite ?iter_out, ?H. rewrite <- IHn'. cbn.
      do 2 f_equal. apply rev_iterate_aux. all: assumption.
Qed.
(* end hide *)

Lemma rev_iterate :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      rev (iterate f n x) = iterate g n (iter f (n - 1) x).
(* begin hide *)
Proof.
  destruct n; intros.
    cbn. reflexivity.
    rewrite (rev_iterate_aux' _ _ _ n _ H), rev_rev. 
      cbn. rewrite <- minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma last_rev :
  forall (A : Type) (l : list A),
    last (rev l) = head l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite last_snoc. reflexivity.
Qed.
(* end hide *)

Lemma head_rev :
  forall (A : Type) (l : list A),
    head (rev l) = last l.
(* begin hide *)
Proof.
  intros. rewrite <- last_rev, rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma tail_rev :
  forall (A : Type) (l : list A),
    tail (rev l) =
    match init l with
        | None => None
        | Some t => Some (rev t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite tail_snoc. destruct (rev t); cbn in *.
      destruct (init t).
        inversion IHt.
        reflexivity.
      destruct (init t); cbn; inversion IHt; subst. reflexivity.
Qed.
(* end hide *)

Lemma init_rev :
  forall (A : Type) (l : list A),
    init (rev l) =
    match tail l with
        | None => None
        | Some t => Some (rev t)
    end.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l) at 2. rewrite tail_rev.
  destruct (init (rev l)); rewrite ?rev_rev; reflexivity.
Qed.
(* end hide *)



(* TODO:
uncons
unsnoc
nth
insert
remove (TODO)
take
drop
splitAt
zip
unzip
zipWith
unzipWith
*)