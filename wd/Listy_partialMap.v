Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Fixpoint pmap {A B : Type} (f : A -> option B) (l : list A) : list B :=
match l with
    | [] => []
    | h :: t =>
        match f h with
            | None => pmap f t
            | Some x => x :: pmap f t
        end
end.

(*


isEmpty (TODO)
length

iterate

nth
last
tail i init

take i drop
takedrop

partition

takeWhile i dropWhile
takedropWhile

zip
unzip
zipWith
unzipWith
intersperse

any
all
find i findLast
removeFirst i removeLast
findIndex
count
findIndices
*)

Lemma pmap_app :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    pmap f (l1 ++ l2) = pmap f l1 ++ pmap f l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_rev :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f (rev l) = rev (pmap f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_app. cbn. destruct (f h); cbn; rewrite ?IHt, ?app_nil_r.
      all: reflexivity.
Qed.
(* end hide *)

Lemma pmap_map :
  forall (A B C : Type) (f : A -> B) (g : B -> option C) (l : list A),
    pmap g (map f l) = pmap (fun x : A => g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (g (f h)); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_join :
  forall (A B : Type) (f : A -> option B) (l : list (list A)),
    pmap f (join l) = join (map (pmap f) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_app. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma pmap_bind :
  forall (A B C : Type) (f : A -> list B) (g : B -> option C) (l : list A),
    pmap g (bind f l) = bind (fun x : A => pmap g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_app. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma pmap_replicate :
  forall (A B : Type) (f : A -> option B) (n : nat) (x : A),
    pmap f (replicate n x) =
    match f x with
        | None => []
        | Some y => replicate n y
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct (f x); reflexivity.
    rewrite IHn'. destruct (f x); reflexivity.
Qed.
(* end hide *)

(* TODO: iterate *)

Definition isSome {A : Type} (x : option A) : bool :=
match x with
    | None => false
    | _ => true
end.

Lemma head_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    head (pmap f l) =
    match find isSome (map f l) with
        | None => None
        | Some x => x
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

(* TODO: tail, last, init *)

(* TODO *) Lemma pmap_filter :
  forall (A B : Type) (p : B -> bool) (f : A -> option B) (l : list A),
    filter p (pmap f l) =
    pmap f
      (filter
        (fun x : A => match f x with | Some b => p b | _ => false end)
        l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Hfh; cbn; rewrite ?IHt.
      destruct (p b); cbn; rewrite ?Hfh; reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma pmap_zip :
  forall
    (A B C : Type)
    (fa : A -> option C) (fb : B -> option C)
    (la : list A) (lb : list B),
      pmap
        (fun '(a, b) =>
        match fa a, fb b with
            | Some a', Some b' => Some (a', b')
            | _, _ => None
        end)
        (zip la lb) =
      zip (pmap fa la) (pmap fb lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct (fa ha); cbn.
        reflexivity.
        rewrite zip_nil_r. reflexivity.
      destruct (fa ha); cbn.
        destruct (fb hb) eqn: Hfbhb; cbn.
          rewrite IHta. reflexivity.
          destruct tb; cbn.
            rewrite zip_nil_r. cbn. reflexivity.
Admitted.
(* end hide *)

Lemma pmap_intersperse :
  forall (A B : Type) (f : A -> option B) (x : A) (l : list A),
    pmap f (intersperse x l) =
    match f x with
        | None => pmap f l
        | Some y => intersperse y (pmap f l)
    end.
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn.
    destruct (f x); reflexivity.
    destruct (f h), (f x); reflexivity.
    cbn in *. rewrite IHl0. destruct (f h), (f x); try reflexivity.
      destruct (f _x).
        reflexivity.
        cbn.
      cbn in IHl0. rewrite Hf_x in IHl0.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f l =.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)