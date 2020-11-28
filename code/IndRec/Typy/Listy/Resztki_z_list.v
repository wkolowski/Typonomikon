Require Import D5.

(** *** Dziwne *)

(** TODO: Wstawić tu jakąś ideologię. *)

Fixpoint revapp {A : Type} (l1 l2 : list A) : list A :=
match l1 with
    | [] => l2
    | h :: t => revapp t (h :: l2)
end.

Definition app' {A : Type} (l1 l2 : list A) : list A :=
  revapp (revapp l1 []) l2.

Lemma revapp_spec :
  forall (A : Type) (l1 l2 : list A),
    revapp l1 l2 = rev l1 ++ l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros; trivial.
    rewrite IHt, <- app_assoc. cbn. trivial.
Qed.
(* end hide *)

Lemma app'_spec :
  forall (A : Type) (l1 l2 : list A),
    app' l1 l2 = l1 ++ l2.
(* begin hide *)
Proof.
  unfold app'. intros. rewrite !revapp_spec, app_nil_r, rev_inv. trivial.
Qed.
(* end hide *)

Definition rev' {A : Type} (l : list A) : list A :=
  revapp l [].

(** ** [foldr] i [foldl] *)

Fixpoint foldr
  {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : B :=
match l with
    | [] => b
    | h :: t => f h (foldr f b t)
end.

Fixpoint foldl
  {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : A :=
match l with
    | [] => a
    | h :: t => foldl f (f a h) t
end.

(** Nie będę na razie tłumaczył, jaka ideologia stoi za [foldr] i [foldl].
    Napiszę o tym później, a na razie porcja zadań.

    Zaimplementuj za pomocą [foldr] i [foldl] następujące funkcje:
    [length], [app], [rev], [map], [join], [filter], [takeWhile],
    [dropWhile].

    Udowodnij, że zdefiniowane przez ciebie funkcje pokrywają się ze
    swoimi klasycznymi odpowiednikami. *)

(* begin hide *)
(* Reszta polecenia: [repeat], [nth], [take], [drop] *)

Functional Scheme foldr_ind := Induction for foldr Sort Prop.
Functional Scheme foldl_ind := Induction for foldl Sort Prop.

Definition lengthF {A : Type} (l : list A) : nat :=
  foldr (fun _ => S) 0 l.

Definition snocF {A : Type} (x : A) (l : list A) : list A :=
  foldr (@cons A) [x] l.

Definition appF {A : Type} (l1 l2 : list A) : list A :=
  foldr (@cons A) l2 l1.

Definition revF {A : Type} (l : list A) : list A :=
  foldr (fun h t => t ++ [h]) [] l.

Definition revF' {A : Type} (l : list A) : list A :=
  foldl (fun t h => h :: t) [] l.

Definition mapF {A B : Type} (f : A -> B) (l : list A) : list B :=
  foldr (fun h t => f h :: t) [] l.

Definition joinF {A : Type} (l : list (list A)) : list A :=
  foldr app [] l.

Require Import Bool.

Definition allF {A : Type} (p : A -> bool) (l : list A) : bool :=
  foldr (fun h t => p h && t) true l.

Definition anyF {A : Type} (p : A -> bool) (l : list A) : bool :=
  foldr (fun h t => p h || t) false l.

Definition findF {A : Type} (p : A -> bool) (l : list A) : option A :=
  foldr (fun h t => if p h then Some h else t) None l.

(*
Definition removeFirstF
  {A : Type} (p : A -> bool) (l : list A) : option A :=
    foldr (fun h t => if p h then Some t else t) None l.
*)

Definition findIndexF
  {A : Type} (p : A -> bool) (l : list A) : option nat :=
    foldr (fun h t => if p h then Some 0 else t) None l.

Definition countF {A : Type} (p : A -> bool) (l : list A) : nat :=
  foldr (fun h t => (if p h then 1 else 0) + t) 0 l.

Definition filterF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then h :: t else t) [] l.

Definition takeWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then h :: t else []) [] l.

(*Definition dropWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then t else h :: t) [] l.*)

(*Definition dropWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldl (fun t h => if p h then t else h :: t) [] l.*)

Ltac solve_fold := intros;
match goal with
    | |- context [@foldr ?A ?B ?f ?a ?l] =>
        functional induction @foldr A B f a l; cbn; trivial;
        match goal with
            | H : ?x = _ |- context [?x] => rewrite ?H; auto
        end
    | |- context [@foldl ?A ?B ?f ?a ?l] =>
        functional induction @foldl A B f a l; cbn; trivial;
        match goal with
            | H : ?x = _ |- context [?x] => rewrite ?H; auto
        end
end.

(* end hide *)

Lemma lengthF_spec :
  forall (A : Type) (l : list A),
    lengthF l = length l.
(* begin hide *)
Proof.
  unfold lengthF; induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold lengthF. solve_fold.
Qed.
(* end hide *)

Lemma snocF_spec :
  forall (A : Type) (x : A) (l : list A),
    snocF x l = snoc x l.
(* begin hide *)
Proof.
  intros. unfold snocF. solve_fold.
Qed.
(* end hide *)

Lemma appF_spec :
  forall (A : Type) (l1 l2 : list A),
    appF l1 l2 = l1 ++ l2.
(* begin hide *)
Proof.
  unfold appF; induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    rewrite IHt1. trivial.
Restart.
  intros. unfold appF. solve_fold.
Qed.
(* end hide *)

Lemma revF_spec :
  forall (A : Type) (l : list A),
    revF l = rev l.
(* begin hide *)
Proof.
  unfold revF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold revF. solve_fold.
Qed.
(* end hide *)

(* begin hide *)
Lemma revF'_spec :
  forall (A : Type) (l : list A),
    revF' l = rev l.
Proof.
  unfold revF'. intros. replace (rev l) with (rev l ++ []).
    remember [] as acc. clear Heqacc. generalize dependent acc.
    induction l as [| h t]; cbn; intros; subst.
      trivial.
      rewrite IHt. rewrite <- app_cons_r. trivial.
    apply app_nil_r.
Qed.
(* end hide *)

Lemma mapF_spec :
  forall (A B : Type) (f : A -> B) (l : list A),
    mapF f l = map f l.
(* begin hide *)
Proof.
  unfold mapF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold mapF. solve_fold.
Qed.
(* end hide *)

Lemma joinF_spec :
  forall (A : Type) (l : list (list A)),
    joinF l = join l.
(* begin hide *)
Proof.
  unfold joinF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold joinF. solve_fold.
Qed.
(* end hide *)

Lemma allF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    allF p l = all p l.
(* begin hide *)
Proof.
  unfold allF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      assumption.
      reflexivity.
Qed.
(* end hide *)

Lemma anyF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    anyF p l = any p l.
(* begin hide *)
Proof.
  unfold anyF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma findF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    findF p l = find p l.
(* begin hide *)
Proof.
  unfold findF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

(* TODO: Lemma findIndexF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndexF p l = findIndex p l.
(* begin hide *)
Proof.
  unfold findIndexF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)
*)

Lemma countF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    countF p l = count p l.
(* begin hide *)
Proof.
  unfold countF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      rewrite IHt. reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma filterF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    filterF p l = filter p l.
(* begin hide *)
Proof.
  unfold filterF; induction l as [| h t].
    cbn. trivial.
    cbn. rewrite IHt. trivial.
Restart.
  intros. unfold filterF. solve_fold.
Qed.
(* end hide *)

Lemma takeWhileF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    takeWhileF p l = takeWhile p l.
(* begin hide *)
Proof.
  unfold takeWhileF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold takeWhileF. solve_fold.
Qed.
(* end hide *)

(** Lematy o foldach *)

Lemma foldr_app :
  forall (A B : Type) (f : A -> B -> B) (b : B) (l1 l2 : list A),
    foldr f b (l1 ++ l2) = foldr f (foldr f b l2) l1.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.

Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Lemma foldr_rev :
  forall (A B : Type) (f : A -> B -> B) (l : list A) (b : B),
    foldr f b (rev l) = foldl (flip f) b l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite foldr_app. cbn. rewrite IHt. unfold flip. reflexivity.
Qed.

(*Lemma foldr_map :
  forall (A B C : Type) (f : B -> C -> C) (g : A -> B) (b : B)
    (l : list A),
    foldr f a (map g l) = foldr (fun a b => g (f a b)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite foldl_snoc. rewrite IHt.
Qed.
(* end hide *)
*)

Lemma foldl_app :
  forall (A B : Type) (f : A -> B -> A) (l1 l2 : list B) (a : A),
    foldl f a (l1 ++ l2) = foldl f (foldl f a l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma foldl_snoc :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A) (b : B),
    foldl f a (l ++ [b]) = f (foldl f a l) b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma foldl_rev :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    foldl f a (rev l) = foldr (flip f) a l.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_inv _ l). rewrite foldr_rev.
  rewrite rev_inv. reflexivity.
Qed.
(* end hide *)

(** Skopiowane z biblioteki standardowej Haskella. Czoś mię się zdaję, że
    jednak tewo nie rozumię... *)

Fixpoint scanl
  {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : list A :=
    a ::
match l with
    | [] => []
    | h :: t => scanl f (f a h) t
end.

Compute scanl plus 0 [1; 2; 3; 4; 5].

Definition scanl1
  {A : Type} (f : A -> A -> A) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => scanl f h t
end.

Compute scanl1 plus [1; 2; 3; 4; 5].

Fixpoint scanr
  {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : list B :=
match l with
    | [] => [b]
    | h :: t =>
        let
          qs := scanr f b t
        in
        match qs with
            | [] => [f h b]
            | q :: _ => f h q :: qs
        end
end.

Compute scanr plus 0 [1; 2; 3; 4; 5].

Fixpoint scanr1
  {A : Type} (f : A -> A -> A) (l : list A) : list A :=
match l with
    | [] => []
    | [h] => [h]
    | h :: t =>
        let
          qs := scanr1 f t
        in
        match qs with
            | [] => []
            | q :: _ => f h q :: qs
        end
end.

Compute scanr1 plus [1; 2; 3; 4; 5].

Lemma isEmpty_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    isEmpty (scanl f a l) = false.
(* begin hide *)
Proof.
  destruct l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    length (scanl f a l) = 1 + length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma scanl_app :
  forall (A B : Type) (f : A -> B -> A) (l1 l2 : list B) (a : A),
    scanl f a (l1 ++ l2) = 
    take (length l1) (scanl f a l1) ++ scanl f (foldl f a l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    f_equal. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma scanl_snoc :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A) (b : B),
    scanl f a (l ++ [b]) = scanl f a l ++ [foldl f a (l ++ [b])].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma head_scanr :
  forall (A B : Type) (f : A -> B -> B) (b : B) (l : list A),
    head (scanr f b l) =
      match l with
          | [] => Some b
          | _  => Some (foldl (flip f) b (rev l))
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (scanr f b t) eqn: Heq; cbn in *.
      destruct t; inv IHt.
      destruct t; inv IHt.
        inv Heq. cbn. reflexivity.
        cbn. rewrite !foldl_app. unfold flip; cbn. reflexivity.
Qed.
(* end hide *)

Lemma scanl_rev :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    scanl f a (rev l) = rev (scanr (flip f) a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite scanl_snoc, IHt. destruct (scanr (flip f) a t) eqn: Heq.
      destruct t; cbn in Heq.
        inversion Heq.
        destruct (scanr (flip f) a t); inversion Heq.
      rewrite foldl_app. cbn. unfold flip. do 3 f_equal.
        apply (f_equal head) in Heq. rewrite head_scanr in Heq.
          destruct t; inv Heq.
            cbn. reflexivity.
            cbn. rewrite !foldl_app. unfold flip; cbn. reflexivity.
Qed.
(* end hide *)

Lemma head_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    head (scanl f a l) = Some a.
(* begin hide *)
Proof.
  destruct l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma last_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    last (scanl f a l) = Some (foldl f a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (scanl f (f a h) t) eqn: Heq.
      apply (f_equal isEmpty) in Heq. rewrite isEmpty_scanl in Heq.
        cbn in Heq. congruence.
      rewrite <- Heq, IHt. reflexivity.
Qed.
(* end hide *)

(** TODO: reguły indukcyjne *)

Fixpoint rot2 {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [x] => [x]
    | x :: y :: t => y :: x :: rot2 t
end.

Fixpoint list_ind_2
  {A : Type} (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (Hcons2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
  (l : list A) : P l :=
match l with
    | [] => Hnil
    | [x] => Hsingl x
    | x :: y :: l' => Hcons2 x y l' (list_ind_2 P Hnil Hsingl Hcons2 l')
end.

Lemma rot2_involution :
  forall (A : Type) (l : list A),
    rot2 (rot2 l) = l.
Proof.
  intro. apply list_ind_2; cbn; intros.
    1-2: reflexivity.
    rewrite H. reflexivity.
Qed.

Inductive Rot2 {A : Type} : list A -> list A -> Prop :=
    | Rot2_nil : Rot2 [] []
    | Rot2_singl : forall x : A, Rot2 [x] [x]
    | Rot2_cons2 :
        forall (x y : A) (l l' : list A),
          Rot2 l l' -> Rot2 (x :: y :: l) (y :: x :: l').

Lemma Rot2_correct :
  forall (A : Type) (l : list A),
    Rot2 l (rot2 l).
Proof.
  intro. apply list_ind_2; cbn; constructor. assumption.
Qed.

Lemma Rot2_complete :
  forall (A : Type) (l l' : list A),
    Rot2 l l' -> rot2 l = l'.
Proof.
  induction 1; cbn.
    1-2: reflexivity.
    rewrite IHRot2. reflexivity.
Qed.