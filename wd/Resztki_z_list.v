Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.



(** *** Dziwne *)

(** TODO: Wstawić tu jakąś ideologię. *)

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

(** * Niestandardowe reguły indukcyjne *)

(** Wyjaśnienia nadejdą już wkrótce. *)

Fixpoint list_ind_2
  (A : Type) (P : list A -> Prop)
  (H0 : P [])
  (H1 : forall x : A, P [x])
  (H2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
    (l : list A) : P l.
(* begin hide *)
Proof.
  destruct l as [| x [| y l]]; cbn; auto.
  apply H2. apply list_ind_2; auto.
Qed.
(* end hide *)

Lemma list_ind_rev :
  forall (A : Type) (P : list A -> Prop)
    (Hnil : P [])
    (Hsnoc : forall (h : A) (t : list A), P t -> P (t ++ [h]))
      (l : list A), P l.
(* begin hide *)
Proof.
  intros. cut (forall l : list A, P (rev l)); intro.
    specialize (H (rev l)). rewrite <- rev_inv. assumption.
    induction l0 as [| h t]; cbn.
      assumption.
      apply Hsnoc. assumption.
Qed.
(* end hide *)

Lemma list_ind_app_l :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l' ++ l))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    assumption.
    apply (IH _ [h]). assumption.
Qed.
(* end hide *)

Lemma list_ind_app_r :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t] using list_ind_rev; cbn.
    assumption.
    apply (IH t [h]). assumption.
Qed.
(* end hide *)

Lemma list_ind_app :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (IH : forall l l' : list A, P l -> P l' -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    assumption.
    apply (IH [h] t); auto.
Qed.
(* end hide *)

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

(** Skopiowane z biblioteki standardowej Haskella. Czoś mię się zdaję, że
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

Lemma scanl_rev :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    scanl f a (rev l) = rev (scanr (flip f) a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite scanl_snoc, IHt. 
Abort.
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