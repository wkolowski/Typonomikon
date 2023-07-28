(** * D1e: Podstawowe funkcje na listach [TODO] *)

(** * Podstawowe funkcje na listach (TODO) *)

(** * [foldr], czyli standardowa reguła rekursji dla list (TODO) *)

From Typonomikon Require Import D5a.

Fixpoint foldr
  {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : B :=
match l with
| [] => b
| h :: t => f h (foldr f b t)
end.

(** Nie będę na razie tłumaczył, jaka ideologia stoi za [foldr] i [foldl].
    Napiszę o tym później, a na razie porcja zadań.

    Zaimplementuj za pomocą [foldr] następujące funkcje:
    [length], [app], [rev], [map], [join], [filter], [takeWhile],
    [dropWhile].

    Udowodnij, że zdefiniowane przez ciebie funkcje pokrywają się ze
    swoimi klasycznymi odpowiednikami. *)

(* begin hide *)
(* Reszta polecenia: [repeat], [nth], [take], [drop] *)

Functional Scheme foldr_ind := Induction for foldr Sort Prop.

Definition lengthF {A : Type} (l : list A) : nat :=
  foldr (fun _ => S) 0 l.

Definition snocF {A : Type} (x : A) (l : list A) : list A :=
  foldr (@cons A) [x] l.

Definition appF {A : Type} (l1 l2 : list A) : list A :=
  foldr (@cons A) l2 l1.

Definition revF {A : Type} (l : list A) : list A :=
  foldr snoc [] l.

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

Definition findIndexF
  {A : Type} (p : A -> bool) (l : list A) : option nat :=
    foldr (fun h t => if p h then Some 0 else option_map S t) None l.

Definition countF {A : Type} (p : A -> bool) (l : list A) : nat :=
  foldr (fun h t => (if p h then 1 else 0) + t) 0 l.

Definition filterF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then h :: t else t) [] l.

Definition takeWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then h :: t else []) [] l.

Ltac solve_foldr := intros;
match goal with
| |- context [@foldr ?A ?B ?f ?a ?l] =>
  functional induction @foldr A B f a l; cbn; trivial;
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
  intros. unfold lengthF. solve_foldr.
Qed.
(* end hide *)

Lemma snocF_spec :
  forall (A : Type) (x : A) (l : list A),
    snocF x l = snoc x l.
(* begin hide *)
Proof.
  intros. unfold snocF. solve_foldr.
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
  intros. unfold appF. solve_foldr.
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
  intros. unfold revF. solve_foldr.
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
  intros. unfold mapF. solve_foldr.
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
  intros. unfold joinF. solve_foldr.
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

Lemma findIndexF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndexF p l = findIndex p l.
(* begin hide *)
Proof.
  unfold findIndexF.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      rewrite IHt.
      destruct (findIndex p t); cbn; reflexivity.
Qed.
(* end hide *)

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
  intros. unfold filterF. solve_foldr.
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
  intros. unfold takeWhileF. solve_foldr.
Qed.
(* end hide *)

(** ** Lematy o foldach (TODO) *)

Lemma foldr_app :
  forall (A B : Type) (f : A -> B -> B) (b : B) (l1 l2 : list A),
    foldr f b (l1 ++ l2) = foldr f (foldr f b l2) l1.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma foldr_map :
  forall (A A' B : Type) (f : A' -> B -> B) (g : A -> A') (b : B) (l : list A),
    foldr f b (map g l) = foldr (fun a x => f (g a) x) b l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; [easy |].
  now rewrite IHt.
Qed.
(* end hide *)