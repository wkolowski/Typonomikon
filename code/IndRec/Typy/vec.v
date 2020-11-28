(** * X5: Listy o znanej długości *)

(* begin hide *)

(*Require Import Coq.Classes.Morphisms.
Require Export MyList.
Require Import Monads.
Require Import JMeq.
Require Import Ring.*)

Require Import List.
Import ListNotations.

Require Import JMeq.
Require Import Eqdep.
Require Import Arith.

Arguments eq_dep [U P p] _ [q] _.

Set Implicit Arguments.

Inductive vec (A : Type) : nat -> Type :=
    | vnil : vec A 0
    | vcons : forall n : nat, A -> vec A n -> vec A (S n).

Arguments vnil {A}.
Arguments vcons {A n} _ _.

(** *** [length] *)

(** Zdefiniuj funkcję [len], która oblicza długość listy. Powinna ona
    wykonywać się w czasie liniowym. *)

(* begin hide *)
Definition len {A : Type} {n : nat} (_ : vec A n) : nat := n.
(* end hide *)

Lemma len_vnil :
  forall A : Type, len (@vnil A) = 0.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma len_vcons' :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    len (vcons h t) = S n.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Lemma len_vcons :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    len (vcons h t) = S (len t).
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

(** * [app] *)

(** Zdefiniuj funkcję [app], która skleja dwie listy. *)

(* begin hide *)
Fixpoint app {A : Type} {n m : nat} (l1 : vec A n) (l2 : vec A m)
  : vec A (n + m) :=
match l1 with
    | vnil => l2
    | vcons h t => vcons h (app t l2)
end.
(* end hide *)

Notation "l1 +++ l2" := (app l1 l2) (at level 40).

Lemma app_vnil_l :
  forall (A : Type) (n : nat) (l : vec A n), vnil +++ l = l.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma JMeq_vcons :
  forall (A : Type) (n m : nat) (h h' : A) (t : vec A n) (t' : vec A m),
    n = m -> JMeq h h' -> JMeq t t' -> JMeq (vcons h t) (vcons h' t').
(* end hide *)
Proof.
  intros. subst. reflexivity.
Qed.
(* end hide *)

Lemma app_vnil_r :
  forall (A : Type) (n : nat) (l : vec A n), JMeq (l +++ vnil) l.
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn.
    trivial.
    apply JMeq_vcons; auto.
Qed.
(* end hide *)

Lemma app_vnil_r' :
  forall (A : Type) (n : nat) (l : vec A n), eq_dep (l +++ vnil) l.
(* begin hide *)
Proof.
  induction l; cbn; try rewrite IHl; trivial.
Qed.
(* end hide *)

Lemma app_assoc :
  forall (A : Type) (x y z : nat) (l1 : vec A x) (l2 : vec A y) (l3 : vec A z),
    eq_dep (l1 +++ (l2 +++ l3)) ((l1 +++ l2) +++ l3).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    rewrite IHl1. trivial.
Qed.
(* end hide *)

Lemma app_assoc' :
  forall (A : Type) (x y z : nat) (l1 : vec A x) (l2 : vec A y) (l3 : vec A z),
    JMeq (l1 +++ (l2 +++ l3)) ((l1 +++ l2) +++ l3).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    apply JMeq_vcons; auto. rewrite plus_assoc. trivial.
Qed.
(* end hide *)

Lemma app_len :
  forall (A : Type) (n m : nat) (l1 : vec A n) (l2 : vec A m),
    len (l1 +++ l2) = len l1 + len l2.
(* begin hide *)
Proof.
  intros. unfold len. trivial.
Qed.
(* end hide *)

Lemma app_cons :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    (vcons x l1) +++ l2 = vcons x (l1 +++ l2).
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Lemma app_cons2 :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    JMeq (l1 +++ vcons x l2) ((l1 +++ (vcons x vnil)) +++ l2).
(* begin hide *)
Proof.
  induction l1 as [| n h1 t1]; cbn; intros.
    trivial.
    apply JMeq_vcons; auto. rewrite <- plus_assoc. f_equal.
Qed.
(* end hide *)

Lemma app_cons2' :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    eq_dep (l1 +++ vcons x l2) ((l1 +++ (vcons x vnil)) +++ l2).
(* begin hide *)
Proof.
  induction l1 as [| n h1 t1]; cbn; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Require Import Lia Arith.

Lemma no_infinite_cons :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    eq_dep t (vcons h t) -> False.
(* begin hide *)
Proof.
  inversion 1. lia.
Qed.
(* end hide *)

Lemma no_infinite_app :
  forall (A : Type) (n m : nat) (l : vec A n) (l' : vec A m),
    ~ eq_dep l' vnil -> eq_dep l (l' +++ l) -> False.
(* begin hide *)
Proof.
  induction l; cbn; intros.
    rewrite app_vnil_r' in H0. apply H. rewrite H0. trivial.
    destruct l'.
      contradiction H. trivial.
      inversion H0. lia.
Qed.
(* end hide *)

Lemma app_inv1 :
  forall (A : Type) (n m : nat) (l : vec A n) (l1 l2 : vec A m),
    l +++ l1 = l +++ l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction l; cbn; intros.
    assumption.
    apply IHl. inversion H. apply inj_pair2 in H1. assumption.
Qed.
(* end hide *)

Lemma is_vnil :
  forall (A : Type) (n : nat) (l : vec A n),
    {eq_dep l vnil} + {~ eq_dep l vnil}.
(* begin hide *)
Proof.
  destruct l; [left | right].
    trivial.
    inversion 1.
Qed.
(* end hide *)

Require Import Coq.Program.Equality.

Lemma app_inv2 :
  forall (A : Type) (n m : nat) (l : vec A n) (l1 l2 : vec A m),
    eq_dep (l1 +++ l) (l2 +++ l) -> eq_dep l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    destruct (is_vnil l2).
      rewrite e. trivial.
      cut False.
        inversion 1.
        eapply no_infinite_app; eauto.
    dependent destruction l2.
      inversion H. subst. apply inj_pair2 in H2.
      erewrite IHl1; eauto. rewrite H2. trivial.
Qed.
(* end hide *)

Lemma app_eq_nil :
  forall (A : Type) (n m : nat) (l1 : vec A n) (l2 : vec A m),
    eq_dep (l1 +++ l2) vnil -> eq_dep l1 vnil /\ eq_dep l2 vnil.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    split; trivial.
    inversion H.
Qed.
(* end hide *)

(** Zdefiniuj funkcję [rev], która odwraca listę. Wskazówka: definicja
    podobna do tej dla [list] nie zadziała. Napiszę wcześniej funkcję
    pomocniczą [snoc], która wstawia element na koniec wektora. *)

(* begin hide *)
Fixpoint snoc {A : Type} {n : nat} (x : A) (l : vec A n) : vec A (S n) :=
match l with
    | vnil => vcons x vnil
    | vcons h t => vcons h (snoc x t)
end.

Fixpoint rev {A : Type} {n : nat} (l : vec A n) : vec A n :=
match l with
    | vnil => vnil
    | vcons h t => snoc h (rev t)
end.
(* end hide *)

Notation "[ ]" := vnil.
Notation "h :: t" := (vcons h t).
Notation "l1 ++ l2" := (app l1 l2).

Lemma rev_nil :
  forall (A : Type), rev [] = @vnil A.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Lemma rev_length :
  forall (A : Type) (n : nat) (l : vec A n),
    len (rev l) = len l.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Lemma snoc_app :
  forall (A : Type) (x : A) (n m : nat) (l1 : vec A n) (l2 : vec A m),
    eq_dep (snoc x (l1 +++ l2)) (l1 +++ snoc x l2).
(* begin hide *)
Proof.
  induction l1; cbn.
    trivial.
    intros. rewrite IHl1. trivial.
Qed.
(* end hide *)

Lemma rev_app :
  forall (A : Type) (n m : nat) (l1 : vec A n) (l2 : vec A m),
    eq_dep (rev (l1 +++ l2)) (rev l2 +++ rev l1).
(* begin hide *)
Proof.
  induction l1 as [| n' h1 t1]; cbn; intro.
    rewrite app_vnil_r'. trivial.
    rewrite IHt1. rewrite snoc_app. trivial. 
Qed.
(* end hide *)

Lemma snoc_rev :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    rev (snoc x l) = vcons x (rev l).
(* begin hide *)
Proof.
  induction l; cbn; try rewrite IHl; trivial.
Qed.
(* end hide *)

Lemma rev_inv :
  forall (A : Type) (n : nat) (l : vec A n), rev (rev l) = l.
(* begin hide *)
Proof.
  induction l; cbn.
    trivial.
    rewrite snoc_rev, IHl. trivial.
Qed.
(* end hide *)

(** Zdefiniuj induktywny predykat [elem]. [elem x l] jest spełniony, gdy
    [x] jest elementem wektora [l]. *)

(* begin hide *)
Inductive elem {A : Type} : A -> forall n : nat, vec A n -> Prop :=
    | elem_head : forall (n : nat) (x : A) (l : vec A n),
        elem x (vcons x l)
    | elem_cons : forall (n : nat) (x h : A) (t : vec A n),
        elem x t -> elem x (vcons h t).

Hint Constructors elem.
(* end hide *)

Lemma elem_nil :
  forall (A : Type) (x : A), ~ elem x vnil.
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma elem_inv_head :
  forall (A : Type) (n : nat) (x h : A) (t : vec A n),
    ~ elem x (vcons h t) -> x <> h.
(* begin hide *)
Proof.
  intros; intro. apply H. subst. constructor.
Qed.
(* end hide *)

Lemma elem_inv_tail :
  forall (A : Type) (n : nat) (x h : A) (t : vec A n),
    ~ elem x (h :: t) -> ~ elem x t.
(* begin hide *)
Proof.
  intros; intro. apply H. constructor. assumption.
Qed.
(* end hide *)

Lemma elem_app_l :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    elem x l1 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma elem_app_r :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| n h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma elem_app_or :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    elem x (l1 ++ l2) -> elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  induction l1 as [| n h1 t1]; cbn; intros.
    right. assumption.
    inversion H; subst.
      left. constructor.
      apply inj_pair2 in H4. subst. destruct (IHt1 _ H3).
        left. constructor. assumption.
        right. assumption.
Qed.
(* end hide *)

Lemma elem_or_app :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    elem x l1 \/ elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  destruct 1; [apply elem_app_l | apply elem_app_r]; assumption.
Qed.
(* end hide *)

Lemma elem_snoc :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x (snoc x l).
(* begin hide *)
Proof.
  induction l; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma elem_snoc' :
  forall (A : Type) (n : nat) (x y : A) (l : vec A n),
    elem x l -> elem x (snoc y l).
(* begin hide *)
Proof.
  induction l; cbn; intros; inversion H; subst; clear H; constructor.
  apply inj_pair2 in H4; subst. auto.
Qed.
(* end hide *)

Lemma elem_snoc'' :
  forall (A : Type) (n : nat) (x y : A) (l : vec A n),
    elem x (snoc y l) <-> x = y \/ elem x l.
(* begin hide *)
Proof.
  split.
    induction l; cbn; intros.
      inversion H; subst; clear H; auto.
        apply inj_pair2 in H4. subst. auto.
      inversion H; subst; clear H.
        right. constructor.
        apply inj_pair2 in H4. subst. destruct (IHl H3); subst; auto.
    destruct 1; subst.
      apply elem_snoc.
      induction l; cbn; intros.
        inversion H.
        inversion H; subst; clear H; constructor.
          apply inj_pair2 in H4; subst. auto.
Qed.
(* end hide *)

Lemma elem_rev :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x l -> elem x (rev l).
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn; intros.
    assumption.
    rewrite elem_snoc''. inversion H; subst; clear H; auto.
      apply inj_pair2 in H4; subst. auto.
Qed.
(* end hide *)

Lemma elem_rev_conv :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x (rev l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn; intros.
    trivial.
    rewrite elem_snoc'' in H. destruct H; subst; constructor; auto.
Qed.
(* end hide *)

Lemma elem_split :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x l -> exists (m1 m2 : nat) (l1 : vec A m1) (l2 : vec A m2),
      eq_dep l (l1 ++ x :: l2).
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn; intro H; inversion H; subst; clear H.
    apply inj_pair2 in H4; subst. do 2 eexists. exists vnil, t. trivial.
    apply inj_pair2 in H4; subst. destruct (IHt H3) as [m1 [m2 [l1 [l2 H]]]].
      exists (S m1), m2, (h :: l1), l2. rewrite H. trivial.
Qed.
(* end hide *)

(** Zdefiniuj funkcję [map], która aplikuje funkcję [f] do każdego
    elementu listy. *)

(* begin hide *)
Fixpoint map {A B : Type} {n : nat} (f : A -> B) (la : vec A n) : vec B n :=
match la with
    | [] => []
    | h :: t => f h :: map f t
end.
(* end hide *)

Lemma map_id : forall (A : Type) (n : nat) (l : vec A n),
  map id l = l.
(* begin hide *)
Proof.
  unfold id. induction l as [| n h t]; cbn; try rewrite IHt; trivial.
Qed.
(* end hide *)

Lemma map_comp :
  forall (A B C : Type) (n : nat) (f : A -> B) (g : B -> C)
    (l : vec A n), map g (map f l) = map (fun x : A => g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma map_length :
  forall (A B : Type) (n : nat) (f : A -> B) (l : vec A n),
    len (map f l) = len l.
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn.
    trivial.
    rewrite ?len_vcons. trivial.
Qed.
(* end hide *)

Lemma map_app :
  forall (A B : Type) (n m : nat) (f : A -> B) (l1 : vec A n) (l2 : vec A m),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
(* begin hide *)
Proof.
  induction l1 as [| n h1 t1]; cbn; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Lemma elem_map :
  forall (A B : Type) (n : nat) (f : A -> B) (l : vec A n) (x : A),
    elem x l -> elem (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn; inversion 1; subst.
    constructor.
    constructor. apply IHt. apply inj_pair2 in H4. subst. assumption.
Qed.
(* end hide *)

Lemma elem_map_conv :
  forall (A B : Type) (n : nat) (f : A -> B) (l : vec A n) (y : B),
    elem y (map f l) <-> exists x : A, f x = y /\ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| n h t]; cbn; intros; inversion H; subst; clear H.
      exists h. split; constructor.
      apply inj_pair2 in H4. subst. destruct (IHt H3) as [x IH].
        exists x. intuition constructor; eauto.
    induction l as [| n h t]; cbn; destruct 1 as [x [Hx1 Hx2]];
    inversion Hx2; subst; constructor.
      apply IHt. exists x. split; trivial. apply inj_pair2 in H3. subst. auto.
Qed.
(* end hide *)

Lemma map_snoc :
  forall (A B : Type) (n : nat) (f : A -> B) (x : A) (l : vec A n),
    map f (snoc x l) = snoc (f x) (map f l).
(* begin hide *)
Proof.
  induction l; cbn; try rewrite IHl; trivial.
Qed.
(* end hide *)

Lemma map_rev :
  forall (A B : Type) (n : nat) (f : A -> B) (l : vec A n),
    map f (rev l) = rev (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite map_snoc, IHl. trivial.
Qed.
(* end hide *)

Lemma map_ext_elem :
  forall (A B : Type) (n : nat) (f g : A -> B) (l : vec A n),
    (forall x : A, elem x l -> f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn; intros.
    trivial.
    rewrite H, IHt; auto.
Qed.
(* end hide *)

Lemma map_ext :
  forall (A B : Type) (n : nat) (f g : A -> B) (l : vec A n),
    (forall x : A, f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn; intro; try rewrite H, IHt; auto.
Qed.
(* end hide *)

(** Napisz funkcję [join], która spłaszcza listę list. *)

(* begin hide *)
Fixpoint join {A : Type} (n m : nat) (lla : vec (vec A n) m)
  : vec A (m * n) :=
match lla with
    | [] => []
    | h :: t => h ++ join t
end.
(* end hide *)

Lemma join_app :
  forall (A : Type) (n n' m m' : nat) (l1 : vec (vec A n) m)
  (l2 : vec (vec A n) m'),
    eq_dep (join (l1 ++ l2)) (join l1 ++ join l2).
(* begin hide *)
Proof.
  induction l1; cbn; intros.
    trivial.
    rewrite IHl1, app_assoc. trivial.
Qed.
(* end hide *)

Lemma join_map :
  forall (A B : Type) (n m : nat) (f : A -> B) (l : vec (vec A n) m),
    map f (join l) = join (map (map f) l).
(* begin hide *)
Proof.
  induction l; cbn; intros.
    trivial.
    rewrite map_app, IHl. trivial.
Qed.
(* end hide *)

(** *** [repeat] (TODO: nastąpiła duplikacja) *)

(** Zdefiniuj funkcję [repeat], która zwraca listę [n] powtórzeń wartości
    [x]. *)

(* begin hide *)
Fixpoint repeat {A : Type} (n : nat) (x : A) : vec A n :=
match n with
    | 0 => []
    | S n' => x :: repeat n' x
end.
(* end hide *)

Lemma repeat_len :
  forall (A : Type) (n : nat) (x : A),
    len (repeat n x) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intro; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Lemma repeat_elem :
  forall (A : Type) (n : nat) (x y : A),
    elem x (repeat n y) -> x = y.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; inversion H; subst.
    trivial.
    apply IHn'. apply inj_pair2 in H4; subst. assumption.
Qed.
(* end hide *)

(** *** [nth] *)

(** Zdefiniuj funkcję [nth], która zwraca n-ty element listy lub [None],
    gdy nie ma n-tego elementu. *)

(* begin hide *)
Fixpoint nth {A : Type} {n : nat} (m : nat) (l : vec A n) : option A :=
match m, l with
    | _, [] => None
    | 0, h :: t => Some h
    | S n', h :: t => nth n' t
end.
(* end hide *)

Lemma nth_len :
  forall (A : Type) (m n : nat) (l : vec A n),
    m < n -> exists x : A, nth m l = Some x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; intros.
    inversion H.
    exists a. cbn. trivial.
    inversion H.
    apply lt_S_n in H. destruct (IHm' _ l H) as [x Hx]. exists x. assumption.
Qed.
(* end hide *)

Require Import Arith.

Lemma nth_elem :
  forall (A : Type) (m n : nat) (l : vec A n),
    m < n -> exists x : A, nth m l = Some x /\ elem x l.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; cbn; intros.
    inversion H.
    eauto.
    inversion H.
    apply lt_S_n in H. destruct (IHm' _ l H) as [x [H1 H2]]. eauto.
Qed.
(* end hide *)

Lemma nth_elem_conv :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x l -> exists m : nat, nth m l = Some x.
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn; inversion 1; subst.
    exists 0. cbn. trivial.
    apply inj_pair2 in H4; subst.
      destruct (IHt H3) as [m Hm]. exists (S m). eauto.
Qed.
(* end hide *)

Lemma nth_overflow :
  forall (A : Type) (m n : nat) (l : vec A n),
    n <= m -> ~ exists x : A, nth m l = Some x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; cbn; intros.
    destruct 1. inversion H0.
    inversion H.
    destruct 1. inversion H0.
    apply IHm'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_app1 :
  forall (A : Type) (m n1 n2 : nat) (l1 : vec A n1) (l2 : vec A n2),
    m < n1 -> nth m (l1 ++ l2) = nth m l1.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l1; cbn; intros.
    inversion H.
    trivial.
    inversion H.
    apply IHm'. apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_app2 :
  forall (A : Type) (m n1 n2 : nat) (l1 : vec A n1) (l2 : vec A n2),
    n1 <= m -> nth m (l1 ++ l2) = nth (m - n1) l2.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l1, l2; cbn; auto;
  try (inversion 1; fail); intros; apply IHm', le_S_n; assumption.
Qed.
(* end hide *)

Lemma nth_split :
  forall (A : Type) (m n : nat) (l : vec A n) (x : A),
    nth m l = Some x -> exists (n1 n2 : nat) (l1 : vec A n1) (l2 : vec A n2),
      eq_dep l (l1 ++ x :: l2) /\ n1 = m.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; cbn; inversion 1; subst.
    do 2 eexists. exists [], l. cbn. eauto.
    destruct (IHm' _ _ _ H) as [n1 [n2 [l1 [l2 [H2 H3]]]]].
      exists (S n1), n2, (a :: l1), l2. subst. rewrite H2. split; eauto.
Qed.
(* end hide *)

Lemma nth_None :
  forall (A : Type) (m n : nat) (l : vec A n),
    nth m l = None -> n <= m.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; cbn; intros.
    trivial.
    inversion H.
    apply le_0_n.
    apply le_n_S. eapply IHm'. exact H.
Qed.
(* end hide *)

Lemma nth_Some :
  forall (A : Type) (m n : nat) (l : vec A n) (x : A),
    nth m l = Some x -> m < n.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; cbn; intros.
    inversion H.
    red. apply le_n_S. apply le_0_n.
    inversion H.
    apply lt_n_S. eapply IHm'. eassumption.
Qed.
(* end hide *)

Lemma map_nth :
    forall (A B : Type) (m n : nat) (f : A -> B) (l : vec A n) (x : A),
      nth m l = Some x -> nth m (map f l) = Some (f x).
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; cbn; inversion 1; trivial.
  rewrite (IHm' _ _ l x); auto.
Qed.
(* end hide *)

(** *** [head] i [last] *)

(** Zdefiniuj funkcje [head] i [last], które zwracają odpowiednio pierwszy
    i ostatni element listy (lub [None], jeżeli jest pusta). *)

(* begin hide *)
Definition head {A : Type} {n : nat} (l : vec A (S n)) : A :=
match l with
    | h :: _ => h
end.

Fixpoint last {A : Type} {n : nat} (l : vec A (S n)) {struct l} : A.
Proof.
  inversion l; subst. destruct n as [| n'].
    exact X.
    apply (last _ _ X0).
Defined.

(*Fixpoint head {A : Type} {n : nat} (l : vec A n) : option A :=
match l with
    | [] => None
    | h :: _ => Some h
end.*)

(*Fixpoint last {A : Type} {n : nat} (l : vec A n) : option A :=
match l with
    | [] => None
    | vcons _ x vnil => Some x
    | h :: t => last t
end.*)
(* end hide *)

Lemma head_cons :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    head (h :: t) = h.
(* begin hide *)
Proof. cbn. trivial. Qed.
(* end hide *)

Lemma last_snoc :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    last (snoc h t) = h.
(* begin hide *)
Proof.
  induction t; cbn; auto.
Qed.
(* end hide *)

Lemma head_nth:
  forall (A : Type) (n : nat) (l : vec A (S n)),
    Some (head l) = nth 0 l.
(* begin hide *)
Proof.
  intros. dependent destruction l; cbn. trivial.
Qed.
(* end hide *)

Lemma last_nth : forall (A : Type) (n : nat) (l : vec A (S n)),
  Some (last l) = nth n l.
(* begin hide *)
Proof.
  dependent induction l; cbn.
  destruct n as [| n']; cbn.
    trivial.
    apply IHl; auto.
Qed.
(* end hide *)

(** *** [tail] i [init] *)

(** Zdefiniuj funkcje [tail] i [init], które zwracają odpowiednio ogon
    listy oraz wszystko poza jej ostatnim elementem. Użyj typów zależnych. *)

(* begin hide *)
(*Fixpoint tail {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | _ :: t => Some t
end.

Fixpoint init {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | h :: t => match init t with
        | None => Some [h]
        | Some t' => Some (h :: t')
    end
end.*)

Definition tail {A : Type} {n : nat} (l : vec A (S n)) : vec A n :=
match l with
    | _ :: t => t
end.

Fixpoint init {A : Type} {n : nat} (l : vec A (S n)) {struct l} : vec A n.
Proof.
  dependent destruction l. destruct n as [| n'].
    exact vnil.
    exact (a :: init _ _ l).
Defined.

(* end hide *)

(** *** [take] i [drop] *)

(** Zdefiniuj funkcje [take] i [drop], które odpowiednio biorą lub
    odrzucają n pierwszych elementów listy. *)

(* begin hide *)

Fixpoint take {A : Type} {n : nat} (m : nat) (l : vec A n) : vec A (min m n).
Proof.
  destruct m as [| m']; cbn.
    exact vnil.
    destruct l as [| n h t]; cbn.
      exact vnil.
      exact (h :: take _ _ m' t).
Defined.

Lemma minus_0_r_transparent :
  forall n : nat,
    minus n 0 = n.
Proof.
  destruct n; reflexivity.
Qed.

Fixpoint drop {A : Type} {n : nat} (m : nat) (l : vec A n) : vec A (n - m).
Proof.
  destruct m as [| m']; cbn.
    destruct n; assumption.
    destruct l as [| n h t]; cbn.
      exact vnil.
      apply drop; auto.
Defined.

Ltac takedrop := intros; repeat
match goal with
    | |- context [take _ ?l] => destruct l; compute
    | |- context [drop _ ?l] => destruct l; compute
    | |- context [minus_n_O ?n] =>
        remember (minus_n_O n) as x; dependent destruction x
    | |- eq_dep ?x ?x => trivial
end; auto.

Ltac takedrop' := intros; repeat
match goal with
    | |- context [take ?n ?l] => induction n; cbn
    | |- context [drop ?n ?l] => induction n; compute
    | |- context [minus_n_O ?n] =>
        remember (minus_n_O n) as x; dependent destruction x
end; auto.

Ltac td := intros; compute; repeat
match goal with
    | |- context [minus_n_O ?n] =>
        remember (minus_n_O n) as x; dependent destruction x
    | H : context [minus_n_O ?n] |- _ =>
        remember (minus_n_O n) as x; dependent destruction x
end; auto.
(* end hide *)

Lemma take_nil :
  forall (A : Type) (n : nat),
    eq_dep (take n []) (@vnil A).
(* begin hide *)
Proof.
  takedrop'.
Restart. 
  destruct n; cbn; trivial.
Qed.
(* end hide *)

Lemma drop_nil :
  forall (A : Type) (n : nat),
    eq_dep (drop n []) (@vnil A).
(* begin hide *)
Proof.
  destruct n.
    compute. remember (minus_n_O 0) as x. dependent destruction x.
      trivial.
    cbn. trivial.
Restart.
  takedrop'.
Qed.
(* end hide *)

Lemma take_cons :
  forall (A : Type) (n m : nat) (h : A) (t : vec A n),
    take (S m) (h :: t) = h :: take m t.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma drop_cons :
  forall (A : Type) (n m : nat) (h : A) (t : vec A n),
    drop (S m) (h :: t) = drop m t.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma take_0 :
  forall (A : Type) (n : nat) (l : vec A n),
    take 0 l = [].
(* begin hide *)
Proof.
  takedrop.
Restart.
  destruct l; cbn; trivial.
Qed.
(* end hide *)

Lemma drop_0 :
  forall (A : Type) (n : nat) (l : vec A n),
    eq_dep (drop 0 l) l.
(* begin hide *)
Proof. takedrop. Qed.
(* end hide *)

Lemma take_length :
  forall (A : Type) (n : nat) (l : vec A n),
    eq_dep (take n l) l.
(* begin hide *)
Proof.
  induction l as [| n h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma drop_all :
  forall (A : Type) (n : nat) (l : vec A n),
    eq_dep (drop n l) [].
(* begin hide *)
Proof.
  induction l as [| n h t]; td.
Qed.
(* end hide *)

Lemma take_length' :
  forall (A : Type) (n m : nat) (l : vec A n),
    n <= m -> eq_dep (take m l) l.
(* begin hide *)
Proof.
  intros A n m. generalize dependent n.
  induction m as [| m']; intros.
    assert (n = 0) by lia. subst.
      dependent destruction l. apply take_nil.
    dependent destruction l.
      apply take_nil.
      cbn. rewrite IHm'; auto; lia.
Qed.
(* end hide *)

Lemma drop_length' :
  forall (A : Type) (m n : nat) (l : vec A n),
    n <= m -> eq_dep (drop m l) [].
(* begin hide *)
Proof.
  induction m as [| m']; intros.
    rewrite drop_0. dependent destruction l; try lia. trivial.
    destruct l as [| n h t]; cbn.
      trivial.
      rewrite IHm'; auto; lia.
Qed.
(* end hide *)

Lemma length_take :
  forall (A : Type) (m n : nat) (l : vec A n),
    len (take m l) = min m n.
(* begin hide *)
Proof.
  destruct m as [| m']; reflexivity.
Qed.
(* end hide *)

Lemma drop_take :
  forall (A : Type) (m n : nat) (l : vec A n),
    m <= n -> len (drop m l) = n - m.
(* begin hide *)
Proof.
  induction m as [| m']; intros.
    rewrite drop_0. compute. trivial.
    destruct l as [| n h t]; cbn.
      compute. trivial.
      reflexivity.
Qed.
(* end hide *)

Lemma take_map :
  forall (A B : Type) (f : A -> B) (m n : nat) (l : vec A n),
    map f (take m l) = take m (map f l).
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    trivial.
    destruct l as [| n h t]; cbn; try rewrite IHm'; trivial.
Restart.
  induction m; destruct l; cbn; intros; rewrite ?IHm; auto.
Qed.
(* end hide *)

Lemma drop_map :
  forall (A B : Type) (f : A -> B) (m n : nat) (l : vec A n),
    eq_dep (map f (drop m l)) (drop m (map f l)).
(* begin hide *)
Proof.
  induction m as [| m']; intros.
    rewrite ?drop_0. trivial.
    destruct l; cbn.
      trivial.
      apply IHm'.
Qed.
(* end hide *)

Lemma take_elem :
  forall (A : Type) (m n : nat) (l : vec A n) (x : A),
    elem x (take m l) -> elem x l.
(* begin hide *)
Proof.
  induction m as [| m'].
    cbn. inversion 1.
    destruct l as [| n h t]; cbn; inversion 1; subst; constructor.
      apply IHm'. apply inj_pair2 in H4. subst. assumption.
Qed.
(* end hide *)

Lemma drop_elem :
  forall (A : Type) (m n : nat) (l : vec A n) (x : A),
    elem x (drop m l) -> elem x l.
(* begin hide *)
Proof.
  induction m as [| m']. td.
    rewrite drop_0 in H. assumption.
    destruct l as [| n h t]; cbn.
      inversion 1.
      intros. constructor. apply IHm'. assumption.
Qed.
(* end hide *)

Lemma take_take :
  forall (A : Type) (m m' n : nat) (l : vec A n),
    eq_dep (take m (take m' l)) (take m' (take m l)).
(* begin hide *)
Proof.
  induction m; destruct m'; intros; trivial.
  destruct l as [| n h t]; cbn.
    reflexivity.
    rewrite IHm. reflexivity.
Qed.
(* end hide *)

Lemma drop_S :
  forall (A : Type) (m m' n : nat) (l : vec A n),
    eq_dep (drop (S m) (drop m' l)) (drop m (drop (S m') l)).
(* begin hide *)
Proof.
  intros. revert m m'.
  induction l as [| n h t]; intros.
    rewrite !drop_nil. reflexivity.
    destruct m' as [| m''].
      rewrite drop_0, !drop_cons. destruct n; cbn; reflexivity.
      {
        change (S n - S m'' - S m) with (n - m'' - S m);
        change (S n - S m'') with (n - m'').
        rewrite !drop_cons. rewrite IHt. reflexivity.
      }
Qed.
(* end hide *)

Lemma drop_drop :
  forall (A : Type) (m m' n : nat) (l : vec A n),
    eq_dep (drop m (drop m' l)) (drop m' (drop m l)).
(* begin hide *)
Proof.
  induction m; intros.
    rewrite ?drop_0. reflexivity.
    rewrite drop_S, IHm, drop_S. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma take_drop_rev_aux :
  forall (A : Type) (m n : nat) (l : vec A n),
    eq_dep (take m l) (rev (drop (n - m) (rev l))).
Proof.
  induction m as [| m']; intros.
    rewrite take_0, <- minus_n_O, drop_all. cbn. reflexivity.
    destruct l as [| n h t].
      rewrite !rev_nil, take_nil. reflexivity.
      change (S n - S m') with (n - m'). cbn. rewrite IHm'.
Admitted.
(* end hide *)

(* begin hide *)
Lemma take_drop_rev :
  forall (A : Type) (m n : nat) (l : vec A n),
    eq_dep (take m (rev l)) (rev (drop (n - m) l)).
Proof.
  intros.
  rewrite take_drop_rev_aux, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma take_drop :
  forall (A : Type) (a b n : nat) (l : vec A n),
    eq_dep (take a (drop b l)) (drop b (take (b + a) l)).
(* begin hide *)
Proof.
  intros A a b n. revert a n.
  induction b as [| b']; intros.
    rewrite !drop_0. cbn. reflexivity.
    destruct l as [| n h t]; cbn.
      rewrite take_nil. reflexivity.
      apply IHb'.
Qed.
(* end hide *)