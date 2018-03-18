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

Arguments vnil [A].
Arguments vcons [A n] _ _.

(** *** [length] *)

(** Zdefiniuj funkcję [len], która oblicza długość listy. Powinna ona
    wykonywać się w czasie liniowym. *)

(* begin hide *)
Function len {A : Type} {n : nat} (_ : vec A n) : nat := n.
(* end hide *)

Theorem len_vnil :
  forall A : Type, len (@vnil A) = 0.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Theorem len_vcons' :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    len (vcons h t) = S n.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Theorem len_vcons :
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

Theorem app_vnil_l :
  forall (A : Type) (n : nat) (l : vec A n), vnil +++ l = l.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Theorem JMeq_vcons :
  forall (A : Type) (n m : nat) (h h' : A) (t : vec A n) (t' : vec A m),
    n = m -> JMeq h h' -> JMeq t t' -> JMeq (vcons h t) (vcons h' t').
(* end hide *)
Proof.
  intros. subst. rewrite H1. reflexivity.
Qed.
(* end hide *)

Theorem app_vnil_r :
  forall (A : Type) (n : nat) (l : vec A n), JMeq (l +++ vnil) l.
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl.
    trivial.
    apply JMeq_vcons; auto.
Qed.
(* end hide *)

Theorem app_vnil_r' :
  forall (A : Type) (n : nat) (l : vec A n), eq_dep (l +++ vnil) l.
(* begin hide *)
Proof.
  induction l; simpl; try rewrite IHl; trivial.
Qed.
(* end hide *)

Theorem app_assoc :
  forall (A : Type) (x y z : nat) (l1 : vec A x) (l2 : vec A y) (l3 : vec A z),
    eq_dep (l1 +++ (l2 +++ l3)) ((l1 +++ l2) +++ l3).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    rewrite IHl1. trivial.
Qed.
(* end hide *)

Theorem app_assoc' :
  forall (A : Type) (x y z : nat) (l1 : vec A x) (l2 : vec A y) (l3 : vec A z),
    JMeq (l1 +++ (l2 +++ l3)) ((l1 +++ l2) +++ l3).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    apply JMeq_vcons; auto. rewrite plus_assoc. trivial.
Qed.
(* end hide *)

Theorem app_len :
  forall (A : Type) (n m : nat) (l1 : vec A n) (l2 : vec A m),
    len (l1 +++ l2) = len l1 + len l2.
(* begin hide *)
Proof.
  intros. unfold len. trivial.
Qed.
(* end hide *)

Theorem app_cons :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    (vcons x l1) +++ l2 = vcons x (l1 +++ l2).
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Theorem app_cons2 :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    JMeq (l1 +++ vcons x l2) ((l1 +++ (vcons x vnil)) +++ l2).
(* begin hide *)
Proof.
  induction l1 as [| n h1 t1]; simpl; intros.
    trivial.
    apply JMeq_vcons; auto. rewrite <- plus_assoc. f_equal.
Qed.
(* end hide *)

Theorem app_cons2' :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    eq_dep (l1 +++ vcons x l2) ((l1 +++ (vcons x vnil)) +++ l2).
(* begin hide *)
Proof.
  induction l1 as [| n h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Require Import Omega.

Theorem no_infinite_cons :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    eq_dep t (vcons h t) -> False.
(* begin hide *)
Proof.
  inversion 1. omega.
Qed.
(* end hide *)

Theorem no_infinite_app :
  forall (A : Type) (n m : nat) (l : vec A n) (l' : vec A m),
    ~ eq_dep l' vnil -> eq_dep l (l' +++ l) -> False.
(* begin hide *)
Proof.
  induction l; simpl; intros.
    rewrite app_vnil_r' in H0. apply H. rewrite H0. trivial.
    destruct l'.
      contradiction H. trivial.
      inversion H0. omega.
Qed.
(* end hide *)

Theorem app_inv1 :
  forall (A : Type) (n m : nat) (l : vec A n) (l1 l2 : vec A m),
    l +++ l1 = l +++ l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction l; simpl; intros.
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

Theorem app_inv2 :
  forall (A : Type) (n m : nat) (l : vec A n) (l1 l2 : vec A m),
    eq_dep (l1 +++ l) (l2 +++ l) -> eq_dep l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
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

Theorem app_eq_nil :
  forall (A : Type) (n m : nat) (l1 : vec A n) (l2 : vec A m),
    eq_dep (l1 +++ l2) vnil -> eq_dep l1 vnil /\ eq_dep l2 vnil.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
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
    | vcons _ h t => vcons h (snoc x t)
end.

Fixpoint rev {A : Type} {n : nat} (l : vec A n) : vec A n :=
match l with
    | vnil => vnil
    | vcons _ h t => snoc h (rev t)
end.
(* end hide *)

Notation "[ ]" := vnil.
Notation "h :: t" := (vcons h t).
Notation "l1 ++ l2" := (app l1 l2).

Theorem rev_nil :
  forall (A : Type), rev [] = @vnil A.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Theorem rev_length :
  forall (A : Type) (n : nat) (l : vec A n),
    len (rev l) = len l.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Theorem snoc_app :
  forall (A : Type) (x : A) (n m : nat) (l1 : vec A n) (l2 : vec A m),
    eq_dep (snoc x (l1 +++ l2)) (l1 +++ snoc x l2).
(* begin hide *)
Proof.
  induction l1; simpl.
    trivial.
    intros. rewrite IHl1. trivial.
Qed.
(* end hide *)

Theorem rev_app :
  forall (A : Type) (n m : nat) (l1 : vec A n) (l2 : vec A m),
    eq_dep (rev (l1 +++ l2)) (rev l2 +++ rev l1).
(* begin hide *)
Proof.
  induction l1 as [| n' h1 t1]; simpl; intro.
    rewrite app_vnil_r'. trivial.
    rewrite IHt1. rewrite snoc_app. trivial. 
Qed.
(* end hide *)

Lemma snoc_rev :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    rev (snoc x l) = vcons x (rev l).
(* begin hide *)
Proof.
  induction l; simpl; try rewrite IHl; trivial.
Qed.
(* end hide *)

Theorem rev_inv :
  forall (A : Type) (n : nat) (l : vec A n), rev (rev l) = l.
(* begin hide *)
Proof.
  induction l; simpl.
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

Theorem elem_nil :
  forall (A : Type) (x : A), ~ elem x vnil.
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Theorem elem_inv_head :
  forall (A : Type) (n : nat) (x h : A) (t : vec A n),
    ~ elem x (vcons h t) -> x <> h.
(* begin hide *)
Proof.
  intros; intro. apply H. subst. constructor.
Qed.
(* end hide *)

Theorem elem_inv_tail :
  forall (A : Type) (n : nat) (x h : A) (t : vec A n),
    ~ elem x (h :: t) -> ~ elem x t.
(* begin hide *)
Proof.
  intros; intro. apply H. constructor. assumption.
Qed.
(* end hide *)

Theorem elem_app_l :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    elem x l1 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; simpl; constructor; assumption.
Qed.
(* end hide *)

Lemma elem_app_r :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| n h t]; simpl; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Theorem elem_app_or :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    elem x (l1 ++ l2) -> elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  induction l1 as [| n h1 t1]; simpl; intros.
    right. assumption.
    inversion H; subst.
      left. constructor.
      apply inj_pair2 in H4. subst. destruct (IHt1 _ H3).
        left. constructor. assumption.
        right. assumption.
Qed.
(* end hide *)

Theorem elem_or_app :
  forall (A : Type) (n m : nat) (x : A) (l1 : vec A n) (l2 : vec A m),
    elem x l1 \/ elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  destruct 1; [apply elem_app_l | apply elem_app_r]; assumption.
Qed.
(* end hide *)

Theorem elem_snoc :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x (snoc x l).
(* begin hide *)
Proof.
  induction l; simpl; constructor; assumption.
Qed.
(* end hide *)

Theorem elem_snoc' :
  forall (A : Type) (n : nat) (x y : A) (l : vec A n),
    elem x l -> elem x (snoc y l).
(* begin hide *)
Proof.
  induction l; simpl; intros; inversion H; subst; clear H; constructor.
  apply inj_pair2 in H4; subst. auto.
Qed.
(* end hide *)

Theorem elem_snoc'' :
  forall (A : Type) (n : nat) (x y : A) (l : vec A n),
    elem x (snoc y l) <-> x = y \/ elem x l.
(* begin hide *)
Proof.
  split.
    induction l; simpl; intros.
      inversion H; subst; clear H; auto.
        apply inj_pair2 in H4. subst. auto.
      inversion H; subst; clear H.
        right. constructor.
        apply inj_pair2 in H4. subst. destruct (IHl H3); subst; auto.
    destruct 1; subst.
      apply elem_snoc.
      induction l; simpl; intros.
        inversion H.
        inversion H; subst; clear H; constructor.
          apply inj_pair2 in H4; subst. auto.
Qed.
(* end hide *)

Theorem elem_rev :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x l -> elem x (rev l).
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl; intros.
    assumption.
    rewrite elem_snoc''. inversion H; subst; clear H; auto.
      apply inj_pair2 in H4; subst. auto.
Qed.
(* end hide *)

Theorem elem_rev_conv :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x (rev l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl; intros.
    trivial.
    rewrite elem_snoc'' in H. destruct H; subst; constructor; auto.
Qed.
(* end hide *)

Theorem elem_split :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x l -> exists (m1 m2 : nat) (l1 : vec A m1) (l2 : vec A m2),
      eq_dep l (l1 ++ x :: l2).
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl; intro H; inversion H; subst; clear H.
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

Theorem map_id : forall (A : Type) (n : nat) (l : vec A n),
  map id l = l.
(* begin hide *)
Proof.
  unfold id. induction l as [| n h t]; simpl; try rewrite IHt; trivial.
Qed.
(* end hide *)

Theorem map_comp :
  forall (A B C : Type) (n : nat) (f : A -> B) (g : B -> C)
    (l : vec A n), map g (map f l) = map (fun x : A => g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem map_length :
  forall (A B : Type) (n : nat) (f : A -> B) (l : vec A n),
    len (map f l) = len l.
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl.
    trivial.
    rewrite ?len_vcons. trivial.
Qed.
(* end hide *)

Theorem map_app :
  forall (A B : Type) (n m : nat) (f : A -> B) (l1 : vec A n) (l2 : vec A m),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
(* begin hide *)
Proof.
  induction l1 as [| n h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Theorem elem_map :
  forall (A B : Type) (n : nat) (f : A -> B) (l : vec A n) (x : A),
    elem x l -> elem (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl; inversion 1; subst.
    constructor.
    constructor. apply IHt. apply inj_pair2 in H4. subst. assumption.
Qed.
(* end hide *)

Theorem elem_map_conv :
  forall (A B : Type) (n : nat) (f : A -> B) (l : vec A n) (y : B),
    elem y (map f l) <-> exists x : A, f x = y /\ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| n h t]; simpl; intros; inversion H; subst; clear H.
      exists h. split; constructor.
      apply inj_pair2 in H4. subst. destruct (IHt H3) as [x IH].
        exists x. intuition constructor; eauto.
    induction l as [| n h t]; simpl; destruct 1 as [x [Hx1 Hx2]];
    inversion Hx2; subst; constructor.
      apply IHt. exists x. split; trivial. apply inj_pair2 in H3. subst. auto.
Qed.
(* end hide *)

Theorem map_snoc :
  forall (A B : Type) (n : nat) (f : A -> B) (x : A) (l : vec A n),
    map f (snoc x l) = snoc (f x) (map f l).
(* begin hide *)
Proof.
  induction l; simpl; try rewrite IHl; trivial.
Qed.
(* end hide *)

Theorem map_rev :
  forall (A B : Type) (n : nat) (f : A -> B) (l : vec A n),
    map f (rev l) = rev (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite map_snoc, IHl. trivial.
Qed.
(* end hide *)

Theorem map_ext_elem :
  forall (A B : Type) (n : nat) (f g : A -> B) (l : vec A n),
    (forall x : A, elem x l -> f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl; intros.
    trivial.
    rewrite H, IHt; auto.
Qed.
(* end hide *)

Theorem map_ext :
  forall (A B : Type) (n : nat) (f g : A -> B) (l : vec A n),
    (forall x : A, f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl; intro; try rewrite H, IHt; auto.
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

Theorem join_app :
  forall (A : Type) (n n' m m' : nat) (l1 : vec (vec A n) m)
  (l2 : vec (vec A n) m'),
    eq_dep (join (l1 ++ l2)) (join l1 ++ join l2).
(* begin hide *)
Proof.
  induction l1; simpl; intros.
    trivial.
    rewrite IHl1, app_assoc. trivial.
Qed.
(* end hide *)

Theorem join_map :
  forall (A B : Type) (n m : nat) (f : A -> B) (l : vec (vec A n) m),
    map f (join l) = join (map (map f) l).
(* begin hide *)
Proof.
  induction l; simpl; intros.
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

Theorem repeat_len :
  forall (A : Type) (n : nat) (x : A),
    len (repeat n x) = n.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intro; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem repeat_elem :
  forall (A : Type) (n : nat) (x y : A),
    elem x (repeat n y) -> x = y.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; inversion H; subst.
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

Theorem nth_len :
  forall (A : Type) (m n : nat) (l : vec A n),
    m < n -> exists x : A, nth m l = Some x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; intros.
    inversion H.
    exists a. simpl. trivial.
    inversion H.
    apply lt_S_n in H. destruct (IHm' _ l H) as [x Hx]. exists x. assumption.
Qed.
(* end hide *)

Theorem nth_elem :
  forall (A : Type) (m n : nat) (l : vec A n),
    m < n -> exists x : A, nth m l = Some x /\ elem x l.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; simpl; intros; intuition; eauto.
  apply lt_S_n in H. destruct (IHm' _ l H) as [x [H1 H2]]. eauto.
Qed.
(* end hide *)

Theorem nth_elem_conv :
  forall (A : Type) (n : nat) (x : A) (l : vec A n),
    elem x l -> exists m : nat, nth m l = Some x.
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl; inversion 1; subst.
    exists 0. simpl. trivial.
    apply inj_pair2 in H4; subst.
      destruct (IHt H3) as [m Hm]. exists (S m). eauto.
Qed.
(* end hide *)

Theorem nth_overflow :
  forall (A : Type) (m n : nat) (l : vec A n),
    n <= m -> ~ exists x : A, nth m l = Some x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; simpl; intros.
    destruct 1. inversion H0.
    inversion H.
    destruct 1. inversion H0.
    apply IHm'. apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem nth_app1 :
  forall (A : Type) (m n1 n2 : nat) (l1 : vec A n1) (l2 : vec A n2),
    m < n1 -> nth m (l1 ++ l2) = nth m l1.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l1; simpl; intros.
    inversion H.
    trivial.
    inversion H.
    apply IHm'. apply lt_S_n. assumption.
Qed.
(* end hide *)

Theorem nth_app2 :
  forall (A : Type) (m n1 n2 : nat) (l1 : vec A n1) (l2 : vec A n2),
    n1 <= m -> nth m (l1 ++ l2) = nth (m - n1) l2.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l1, l2; simpl; auto;
  try (inversion 1; fail); intros; apply IHm', le_S_n; assumption.
Qed.
(* end hide *)

Theorem nth_split :
  forall (A : Type) (m n : nat) (l : vec A n) (x : A),
    nth m l = Some x -> exists (n1 n2 : nat) (l1 : vec A n1) (l2 : vec A n2),
      eq_dep l (l1 ++ x :: l2) /\ n1 = m.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; simpl; inversion 1; subst.
    do 2 eexists. exists [], l. simpl. eauto.
    destruct (IHm' _ _ _ H) as [n1 [n2 [l1 [l2 [H2 H3]]]]].
      exists (S n1), n2, (a :: l1), l2. subst. rewrite H2. split; eauto.
Qed.
(* end hide *)

Theorem nth_None :
  forall (A : Type) (m n : nat) (l : vec A n),
    nth m l = None -> n <= m.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; simpl; intros.
    trivial.
    inversion H.
    apply le_0_n.
    apply le_n_S. eapply IHm'. exact H.
Qed.
(* end hide *)

Theorem nth_Some :
  forall (A : Type) (m n : nat) (l : vec A n) (x : A),
    nth m l = Some x -> m < n.
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; simpl; intros.
    inversion H.
    red. apply le_n_S. apply le_0_n.
    inversion H.
    apply lt_n_S. eapply IHm'. eassumption.
Qed.
(* end hide *)

Theorem map_nth :
    forall (A B : Type) (m n : nat) (f : A -> B) (l : vec A n) (x : A),
      nth m l = Some x -> nth m (map f l) = Some (f x).
(* begin hide *)
Proof.
  induction m as [| m']; destruct l; simpl; inversion 1; trivial.
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

Theorem head_cons :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    head (h :: t) = h.
(* begin hide *)
Proof. simpl. trivial. Qed.
(* end hide *)

Theorem last_snoc :
  forall (A : Type) (n : nat) (h : A) (t : vec A n),
    last (snoc h t) = h.
(* begin hide *)
Proof.
  induction t; simpl; auto.
Qed.
(* end hide *)

Theorem head_nth:
  forall (A : Type) (n : nat) (l : vec A (S n)),
    Some (head l) = nth 0 l.
(* begin hide *)
Proof.
  intros. dependent destruction l; simpl. trivial.
Qed.
(* end hide *)

Theorem last_nth : forall (A : Type) (n : nat) (l : vec A (S n)),
  Some (last l) = nth n l.
(* begin hide *)
Proof.
  dependent induction l; simpl.
  destruct n as [| n']; simpl.
    trivial.
    apply IHl; auto.
Restart.
  dependent induction l; destruct n; simpl; auto.
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

Fixpoint tail {A : Type} {n : nat} (l : vec A (S n)) : vec A n :=
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
  destruct m as [| m']; simpl.
    exact vnil.
    destruct l as [| n h t]; simpl.
      exact vnil.
      exact (h :: take _ _ m' t).
Defined.

Fixpoint drop {A : Type} {n : nat} (m : nat) (l : vec A n) : vec A (n - m).
Proof.
  destruct m as [| m']; simpl.
    rewrite <- minus_n_O. exact l.
    destruct l as [| n h t]; simpl.
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
    | |- context [take ?n ?l] => induction n; simpl
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

Theorem take_nil :
  forall (A : Type) (n : nat),
    eq_dep (take n []) (@vnil A).
(* begin hide *)
Proof.
  takedrop'.
Restart. 
  destruct n; simpl; trivial.
Qed.
(* end hide *)

Theorem drop_nil :
  forall (A : Type) (n : nat),
    eq_dep (drop n []) (@vnil A).
(* begin hide *)
Proof.
  destruct n.
    compute. remember (minus_n_O 0) as x. dependent destruction x.
      trivial.
    simpl. trivial.
Restart.
  takedrop'.
Qed.
(* end hide *)

Theorem take_cons :
  forall (A : Type) (n m : nat) (h : A) (t : vec A n),
    take (S m) (h :: t) = h :: take m t.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Theorem drop_cons :
  forall (A : Type) (n m : nat) (h : A) (t : vec A n),
    drop (S m) (h :: t) = drop m t.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Theorem take_0 :
  forall (A : Type) (n : nat) (l : vec A n),
    take 0 l = [].
(* begin hide *)
Proof.
  takedrop.
Restart.
  destruct l; simpl; trivial.
Qed.
(* end hide *)

Theorem drop_0 :
  forall (A : Type) (n : nat) (l : vec A n),
    eq_dep (drop 0 l) l.
(* begin hide *)
Proof. takedrop. Qed.
(* end hide *)

Theorem take_length :
  forall (A : Type) (n : nat) (l : vec A n),
    eq_dep (take n l) l.
(* begin hide *)
Proof.
  induction l as [| n h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem drop_all :
  forall (A : Type) (n : nat) (l : vec A n),
    eq_dep (drop n l) [].
(* begin hide *)
Proof.
  induction l as [| n h t]; td.
Qed.
(* end hide *)

Theorem take_length' :
  forall (A : Type) (n m : nat) (l : vec A n),
    n <= m -> eq_dep (take m l) l.
(* begin hide *)
Proof.
  intros A n m. generalize dependent n.
  induction m as [| m']; intros.
    assert (n = 0) by omega. subst.
      dependent destruction l. apply take_nil.
    dependent destruction l.
      apply take_nil.
      simpl. rewrite IHm'; auto; omega.
Qed.
(* end hide *)

Theorem drop_length' :
  forall (A : Type) (m n : nat) (l : vec A n),
    n <= m -> eq_dep (drop m l) [].
(* begin hide *)
Proof.
  induction m as [| m']; intros.
    rewrite drop_0. dependent destruction l; try omega. trivial.
    destruct l as [| n h t]; simpl.
      trivial.
      rewrite IHm'; auto; omega.
Qed.
(* end hide *)

Theorem length_take :
  forall (A : Type) (m n : nat) (l : vec A n),
    n <= m -> len (take n l) = n.
(* begin hide *)
Proof.
  induction m as [| m']; intros.
    dependent destruction l; try omega. compute. trivial.
    destruct l as [| n h t].
      compute. trivial.
      simpl. rewrite len_vcons, IHm'; auto; omega.
Qed.
(* end hide *)

Theorem drop_take :
  forall (A : Type) (m n : nat) (l : vec A n),
    m <= n -> len (drop m l) = n - m.
(* begin hide *)
Proof.
  induction m as [| m']; intros.
    rewrite drop_0. compute. trivial.
    destruct l as [| n h t]; simpl.
      compute. trivial.
      rewrite IHm'; omega.
Qed.
(* end hide *)

Theorem take_map :
  forall (A B : Type) (f : A -> B) (m n : nat) (l : vec A n),
    map f (take m l) = take m (map f l).
(* begin hide *)
Proof.
  induction m as [| m']; simpl.
    trivial.
    destruct l as [| n h t]; simpl; try rewrite IHm'; trivial.
Restart.
  induction m; destruct l; simpl; intros; rewrite ?IHm; auto.
Qed.
(* end hide *)

Theorem drop_map :
  forall (A B : Type) (f : A -> B) (m n : nat) (l : vec A n),
    eq_dep (map f (drop m l)) (drop m (map f l)).
(* begin hide *)
Proof.
  induction m as [| m']; intros.
    rewrite ?drop_0. trivial.
    destruct l; simpl.
      trivial.
      apply IHm'.
Qed.
(* end hide *)

Theorem take_elem :
  forall (A : Type) (m n : nat) (l : vec A n) (x : A),
    elem x (take m l) -> elem x l.
(* begin hide *)
Proof.
  induction m as [| m'].
    simpl. inversion 1.
    destruct l as [| n h t]; simpl; inversion 1; subst; constructor.
      apply IHm'. apply inj_pair2 in H4. subst. assumption.
Qed.
(* end hide *)

Print Assumptions take_elem.

Theorem drop_elem :
  forall (A : Type) (m n : nat) (l : vec A n) (x : A),
    elem x (drop m l) -> elem x l.
(* begin hide *)
Proof.
  induction m as [| m']. td.
    rewrite drop_0 in H. assumption.
    destruct l as [| n h t]; simpl.
      inversion 1.
      intros. constructor. apply IHm'. assumption.
Qed.
(* end hide *)

Theorem take_take :
  forall (A : Type) (m m' n : nat) (l : vec A n),
    eq_dep (take m (take m' l)) (take m' (take m l)).
(* begin hide *)
Proof.
  induction m; destruct m'; intros; trivial.
  destruct l as [| n h t]; simpl; try rewrite IHm; trivial.
Qed.
(* end hide *)

Lemma drop_S :
  forall (A : Type) (m m' n : nat) (l : vec A n),
    eq_dep (drop (S m) (drop m' l)) (drop m' (drop (S m) l)).
(* begin hide *)
Proof.
  induction m; destruct l; simpl.
    Check drop_nil.
    remember (drop m' (@vnil A)) as x. dependent destruction x. trivial.
    remember (drop m' (a :: l)) as x. dependent destruction x.
Admitted.
(* end hide *) 

Theorem drop_drop :
  forall (A : Type) (m m' n : nat) (l : vec A n),
    eq_dep (drop m (drop m' l)) (drop m' (drop m l)).
(* begin hide *)
Proof.
  induction m; intros.
    rewrite ?drop_0. trivial.
    rewrite drop_S. trivial.
Qed.
(* end hide *)

(* begin hide *)
Theorem take_drop_rev :
  forall (A : Type) (m n : nat) (l : vec A n),
    eq_dep (take m (rev l)) (rev (drop (n - m) l)).
Proof.
  induction m as [| m']; intros.
    rewrite take_0, <- minus_n_O, drop_all. simpl. trivial.
    destruct l.
      rewrite ?rev_nil. rewrite take_nil, drop_nil. simpl. trivial.
      
      SearchAbout rev.
Abort.
(* end hide *)

Theorem take_drop :
  forall (A : Type) (m m' n : nat) (l : vec A n),
    eq_dep (take m (drop m' l)) (drop m' (take (m + m') l)).
(* begin hide *)
Proof.
  induction m; intros.
    simpl. rewrite take_length'.
Admitted.
(* end hide *)

(** *** [filter] *)

(** Napisz funkcję [filter], która zostawia na liście elementy, dla których
    funkcja [p] zwraca [true], a usuwa te, dla których zwraca [false]. *)

(* begin hide *)
Fixpoint filter {A : Type} {n : nat} (f : A -> bool) (l : vec A n)
  : vec A n :=
match l with
    | [] => []
    | h :: t => if f h then h :: filter f t else filter f t
end.
(* end hide *)

Theorem filter_false : forall (A : Type) (l : list A),
    filter (fun _ => false) l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; trivial.
Qed.
(* end hide *)

Theorem filter_true : forall (A : Type) (l : list A),
    filter (fun _ => true) l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem filter_spec :
    forall (A : Type) (p : A -> bool) (l : list A) (x : A),
        p x = false -> ~ elem x (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    inversion 1.
    case_eq (p h); intro.
      inversion 1; subst.
        rewrite H0 in H. inversion H.
        unfold not in IHt. apply IHt with x; assumption.
      apply IHt. assumption.
Qed.
(* end hide *)

Theorem filter_app :
    forall (A : Type) (p : A -> bool) (l1 l2 : list A),
        filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    destruct (p h1); rewrite IHt1; trivial.
Qed.
(* end hide *)

Theorem filter_rev :
    forall (A : Type) (p : A -> bool) (l : list A),
        filter p (rev l) = rev (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite filter_app; simpl. destruct (p h); simpl.
      rewrite IHt. trivial.
      rewrite app_nil_r. rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem filter_comm :
    forall (A : Type) (f g : A -> bool) (l : list A),
        filter f (filter g l) = filter g (filter f l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    case_eq (f h); case_eq (g h); intros;
    simpl; repeat rewrite H; repeat rewrite H0; rewrite IHt; trivial.
Qed.
(* end hide *)

Theorem filter_idempotent :
    forall (A : Type) (f : A -> bool) (l : list A),
        filter f (filter f l) = filter f l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    case_eq (f h); simpl; intro; try rewrite H, IHt; trivial.
Qed.
(* end hide *)

Theorem filter_map :
    forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
        filter p (map f l) = map f (filter (fun x : A => p (f x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    destruct (p (f h)); simpl; rewrite IHt; trivial.
Qed.
(* end hide *)

Theorem filter_repeat_false :
    forall (A : Type) (p : A -> bool) (n : nat) (x : A),
        p x = false -> filter p (repeat n x) = [].
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    trivial.
    rewrite H. apply IHn'. assumption.
Qed.
(* end hide *)

Theorem filter_repeat_true :
    forall (A : Type) (p : A -> bool) (n : nat) (x : A),
        p x = true -> filter p (repeat n x) = repeat n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    trivial.
    rewrite H. rewrite IHn'; [trivial | assumption].
Qed.
(* end hide *)

Theorem filter_length :
    forall (A : Type) (p : A -> bool) (l : list A),
        length (filter p l) <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    trivial.
    destruct (p h).
      simpl. apply le_n_S. assumption.
      apply le_trans with (length t).
        assumption.
        apply le_S. apply le_n.
Qed.
(* end hide *)

Theorem filter_join :
    forall (A : Type) (p : A -> bool) (lla : list (list A)),
        join (map (filter p) lla) = filter p (join lla).
(* begin hide *)
Proof.
  induction lla as [| hl tl]; simpl.
    trivial.
    rewrite filter_app. rewrite IHtl. trivial.
Qed.
(* end hide *)

(** *** [takeWhile] i [dropWhile] *)

(** Zdefiniuj funkcje [takeWhile] oraz [dropWhile], które, dopóki
    funkcja [p] zwraca [true], odpowiednio biorą lub usuwają elementy
    z listy. *)

(* begin hide *)
Fixpoint takeWhile {A : Type} (p : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if p h then h :: takeWhile p t else []
end.

Fixpoint dropWhile {A : Type} (p : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if p h then dropWhile p t else l
end.
(* end hide *)

Theorem takeWhile_false : forall (A : Type) (l : list A),
    takeWhile (fun _ => false) l = [].
(* begin hide *)
Proof.
  destruct l; simpl; trivial.
Qed.
(* end hide *)

Theorem dropWhile_false : forall (A : Type) (l : list A),
    dropWhile (fun _ => false) l = l.
(* begin hide *)
Proof.
  destruct l; simpl; trivial.
Qed.
(* end hide *)

Theorem takeWhile_spec :
    forall (A : Type) (p : A -> bool) (l : list A) (x : A),
        elem x (takeWhile p l) -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    case_eq (p h); intro.
      rewrite H0 in H. inversion H; subst.
        trivial.
        apply IHt. assumption.
      rewrite H0 in H. inversion H.
Qed.
(* end hide *)

(* begin hide *)
(*Theorem takeWhile_spec' :
    forall (A : Type) (p : A -> bool) (l : list A) (x : A),
        elem x l -> ~ elem x (takeWhile p l) -> p x = false.
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    case_eq (p h); inversion H; subst; intro; rewrite H1 in H0.
      cut False. inversion 1. apply H0. constructor.
      apply IHt.
        assumption.
        apply elem_inv_tail with h. assumption.
      assumption.
      apply IHt.
        assumption.
        apply elem_inv_tail with h. assumption.
  *)
(* end hide *)  

Theorem dropWhile_spec :
    forall (A : Type) (p : A -> bool) (l : list A) (x : A),
        elem x l -> ~ elem x (dropWhile p l) -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    case_eq (p h); intro.
      rewrite H1 in H0. inversion H; subst.
        assumption.
        apply IHt; assumption.
      rewrite H1 in H0. contradiction H.
Qed.
(* end hide *)

Theorem takeWhile_idempotent :
    forall (A : Type) (p : A -> bool) (l : list A),
        takeWhile p (takeWhile p l) = takeWhile p l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    case_eq (p h); simpl; intro.
      rewrite H. rewrite IHt. trivial.
      trivial.
Qed.
(* end hide *)

Theorem dropWhile_idempotent :
    forall (A : Type) (p : A -> bool) (l : list A),
        dropWhile p (dropWhile p l) = dropWhile p l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    case_eq (p h); simpl; intro; [rewrite IHt | rewrite H]; trivial.
Qed.
(* end hide *)

Theorem takeWhile_repeat :
    forall (A : Type) (p : A -> bool) (n : nat) (x : A),
        p x = true -> takeWhile p (repeat n x) = repeat n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    trivial.
    rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem dropWhile_repeat :
    forall (A : Type) (p : A -> bool) (n : nat) (x : A),
        p x = true -> dropWhile p (repeat n x) = [].
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    trivial.
    rewrite H, IHn'; trivial.
Qed.
(* end hide *)

(** *** Zwijanie *)

Fixpoint foldr {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : B :=
match l with
    | [] => b
    | h :: t => f h (foldr f b t)
end.

Fixpoint foldl {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : A :=
match l with
    | [] => a
    | h :: t => foldl f (f a h) t
end.

(** Nie będę na razie tłumaczył, jaka ideologia stoi za [foldr] i [foldl].
    Napiszę o tym później, a na razie porcja zadań.

    Zaimplementuj za pomocą [foldr] lub [foldl] następujące funkcje:
    [length], [app], [rev], [map], [join], [filter], [takeWhile],
    [dropWhile].

    Udowodnij, że zdefiniowane przez ciebie funkcje pokrywają się ze
    swoimi klasycznymi odpowiednikami. *)

(* begin hide *)
(* Reszta polecenia: [repeat], [nth], [take], [drop] *)

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

(*Definition repeatF {A : Type} (n : nat) (x : A) : list A :=
    foldr (fun n t => match n with | 0 => t | S n' => x :: t end) [x] [].*)

Definition filterF {A : Type} (p : A -> bool) (l : list A) : list A :=
    foldr (fun h t => if p h then h :: t else t) [] l.

Definition takeWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
    foldr (fun h t => if p h then h :: t else []) [] l.

(*Definition dropWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
    foldr (fun h t => if p h then t else h :: t) [] l.*)

(*Definition dropWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
    foldl (fun t h => if p h then t else h :: t) [] l.*)

(* end hide *)

Theorem lengthF_spec : forall (A : Type) (l : list A),
    lengthF l = length l.
(* begin hide *)
Proof.
  unfold lengthF; induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem appF_spec : forall (A : Type) (l1 l2 : list A),
    appF l1 l2 = l1 ++ l2.
(* begin hide *)
Proof.
  unfold appF; induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Theorem revF_spec : forall (A : Type) (l : list A),
    revF l = rev l.
(* begin hide *)
Proof.
  unfold revF; induction l as [| h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

(* begin hide *)
Theorem revF'_spec : forall (A : Type) (l : list A),
    revF' l = rev l.
Proof.
  unfold revF'. intros. replace (rev l) with (rev l ++ []).
    remember [] as acc. clear Heqacc. generalize dependent acc.
    induction l as [| h t]; simpl; intros; subst.
      trivial.
      rewrite IHt. rewrite <- app_cons2. trivial.
    apply app_nil_r.
Qed.
(* end hide *)

Theorem mapF_spec : forall (A B : Type) (f : A -> B) (l : list A),
    mapF f l = map f l.
(* begin hide *)
Proof.
  unfold mapF; induction l as [| h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem joinF_spec : forall (A : Type) (l : list (list A)),
    joinF l = join l.
(* begin hide *)
Proof.
  unfold joinF; induction l as [| h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem filterF_spec : forall (A : Type) (p : A -> bool) (l : list A),
    filterF p l = filter p l.
(* begin hide *)
Proof.
  unfold filterF; induction l as [| h t].
    simpl. trivial.
    simpl. rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem takeWhileF_spec : forall (A : Type) (p : A -> bool) (l : list A),
    takeWhileF p l = takeWhile p l.
(* begin hide *)
Proof.
  unfold takeWhileF; induction l as [| h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

(* begin hide *)
(* Theorem dropWhileF_spec : forall (A : Type) (p : A -> bool) (l : list A),
    dropWhileF p l = dropWhile p l.
(* begin hide *)
Proof.
  unfold dropWhileF; intros. remember [] as acc.
  generalize dependent acc.
  induction l as [| h t]; simpl; intros.
    trivial.
    destruct (p h).
      rewrite IHt; trivial.
      rewrite IHt.
Qed. *)
(* end hide *)

(** *** [partition] *)

(** Napisz funkcję [partition], która dzieli listę [l] na listy
    elementów spełniających i niespełniających pewnego warunku
    boolowskiego. *)

(* begin hide *)
Fixpoint partition {A : Type} (p : A -> bool) (l : list A)
    : list A * list A :=
match l with
    | [] => ([], [])
    | h :: t => let (l1, l2) := partition p t in
        if p h then (h :: l1, l2) else (l1, h :: l2)
end.
(* end hide *)

Theorem partition_spec : forall (A : Type) (p : A -> bool) (l : list A),
    partition p l = (filter p l, filter (fun x => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    destruct (partition p t). destruct (p h); simpl; inversion IHt; trivial.
Qed.
(* end hide *)

(** *** [zip] *)

(** Napisz funkcję [zip : forall A B : Type, list A -> list B -> list (A * B)],
    która spełnia poniższą specyfikację. Co robi ta funkcja? *)

(* begin hide *)
Fixpoint zip {A B : Type} (la : list A) (lb : list B) : list (A * B) :=
match la, lb with
    | [], _ => []
    | _, [] => []
    | ha :: ta, hb :: tb => (ha, hb) :: zip ta tb
end.
(* end hide *)

Theorem zip_nil_l :
  forall (A B : Type) (l : list B), zip (@nil A) l = [].
(* begin hide *)
Proof. simpl. trivial. Qed.
(* end hide *)

Theorem zip_nil_r :
  forall (A B : Type) (l : list A), zip l (@nil B) = [].
(* begin hide *)
Proof. destruct l; simpl; trivial. Qed.
(* end hide *)

Theorem zip_length :
  forall (A B : Type) (la : list A) (lb : list B),
    length (zip la lb) = min (length la) (length lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; intros.
    simpl. trivial.
    destruct lb as [| hb tb]; simpl.
      trivial.
      rewrite IHta. trivial.
Qed.
(* end hide *)

Theorem zip_not_rev :
  exists (A B : Type) (la : list A) (lb : list B),
    zip (rev la) (rev lb) <> rev (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists [true; false; true], [false; true].
  simpl. inversion 1.
Qed.
(* end hide *)

Theorem zip_head :
  forall (A B : Type) (la : list A) (lb : list B) (a : A) (b : B),
    head la = Some a -> head lb = Some b -> head (zip la lb) = Some (a, b).
(* begin hide *)
Proof.
  induction la as [| ha ta]; destruct lb as [| hb tb]; simpl; intros;
  inversion H; inversion H0; trivial.
Qed.
(* end hide *)

Theorem zip_tail :
  forall (A B : Type) (la ta : list A) (lb tb : list B),
    tail la = Some ta -> tail lb = Some tb ->
      tail (zip la lb) = Some (zip ta tb).
(* begin hide *)
Proof.
  induction la as [| ha ta']; simpl.
    inversion 1.
    destruct lb as [| hb tb']; simpl.
      inversion 2.
      do 2 inversion 1. trivial.
Qed.
(* end hide *)

Theorem zip_not_app :
  exists (A B : Type) (la la' : list A) (lb lb' : list B),
    zip (la ++ la') (lb ++ lb') <> zip la lb ++ zip la' lb'.
(* begin hide *)
Proof.
  exists bool, bool. exists [true], [false], [true; false; true], [].
  simpl. inversion 1.
Qed.
(* end hide *)

Theorem zip_map :
  forall (A B A' B' : Type) (f : A -> A') (g : B -> B')
  (la : list A) (lb : list B),
    zip (map f la) (map g lb) =
    map (fun x => (f (fst x), g (snd x))) (zip la lb).
(* begin hide *)
Proof.
  induction la; destruct lb; simpl; trivial.
    rewrite IHla. trivial.
Qed.
(* end hide *)

Theorem zip_not_filter :
  exists (A B : Type) (pa : A -> bool) (pb : B -> bool)
  (la : list A) (lb : list B),
    zip (filter pa la) (filter pb lb) <>
    filter (fun x => andb (pa (fst x)) (pb (snd x))) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (fun a : bool => if a then true else false). exists negb.
  exists [false; true], [false; true].
  simpl. inversion 1.
Qed.
(* end hide *)

Theorem zip_take :
  forall (A B : Type) (n : nat) (la : list A) (lb : list B),
    zip (take n la) (take n lb) = take n (zip la lb).
(* begin hide *)
Proof.
  induction n as [| n']; simpl.
    trivial.
    destruct la, lb; simpl; trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem zip_drop :
  forall (A B : Type) (n : nat) (la : list A) (lb : list B),
    zip (drop n la) (drop n lb) = drop n (zip la lb).
(* begin hide *)
Proof.
  induction n as [| n']; simpl.
    trivial.
    destruct la, lb; simpl; trivial.
      rewrite zip_nil_r. trivial.
Qed.
(* end hide *)

Theorem zip_elem :
  forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    elem (a, b) (zip la lb) -> elem a la /\ elem b lb.
(* begin hide *)
Proof.
  induction la; simpl.
    inversion 1.
    destruct lb; simpl; inversion 1; subst; simpl in *.
      split; constructor.
      destruct (IHla _ H2). split; right; assumption.
Qed.
(* end hide *)

Theorem zip_not_elem :
  exists (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    elem a la /\ elem b lb /\ ~ elem (a, b) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists true, false.
  exists [true; false], [true; false].
  simpl. repeat split.
    repeat constructor.
    repeat constructor.
    inversion 1; subst. inversion H2; subst. inversion H3.
Qed.
(* end hide *)

(** *** [intersperse] *)

(** Napisz funkcję [intersperse], który wstawia element [x : A] między
    każde dwa elementy z listy [l : list A]. *)

(* begin hide *)
Fixpoint intersperse {A : Type} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | [h] => [h]
    | h :: t => h :: x :: intersperse x t
end.
(* end hide *)

Theorem intersperse_length :
  forall (A : Type) (x : A) (l : list A),
    length (intersperse x l) = 2 * length l - 1.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl in *; trivial.
  Require Import Omega. rewrite IHl. omega.
Qed.
(* end hide *)

Theorem intersperse_app_last2 :
  forall (A : Type) (x y z : A) (l : list A),
    intersperse x (l ++ [y; z]) =
    intersperse x (l ++ [y]) ++ [x; z].
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl in *; trivial.
  rewrite IHl. trivial.
Qed.
(* end hide *)

Theorem intersperse_rev :
  forall (A : Type) (x : A) (l : list A),
    intersperse x (rev l) = rev (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl; trivial.
  simpl in *. rewrite <- IHl. 
  rewrite <- !app_assoc; simpl. apply intersperse_app_last2.
Qed.
(* end hide *)

(* begin hide *)
Theorem intersperse_app :
  forall (A : Type) (x : A) (l l' : list A),
    intersperse x (l ++ l') = intersperse x l ++ intersperse x l'.
Proof.
  induction l as [| h [| hh t]]; simpl.
    trivial.
    destruct l'; trivial.
    destruct l' as [| h' t']; simpl.
Abort.
(* end hide *)

Theorem intersperse_filter :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = false -> filter p (intersperse x l) = filter p l.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl; intros; trivial.
    rewrite H. simpl in IHl. rewrite (IHl H). trivial.
Qed.
(* end hide *)

Theorem intersperse_map :
  forall (A B : Type) (f : A -> B) (l : list A) (a : A) (b : B),
    f a = b -> intersperse b (map f l) = map f (intersperse a l).
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl; trivial; intros.
  rewrite H. simpl in *. rewrite (IHl _ _ H). trivial.
Qed.
(* end hide *)

(** *** [replicate] *)

(** Napsiz funkcję [replicate], która powiela dany element [n] razy, tworząc
    listę. *)

(* begin hide *)
Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
match n with
    | 0 => []
    | S n' => x :: replicate n' x
end.
(* end hide *)

Theorem replicate_length :
  forall (A : Type) (n : nat) (x : A),
    length (replicate n x) = n.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_plus_app :
  forall (A : Type) (n m : nat) (x : A),
    replicate (n + m) x = replicate n x ++ replicate m x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_rev :
  forall (A : Type) (n : nat) (x : A),
    rev (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; trivial.
  change [x] with (replicate 1 x).
  rewrite IHn', <- replicate_plus_app, plus_comm. simpl. trivial.
Qed.
(* end hide *)

Theorem replicate_elem :
  forall (A : Type) (n : nat) (x y : A),
    elem y (replicate n x) <-> n <> 0 /\ x = y.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; simpl; inversion 1; subst.
      split; auto.
      destruct (IHn' H2). auto.
    intros [H H']. rewrite H'. destruct n as [| n'].
      contradiction H. trivial.
      simpl. left.
Qed.
(* end hide *)

Theorem replicate_map :
  forall (A B : Type) (f : A -> B) (n : nat) (x : A),
    map f (replicate n x) = replicate n (f x).
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intro; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_nth :
  forall (A : Type) (i n : nat) (x : A),
    i < n -> nth i (replicate n x) = Some x.
(* begin hide *)
Proof.
  induction i as [| i']; destruct n as [| n']; simpl; intros.
    omega.
    trivial.
    omega.
    rewrite IHi'.
      trivial.
      apply lt_S_n. assumption.
Qed.
(* end hide *)

Theorem replicate_head :
  forall (A : Type) (n : nat) (x : A),
    head (replicate (S n) x) = Some x.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem replicate_tail :
  forall (A : Type) (n : nat) (x : A),
    tail (replicate (S n) x) = Some (replicate n x).
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem replicate_take :
  forall (A : Type) (m n : nat) (x : A),
    take m (replicate n x) = replicate (min m n) x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct n as [| n']; simpl; intros; trivial.
  rewrite IHm'. trivial.
Qed.
(* end hide *)

Theorem replicate_drop :
  forall (A : Type) (m n : nat) (x : A),
    drop m (replicate n x) = replicate (n - m) x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct n as [| n']; simpl; intros; trivial.
Qed.
(* end hide *)

Theorem replicate_filter_true :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = true -> filter p (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_filter_false :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = false -> filter p (replicate n x) = [].
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_takeWhile_true :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = true -> takeWhile p (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_takeWhile_false :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = false -> takeWhile p (replicate n x) = [].
(* begin hide *)
Proof.
  destruct n as [| n']; simpl; intros; try rewrite H; trivial.
Qed.
(* end hide *)

Theorem replicate_dropWhile_true :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = true -> dropWhile p (replicate n x) = [].
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_dropWhile_false :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = false -> dropWhile p (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  destruct n as [| n']; simpl; intros; try rewrite H; trivial.
Qed.
(* end hide *)

Theorem replicate_zip :
  forall (A B : Type) (n m : nat) (a : A) (b : B),
    zip (replicate n a) (replicate m b) = replicate (min n m) (a, b).
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'];
  simpl; intros; try rewrite IHn'; trivial.
Qed.
(* end hide *)

(** *** [zipWith] *)

(** Zdefiniuj funkcję [zipWith], która spełnia poniższą specyfikację. *)

(* begin hide *)
Fixpoint zipWith {A B C : Type} (f : A -> B -> C)
  (la : list A) (lb : list B) : list C :=
match la, lb with
    | [], _ => []
    | _, [] => []
    | ha :: ta, hb :: tb => f ha hb :: zipWith f ta tb
end.
(* end hide *)

Theorem zipWith_spec :
  forall (A B C : Type) (f : A -> B -> C) (la : list A) (lb : list B),
    zipWith f la lb = map (fun x => f (fst x) (snd x)) (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; destruct lb as [| hb tb];
  simpl; intros; try rewrite IHta; trivial.
Qed.
(* end hide *)

(** *** [unzip] (odtąd TODO!) *)

(** Zdefiniuj funkcję [unzip], która jest w pewnym sensie "odwrotna"
    do [zip]. *)

(* begin hide *)
Fixpoint unzip {A B : Type} (l : list (A * B)) : list A * list B :=
match l with
    | [] => ([], [])
    | (ha, hb) :: t =>
        let (ta, tb) := unzip t in (ha :: ta, hb :: tb)
end.
(* end hide *)

Theorem zip_unzip :
  forall (A B : Type) (l : list (A * B)),
    zip (fst (unzip l)) (snd (unzip l)) = l.
(* begin hide *)
Proof.
  induction l as [| [ha hb] t]; simpl.
    trivial.
    destruct (unzip t). simpl in *. rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem unzip_zip :
  exists (A B : Type) (la : list A) (lb : list B),
    unzip (zip la lb) <> (la, lb).
(* begin hide *)
Proof.
  exists unit, unit, [], [tt]. simpl. inversion 1.
Qed.
(* end hide *)

(** *** [find] *)

(** Napisz funkcję [find], która znajduje pierwszy element na liście,
    który spełnia podany predykat boolowski. Podaj i udowodnij jej
    specyfikację. *)

(* begin hide *)
Function find {A : Type} (p : A -> bool) (l : list A) : option A :=
match l with
    | [] => None
    | h :: t => if p h then Some h else find p t
end.
(* end hide *)

Theorem find_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    (exists x : A, find p l = Some x) <->
    (exists (h : A) (t : list A), filter p l = h :: t).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; simpl; destruct 1.
      congruence.
      destruct (p h).
        exists h, (filter p t). trivial.
        edestruct IHt.
          exists x. assumption.
          destruct H0 as [t0 Ht0]. exists x0, t0. assumption.
    induction l as [| h t]; simpl; destruct 1 as [x [l H]].
      inversion H.
      destruct (p h).
        exists h. trivial.
        edestruct IHt.
          exists x, l. assumption.
          exists x0. assumption.
Qed.
(* end hide *)

(** *** [findIndex] *)

(** Napisz funkcję [findIndex], która znajduje indeks pierwszego elementu,
    który spełnia predykat boolowski [p]. *)

(* begin hide *)
Function findIndex {A : Type} (p : A -> bool) (l : list A) : option nat :=
match l with
    | [] => None
    | h :: t =>
        if p h
        then Some 0
        else match findIndex p t with
            | None => None
            | Some n => Some (S n)
        end
end.
(* end hide *)

Theorem findIndex_spec :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n -> exists x : A, nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    inversion 1.
    case_eq (p h); intros.
      inversion H0; subst; clear H0; simpl. exists h. auto. 
      case_eq (findIndex p t); intros.
        rewrite H1 in H0. inversion H0; subst; clear H0.
          destruct (IHt _ H1). exists x. simpl. assumption.
        rewrite H1 in H0. inversion H0.
Restart.
  intros A p l. functional induction @findIndex A p l;
  intros; inversion H; subst; clear H; simpl in *.
    exists h. auto.
    destruct (IHo _ e1) as [x H]. exists x. assumption.
Qed.
(* end hide *)

(** *** [findIndices] *)

(** Napisz funkcję [findIndices], która znajduje indeksy wszystkich elemtnów
    listy, które spełniają predykat boolowski [p]. *)

(* begin hide *)
Definition findIndices {A : Type} (p : A -> bool) (l : list A) : list nat :=
  (fix f (l : list A) (n : nat) : list nat :=
  match l with
      | [] => []
      | h :: t => if p h then n :: f t (S n) else f t (S n)
  end) l 0.

(*Theorem findIndices_spec :
  forall (A : Type) (p : A -> bool) (l : list A) (indices : list nat),
    findIndices p l = indices -> forall n : nat, elem n indices ->*)

(* end hide *)

(*Section fns.

Variables A B : Type.

Definition len {n : nat} (_ : Vec A n) : nat := n.

Fixpoint repeat (n : nat) (a : A) : Vec A n :=
match n with
    | 0 => Nil
    | S n' => Cons a (repeat n' a)
end.

Fixpoint take {n : nat} (m : nat) (v : Vec A n) : Vec A (min n m) := 
match v with
    | Nil => Nil
    | Cons _ x xs => match m with
        | 0 => Nil
        | S m' => Cons x (take m' xs)
    end
end.

Fixpoint toList {n : nat} (v : Vec A n) : list A :=
match v with
    | Nil => nil
    | Cons _ x xs => cons x (toList xs)
end.

(*Definition fold {n : nat} (f : A -> B -> B) (v : Vec A n) (b : B) : B := 
    fold f (toList v) b.*)

Fixpoint foldr {n : nat} (f : A -> B -> B) (b : B) (v : Vec A n) : B :=
match v with
    | Nil => b
    | Cons _ h t => f h (foldr f b t)
end.

Fixpoint fromList (l : list A) : Vec A (length l) :=
match l with
    | nil => Nil
    | cons x xs => Cons x (fromList xs)
end.

Theorem toList_length : forall (n : nat) (v : Vec A n),
    length (toList v) = n.
Proof.
  induction v; simpl; try rewrite IHv; trivial.
Qed.

Fixpoint app {n m : nat} (v1 : Vec A n) (v2 : Vec A m) : Vec A (n + m) :=
match v1 with
    | Nil => v2
    | Cons _ x xs => Cons x (app xs v2)
end.

(*Fixpoint filter {n : nat} (f : A -> bool) (v : Vec A n) :=
    let l := MyList.filter f (toList v) in fromList l.*)

End fns.

Fixpoint map {A B : Type} {n : nat} (f : A -> B) (v : Vec A n) : Vec B n :=
match v with
    | Nil => Nil
    | Cons m x xs => Cons (f x) (map f xs)
end.

Definition fives := repeat 5 5.
Definition sixList := [6; 6; 6].

Eval compute in fives.

Eval compute in take 2 fives.
Eval compute in foldr plus 0 fives.
Eval compute in (fromList sixList).
Eval compute in (app fives fives).
(*Eval compute in filter (fun n => match n with | 5 => false | _ => true end)
fives.*)

(*Instance Functor_Vec (n : nat) : Functor (fun A : Set => Vec A n).
split with (@map n);
unfold map; intros; rewrite fn_ext; induction a;
try rewrite IHa; trivial.
Defined.*)


Require Import JMeq.

Theorem JMeq_Cons :
  forall (A B : Type) (n m : nat) (h1 : A) (h2 : B)
  (t1 : Vec A n) (t2 : Vec B m),
    A = B -> n = m -> JMeq h1 h2 -> JMeq t1 t2 ->
      JMeq (Cons h1 t1) (Cons h2 t2).
Proof.
  intros; subst. rewrite H1, H2. trivial.
Qed.

Theorem toList_fromList : forall (A : Type) (n : nat) (v : Vec A n),
    JMeq (fromList (toList v)) v.
Proof.
  induction v; simpl.
    reflexivity.
    apply JMeq_Cons; auto. apply toList_length.
Qed.

(*Fixpoint vfilter {A : Type} {n : nat} (p : A -> bool) (v : Vec A n) :=
match v return 
    match v with | Nil => Vec A 0 | Cons _ h t => if p h
        then Vec A (S (length (vfilter p t)))
        else Vec A (length (vfilter p t))
    end
with
    | Nil => Nil
    | Cons _ h t => if p h then Cons h (vfilter p t) else vfilter p t
end.*)

Require Import Eqdep.

Print inj_pair2.















Print Assumptions JMeq_Cons.

Print JMeq_eq.

Require Import Program.

Theorem wut_1 : forall (A : Type) (n m : nat),
    n <> m -> Vec A n <> Vec A m.
Proof.
  induction n as [| n'].
    destruct m as [| m'].
      intros. contradiction H. trivial.
      intros. intro. inversion H0.

Theorem wwwut : forall (A : Type) (n m : nat),
    Vec A n = Vec A m -> n = m.
Proof.
  intros. dependent destruction H.

Theorem vec_wut : forall (A B : Type) (n m : nat) (h1 : A) (h2 : B)
    (t1 : Vec A n) (t2 : Vec B m), n = m ->
        JMeq h1 h2 -> JMeq t1 t2 -> JMeq (Cons h1 t1) (Cons h2 t2).
Proof.
  intros. subst. destruct H0. inversion H1.
    apply inj_pair2 in H. subst. trivial.
Qed.

Theorem vec_wut' : forall (A B : Type) (n m : nat) (h1 : A) (h2 : B)
    (t1 : Vec A n) (t2 : Vec B m),
        JMeq h1 h2 -> JMeq t1 t2 -> JMeq (Cons h1 t1) (Cons h2 t2).
Proof.
  intros. destruct H. inversion H0.
  assert (JMeq (len t1) (len t2)).
    compute. trivial.
  compute in H0.
Abort.

Inductive Wydmuszka (A : Type) (n : nat) : Type :=
    | WydNil : Wydmuszka A n
    | WyCons : A -> Wydmuszka A n -> Wydmuszka A n.

Theorem wydmuszka_inversion : forall (A B : Type) (n m : nat)
    (w1 : Wydmuszka A n) (w2 : Wydmuszka B m), JMeq w1 w2 -> n = m.
Proof.
  intros. inversion H.

Theorem all_len : forall (A : Type) (n : nat) (v : Vec A n),
    len v = n.
Proof.
  intros. compute. trivial.
Qed.

Theorem all_len2 : forall (A : Type) (n m : nat) (v : Vec A n),
    Vec A n = Vec A m -> len v = m.
Proof.
  intros. destruct H. *)

(* end hide *)