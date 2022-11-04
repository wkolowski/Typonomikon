Require Import List.
Import ListNotations.

Require Import JMeq.
Require Import Eqdep.
Require Import Lia Arith.

Arguments eq_dep [U P p] _ [q] _.

Set Implicit Arguments.

Fixpoint RVec (A : Type) (n : nat) : Type :=
match n with
| 0    => unit
| S n' => A * RVec A n'
end.

Definition vnil {A : Type} : RVec A 0 := tt.

Definition vcons {A : Type} {n : nat} (h : A) (t : RVec A n) : RVec A (S n) :=
  (h, t).

(** *** Reguła indukcji *)

Fixpoint RVec_rect
  {A : Type} {P : forall n : nat, RVec A n -> Type}
  (Hvnil  : P 0 vnil)
  (Hvcons : forall (n : nat) (h : A) (t : RVec A n), P n t -> P (S n) (vcons h t))
  {n : nat} (v : RVec A n) {struct n} : P n v.
Proof.
  destruct n as [| n'].
    destruct v. exact Hvnil.
    destruct v as [h t]. exact (Hvcons n' h t (RVec_rect A P Hvnil Hvcons n' t)).
Defined.

Fixpoint RVec_ind
  {A : Type} {P : forall n : nat, RVec A n -> Prop}
  (Hvnil  : P 0 vnil)
  (Hvcons : forall (n : nat) (h : A) (t : RVec A n), P n t -> P (S n) (vcons h t))
  {n : nat} (v : RVec A n) {struct n} : P n v.
Proof.
  destruct n as [| n'].
    destruct v. exact Hvnil.
    destruct v as [h t]. exact (Hvcons n' h t (RVec_ind A P Hvnil Hvcons n' t)).
Defined.

(** *** [len] *)

(** Zdefiniuj funkcję [len], która oblicza długość listy. Powinna ona
    wykonywać się w czasie liniowym. *)

(* begin hide *)
Definition len {A : Type} {n : nat} (_ : RVec A n) : nat := n.
(* end hide *)

Lemma len_vnil :
  forall A : Type, len (@vnil A) = 0.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma len_vcons' :
  forall (A : Type) (n : nat) (h : A) (t : RVec A n),
    len (vcons h t) = S n.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma len_vcons :
  forall (A : Type) (n : nat) (h : A) (t : RVec A n),
    len (vcons h t) = S (len t).
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

(** * [app] *)

(** Zdefiniuj funkcję [app], która skleja dwie listy. *)

(* begin hide *)
Fixpoint app {A : Type} {n m : nat} (l1 : RVec A n) (l2 : RVec A m)
  : RVec A (n + m) :=
match n, l1 with
| 0   , _      => l2
| S n', (h, t) => vcons h (app t l2)
end.
(* end hide *)

Notation "l1 +++ l2" := (app l1 l2) (at level 40).

Lemma app_vnil_l :
  forall (A : Type) (n : nat) (l : RVec A n), vnil +++ l = l.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma JMeq_vcons :
  forall (A : Type) (n m : nat) (h h' : A) (t : RVec A n) (t' : RVec A m),
    n = m -> JMeq h h' -> JMeq t t' -> JMeq (vcons h t) (vcons h' t').
(* end hide *)
Proof.
  intros. subst. reflexivity.
Qed.
(* end hide *)

Lemma app_vnil_r :
  forall (A : Type) (n : nat) (l : RVec A n), JMeq (l +++ vnil) l.
(* begin hide *)
Proof.
  intros. apply (@RVec_rect _ (fun n l => JMeq (l +++ vnil) l)); clear n l.
    cbn. reflexivity.
    intros n h t IH. apply JMeq_vcons.
      apply plus_0_r.
      reflexivity.
      apply IH.
Qed.
(* end hide *)

Lemma app_vnil_r' :
  forall (A : Type) (n : nat) (l : RVec A n), eq_dep (l +++ vnil) l.
(* begin hide *)
Proof.
  intros. apply (@RVec_rect _ (fun n l => eq_dep (l +++ vnil) l)); clear n l.
    cbn. reflexivity.
    intros n h t IH. cbn. rewrite IH. reflexivity.
Qed. 
(* end hide *)

Lemma app_assoc :
  forall (A : Type) (x y z : nat) (l1 : RVec A x) (l2 : RVec A y) (l3 : RVec A z),
    eq_dep (l1 +++ (l2 +++ l3)) ((l1 +++ l2) +++ l3).
(* begin hide *)
Proof.
  intros A x y z l1 l2 l3.
  apply (@RVec_rect _ (fun x l1 => eq_dep (l1 +++ (l2 +++ l3)) ((l1 +++ l2) +++ l3))).
    cbn. reflexivity.
    intros n h t IH. cbn. rewrite IH. reflexivity.
Qed.
(* end hide *)

Lemma app_assoc' :
  forall (A : Type) (x y z : nat) (l1 : RVec A x) (l2 : RVec A y) (l3 : RVec A z),
    JMeq (l1 +++ (l2 +++ l3)) ((l1 +++ l2) +++ l3).
(* begin hide *)
Proof.
  intros A x y z l1 l2 l3.
  apply (@RVec_rect _ (fun x l1 => JMeq (l1 +++ (l2 +++ l3)) ((l1 +++ l2) +++ l3))).
    cbn. reflexivity.
    intros n h t IH. cbn. apply JMeq_vcons.
      apply plus_assoc.
      reflexivity.
      exact IH.
Qed.
(* end hide *)

Lemma app_len :
  forall (A : Type) (n m : nat) (l1 : RVec A n) (l2 : RVec A m),
    len (l1 +++ l2) = len l1 + len l2.
(* begin hide *)
Proof.
  intros. unfold len. reflexivity.
Qed.
(* end hide *)

Lemma app_cons :
  forall (A : Type) (n m : nat) (x : A) (l1 : RVec A n) (l2 : RVec A m),
    (vcons x l1) +++ l2 = vcons x (l1 +++ l2).
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma app_cons2 :
  forall (A : Type) (n m : nat) (x : A) (l1 : RVec A n) (l2 : RVec A m),
    JMeq (l1 +++ vcons x l2) ((l1 +++ (vcons x vnil)) +++ l2).
(* begin hide *)
Proof.
  intros A n m x l1 l2.
  apply (@RVec_rect _ (fun n l1 => JMeq (l1 +++ vcons x l2) ((l1 +++ vcons x vnil) +++ l2))). 
    cbn. reflexivity.
    intros n' h t IH. cbn. apply JMeq_vcons.
      rewrite <- plus_assoc. cbn. reflexivity.
      reflexivity.
      exact IH.
Qed.
(* end hide *)

Lemma app_cons2' :
  forall (A : Type) (n m : nat) (x : A) (l1 : RVec A n) (l2 : RVec A m),
    eq_dep (l1 +++ vcons x l2) ((l1 +++ (vcons x vnil)) +++ l2).
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma no_infinite_cons :
  forall (A : Type) (n : nat) (h : A) (t : RVec A n),
    eq_dep t (vcons h t) -> False.
(* begin hide *)
Proof.
  inversion 1. lia.
Qed.
(* end hide *)

(* TODO: RVec *)