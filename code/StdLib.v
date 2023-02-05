Require Import Recdef Bool.

Require Import List.
Import ListNotations.

Inductive Even : nat -> Prop :=
| Even0 : Even 0
| EvenSS : forall n : nat, Even n -> Even (S (S n)).

Function isEven (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S n') => isEven n'
end.

Lemma isEven_spec :
  forall n : nat, reflect (Even n) (isEven n).
Proof.
  intro.
  functional induction (isEven n); try constructor.
    constructor.
    inversion 1.
    destruct IHb; constructor.
      constructor. assumption.
      inversion 1; subst. contradiction.
Qed.

Module Unbundled.

Class Dec (P : Prop) : Type :=
{
  b : bool;
  spec : reflect P b;
}.

Coercion cast (P : Prop) {d : Dec P} : bool := b.

Print Graph.

#[refine]
#[export]
Instance Dec_Even (n : nat) : Dec (Even n) :=
{
  b := isEven n
}.
Proof.
  apply isEven_spec.
Defined.

(* Doesn't work. *)
Fail Definition silly (n : nat) : bool :=
  if Even n then true else false.

End Unbundled.

Module Bundled.

Class Dec : Type :=
{
  P : Prop;
  b : bool;
  spec : reflect P b;
}.

Coercion cast (d : Dec) : bool := b.

#[refine]
#[export]
Instance Dec_Even (n : nat) : Dec :=
{
  P := Even n;
  b := isEven n;
}.
Proof.
  apply isEven_spec.
Defined.

(* Still no luck. *)
Fail Definition silly (n : nat) : bool :=
  if Even n then true else false.

End Bundled.

Module Canonical.

Module Dec.

Record class (P : Prop) := Class
{
  b :> bool;
  spec : reflect P b;
}.

Structure type := Pack
{
  P : Prop;
  class_of :> class P;
}.

Definition dec (t : type) : bool :=
  let 'Pack _ (Class _ b _) := t in b.

Arguments dec {t} : simpl never.
Arguments Class {P} _.

Module theory.
(* Notation "x == y" := (42) (at level 70). *)
End theory.

End Dec.

Import Dec.theory.

Definition Even_class (n : nat) : Dec.class (Even n).
Proof.
  split with (isEven n).
  apply isEven_spec.
Defined.

Canonical Structure Dec_Even (n : nat) : Dec.type :=
  Dec.Pack (Even n) (Even_class n).

(* Still no success. *)
Fail Definition silly (n : nat) : bool :=
  if Even n then true else false.

End Canonical.

From Typonomikon Require Import M.

Module ThisMustWork.

Class Dec (P : Prop) : Type :=
{
  dec : bool;
  dec_spec : reflect P dec;
}.

Arguments dec      _ {Dec}.
Arguments dec_spec _ {Dec}.

#[refine]
#[export]
Instance Dec_isEven (n : nat) : Dec (Even n) :=
{
  dec := isEven n;
}.
Proof.
  apply isEven_spec.
Defined.

Definition not_so_silly (n : nat) : bool :=
  if dec (Even n) then true else false.

Compute not_so_silly 6.

#[refine]
#[export]
Instance Dec_False : Dec False :=
{
  dec := false
}.
Proof.
  constructor.
  destruct 1.
Defined.

#[refine]
#[export]
Instance Dec_True : Dec True :=
{
  dec := true
}.
Proof.
  constructor.
  trivial.
Defined.

#[refine]
#[export]
Instance Dec_or {P Q : Prop} (DP : Dec P) (DQ : Dec Q) : Dec (P \/ Q) :=
{
  dec := dec P || dec Q
}.
Proof.
  destruct (dec_spec P), (dec_spec Q); cbn; constructor.
    1-3: auto.
    intros [p | q]; contradiction.
Defined.

#[refine]
#[export]
Instance Dec_and {P Q : Prop} (DP : Dec P) (DQ : Dec Q) : Dec (P /\ Q) :=
{
  dec := dec P && dec Q
}.
Proof.
  destruct (dec_spec P), (dec_spec Q); cbn; constructor.
    split; assumption.
    all: intros [p' q']; contradiction.
Defined.

#[refine]
#[export]
Instance Dec_impl {P Q : Prop} (DP : Dec P) (DQ : Dec Q) : Dec (P -> Q) :=
{
  dec := negb (dec P) || dec Q
}.
Proof.
  destruct (dec_spec P), (dec_spec Q);
  cbn; constructor; intros.
    assumption.
    intro. apply n, H. assumption.
    assumption.
    contradiction.
Defined.

#[refine]
#[export]
Instance Dec_not
  {P : Prop} (DP : Dec P) : Dec (~ P) :=
{
  dec := negb (dec P)
}.
Proof.
  destruct (dec_spec P); constructor.
    intro. contradiction.
    assumption.
Defined.

#[refine]
#[export]
Instance Dec_exists
  {A : Type} {P : A -> Prop}
  (SA : Searchable A) (DP : forall x : A, Dec (P x))
  : Dec (exists x : A, P x) :=
{
  dec := dec (P (search (fun x : A => dec (P x))))
}.
Proof.
  destruct (@dec_spec _ (DP (search (fun x : A => dec (P x)))));
  constructor.
    exists (search (fun x : A => dec (P x))). assumption.
    intros [x p]. destruct (dec (P (search (fun x : A => dec (P x))))) eqn: Heq.
      destruct (@dec_spec _ (DP (search (fun x : A => dec (P x))))).
        contradiction.
        congruence.
      pose (search_spec (fun x : A => dec (P x)) Heq x). clearbody e. cbn in e.
        destruct (dec_spec (P x)).
          congruence.
          contradiction.
Defined.

#[refine]
#[export]
Instance Dec_forall
  {A : Type} {P : A -> Prop}
  (SA : Searchable A) (DP : forall x : A, Dec (P x))
  : Dec (forall x : A, P x) :=
{
  dec := negb (dec (~ P (search (fun x : A => dec (~ P x)))))
}.
Proof.
  destruct (dec_spec (~ P (search (fun x : A => dec (~ P x)))));
  constructor.
    intro. apply n, H.
    cut (forall x : A, dec (~ P x) = false).
      intros. cbn in H. specialize (H x). destruct (dec_spec (P x)).
        assumption.
        cbn in H. congruence.
      apply (search_spec (fun x : A => dec (~ P x))).
        destruct (dec_spec (~ P (search (fun x : A => dec (~ P x))))).
          contradiction.
          reflexivity.
Defined.

End ThisMustWork.

Module WeakEquality.

Class WeakEquality (A : Type) : Type :=
{
  weq : A -> A -> Prop;
  weq_spec :
    forall x y : A, x = y -> weq x y;
}.

Notation "x ~=~ y" := (weq x y) (at level 50).

#[refine]
#[export]
Instance WeakEquality_Unit : WeakEquality unit :=
{
  weq := fun _ _ => True;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance WeakEquality_Empty : WeakEquality False :=
{
  weq := fun _ _ => True;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance WeakEquality_Fun
  {A B : Type} : WeakEquality (A -> B) :=
{
  weq := fun f g => forall x : A, f x = g x;
}.
Proof.
  intros f g [] x. reflexivity.
Defined.

#[refine]
#[export]
Instance WeakEquality_Fun'
  {A B : Type} (WEB : WeakEquality B): WeakEquality (A -> B) :=
{
  weq := fun f g => forall x : A, weq (f x) (g x);
}.
Proof.
  intros f g [] x. apply weq_spec. reflexivity.
Defined.

#[refine]
#[export]
Instance WeakEquality_Sum
  {A B : Type} (WEA : WeakEquality A) (WEB : WeakEquality B) : WeakEquality (A + B) :=
{
  weq := fun x y =>
    match x, y with
    | inl a1, inl a2 => weq a1 a2
    | inr b1, inr b2 => weq b1 b2
    | _     , _      => False
    end
}.
Proof.
  destruct x, y; intro H; inversion H; subst; clear H.
    apply weq_spec. reflexivity.
    apply weq_spec. reflexivity.
Defined.

#[refine]
#[export]
Instance WeakEquality_Prod
  {A B : Type} (WEA : WeakEquality A) (WEB : WeakEquality B) : WeakEquality (A * B) :=
{
  weq := fun x y =>
    match x, y with
    | (a1, b1), (a2, b2) => weq a1 a2 /\ weq b1 b2
    end
}.
Proof.
  destruct x, y.
  intro H.
  inversion H; subst; clear H.
  split.
    apply weq_spec. reflexivity.
    apply weq_spec. reflexivity.
Defined.

#[refine]
#[export]
Instance WeakEquality_List
  {A B : Type} (WEA : WeakEquality A) : WeakEquality (list A) :=
{
  weq := fix f (x y : list A) : Prop :=
    match x, y with
    | [], [] => True
    | h1 :: t1, h2 :: t2 => weq h1 h2 /\ f t1 t2
    | _, _ => False
    end
}.
Proof.
  induction x as [| h1 t1]; destruct y as [| h2 t2]; cbn; intro H.
    trivial.
    1-2: inversion H.
    inversion H; subst. split.
      apply weq_spec. reflexivity.
      apply IHt1. reflexivity.
Defined.

Set Warnings "-require-in-module".
From Typonomikon Require Import F2.
Set Warnings "require-in-module".

#[refine]
#[export]
Instance WeakEquality_Stream
  {A B : Type} (WEA : WeakEquality A) : WeakEquality (Stream A) :=
{
  weq := sim;
}.
Proof.
  destruct 1. apply sim_refl.
Defined.

End WeakEquality.

Module StrongInequality.

Class StrongDisequality (A : Type) : Type :=
{
  sdeq : A -> A -> Prop;
  sdeq_spec :
    forall x y : A, sdeq x y -> x <> y;
}.

Notation "x =/= y" := (sdeq x y) (at level 50).

#[refine]
#[export]
Instance StrongDisequality_Unit : StrongDisequality unit :=
{
  sdeq := fun _ _ => False;
}.
Proof.
  destruct 1.
Defined.

#[refine]
#[export]
Instance StrongDisequality_Empty : StrongDisequality False :=
{
  sdeq := fun _ _ => True;
}.
Proof.
  destruct x.
Defined.

#[refine]
#[export]
Instance StrongDisequality_Sum
  {A B : Type} (SDA : StrongDisequality A) (SDB : StrongDisequality B) : StrongDisequality (A + B) :=
{
  sdeq := fun x y =>
    match x, y with
    | inl a1, inl a2 => sdeq a1 a2
    | inr b1, inr b2 => sdeq b1 b2
    | inl _ , inr _  => True
    | inr _ , inl _  => True
    end
}.
Proof.
  destruct x, y; intros H1 H2;
  inversion H2; subst.
    apply sdeq_spec in H1. contradiction.
    apply sdeq_spec in H1. contradiction.
Defined.

#[refine]
#[export]
Instance StrongDisequality_Prod
  {A B : Type} (SDA : StrongDisequality A) (SDB : StrongDisequality B) : StrongDisequality (A * B) :=
{
  sdeq := fun x y =>
    match x, y with
    | (a1, b1), (a2, b2) => sdeq a1 a2 \/ sdeq b1 b2
    end
}.
Proof.
  destruct x, y; intros H1 H2;
  inversion H2; subst.
  destruct H1.
    apply sdeq_spec in H. contradiction.
    apply sdeq_spec in H. contradiction.
Defined.

#[refine]
#[export]
Instance StrongDisequality_Fun
  {A B : Type} : StrongDisequality (A -> B) :=
{
  sdeq := fun f g => exists x : A, f x <> g x;
}.
Proof.
  intros f g [x H] p. subst. contradiction.
Defined.

#[refine]
#[export]
Instance StrongDisequality_Fun'
  {A B : Type} (SDB : StrongDisequality B) : StrongDisequality (A -> B) :=
{
  sdeq := fun f g => exists x : A, sdeq (f x) (g x);
}.
Proof.
  intros f g [x H] p. subst. apply sdeq_spec in H. contradiction.
Defined.

#[refine]
#[export]
Instance StrongDisequality_List
  {A B : Type} (SDA : StrongDisequality A) : StrongDisequality (list A) :=
{
  sdeq := fix f (x y : list A) : Prop :=
    match x, y with
    | [], [] => False
    | h1 :: t1, h2 :: t2 => sdeq h1 h2 \/ f t1 t2
    | _, _ => True
    end
}.
Proof.
  induction x as [| h1 t1];
  destruct y as [| h2 t2];
  cbn; intro H;
  inversion 1; subst.
    contradiction.
    destruct H.
      apply sdeq_spec in H. contradiction.
      apply (IHt1 t2). apply H. reflexivity.
Defined.

Set Warnings "-require-in-module".
From Typonomikon Require Import F2.
Set Warnings "require-in-module".

Inductive Ex {A : Type} (R : A -> A -> Prop) : Stream A -> Stream A -> Prop :=
| Ex_hd :
    forall s1 s2 : Stream A, R (hd s1) (hd s2) -> Ex R s1 s2
| Ex_tl :
    forall s1 s2 : Stream A, Ex R (tl s1) (tl s2) -> Ex R s1 s2.

#[refine]
#[export]
Instance StrongDisequality_Stream
  {A B : Type} (SDA : StrongDisequality A) : StrongDisequality (Stream A) :=
{
  sdeq := Ex sdeq;
}.
Proof.
  induction 1; inversion 1; subst.
    apply sdeq_spec in H. contradiction.
    contradiction.
Defined.

End StrongInequality.

Class Pointed (A : Type) : Type :=
{
  point : A;
}.

Set Warnings "-cannot-define-projection".

Class Inhabited (A : Type) : Prop :=
{
  inhabitant : A;
}.

#[export]
Instance Inhabited_Pointed
  (A : Type) (inst : Pointed A)
  : Inhabited A :=
{
  inhabitant := point;
}.

#[export]
Instance Pointed_nat : Pointed nat :=
{
  point := 0
}.

Module StrongNegation.

Class StrongNegation (A : Type) : Type :=
{
  NOT : Type;
  NOT_spec : NOT -> A -> False;
}.

Arguments NOT A {StrongNegation}.

#[refine]
#[export]
Instance StrongNegation_Default
  (A : Type) : StrongNegation A | 999 :=
{
  NOT := A -> False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_Pointed
  (A : Type) (inst : Pointed A)
  : StrongNegation A :=
{
  NOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_Inhabited
  (A : Type) (inst : Inhabited A)
  : StrongNegation A :=
{
  NOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_True :
  StrongNegation True :=
{
  NOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_False :
  StrongNegation False :=
{
  NOT := True;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_or
  (P Q : Prop) (PSN : StrongNegation P) (QSN : StrongNegation Q)
  : StrongNegation (P \/ Q) :=
{
  NOT := NOT P * NOT Q;
}.
Proof.
  destruct 1, 1.
    apply PSN; assumption.
    apply QSN; assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_and
  (P Q : Prop) (PSN : StrongNegation P) (QSN : StrongNegation Q)
  : StrongNegation (P /\ Q) :=
{
  NOT := NOT P + NOT Q;
}.
Proof.
  destruct 1, 1.
    apply PSN; assumption.
    apply QSN; assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_impl
  (P Q : Prop) (QSN : StrongNegation Q)
  : StrongNegation (P -> Q) :=
{
  NOT := P * NOT Q;
}.
Proof.
  destruct 1. intro pq. apply QSN.
    assumption.
    apply pq. assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_forall
  (A : Type) (P : A -> Prop)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation (forall x : A, P x) :=
{
  NOT := {x : A & NOT (P x)};
}.
Proof.
  intros [x np] H.
  apply (PSN x).
    assumption.
    apply H.
Defined.

#[refine]
#[export]
Instance StrongNegation_exists
  (A : Type) (P : A -> Prop)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation (exists x : A, P x) :=
{
  NOT := forall x : A, NOT (P x);
}.
Proof.
  intros H [x np]. apply (PSN x).
    apply H.
    assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_subset
  (A : Type) (P : A -> Prop)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation {x : A | P x} :=
{
  NOT := forall x : A, NOT (P x);
}.
Proof.
  intros H [x np]. apply (PSN x).
    apply H.
    assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_sigma
  (A : Type) (P : A -> Type)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation {x : A & P x} :=
{
  NOT := forall x : A, NOT (P x);
}.
Proof.
  intros H [x np]. apply (PSN x).
    apply H.
    assumption.
Defined.

Compute NOT (forall n : nat, True).
Compute NOT (NOT (forall n : nat, True)).
Compute NOT nat.

End StrongNegation.

Module StrongNegation_Prop.

Class StrongNegation (A : Prop) : Type :=
{
  NOT : Prop;
  NOT_spec : NOT -> A -> False;
}.

Arguments NOT A {StrongNegation}.

#[refine]
#[export]
Instance StrongNegation_Default
  (A : Prop) : StrongNegation A | 999 :=
{
  NOT := A -> False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_Pointed
  (A : Prop) (inst : Pointed A)
  : StrongNegation A :=
{
  NOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_Inhabited
  (A : Prop) (inst : Inhabited A)
  : StrongNegation A :=
{
  NOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_True :
  StrongNegation True :=
{
  NOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_False :
  StrongNegation False :=
{
  NOT := True;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_or
  (P Q : Prop) (PSN : StrongNegation P) (QSN : StrongNegation Q)
  : StrongNegation (P \/ Q) :=
{
  NOT := NOT P /\ NOT Q;
}.
Proof.
  destruct 1, 1.
    apply PSN; assumption.
    apply QSN; assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_and
  (P Q : Prop) (PSN : StrongNegation P) (QSN : StrongNegation Q)
  : StrongNegation (P /\ Q) :=
{
  NOT := NOT P \/ NOT Q;
}.
Proof.
  destruct 1, 1.
    apply PSN; assumption.
    apply QSN; assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_impl
  (P Q : Prop) (QSN : StrongNegation Q)
  : StrongNegation (P -> Q) :=
{
  NOT := P /\ NOT Q;
}.
Proof.
  destruct 1. intro pq. apply QSN.
    assumption.
    apply pq. assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_forall
  (A : Type) (P : A -> Prop)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation (forall x : A, P x) :=
{
  NOT := exists x : A, NOT (P x);
}.
Proof.
  intros [x np] H.
  apply (PSN x).
    assumption.
    apply H.
Defined.

#[refine]
#[export]
Instance StrongNegation_exists
  (A : Type) (P : A -> Prop)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation (exists x : A, P x) :=
{
  NOT := forall x : A, NOT (P x);
}.
Proof.
  intros H [x np]. apply (PSN x).
    apply H.
    assumption.
Defined.

Compute NOT (forall n : nat, True).
Compute NOT (NOT (forall n : nat, True)).

End StrongNegation_Prop.

Module StrongNegation_Type.

Class StrongNegation (A : Type) : Type :=
{
  TNOT : Type;
  TNOT_spec : TNOT -> A -> False;
}.

Arguments TNOT A {StrongNegation}.

#[refine]
#[export]
Instance StrongNegation_Default
  (A : Type) : StrongNegation A | 999 :=
{
  TNOT := A -> False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_Pointed
  (A : Type) (inst : Pointed A)
  : StrongNegation A :=
{
  TNOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_Inhabited
  (A : Type) (inst : Inhabited A)
  : StrongNegation A :=
{
  TNOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_True :
  StrongNegation unit :=
{
  TNOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_False :
  StrongNegation False :=
{
  TNOT := True;
}.
Proof.
  trivial.
Defined.

#[refine]
#[export]
Instance StrongNegation_or
  (A B : Type) (PSN : StrongNegation A) (QSN : StrongNegation B)
  : StrongNegation (A + B) :=
{
  TNOT := TNOT A * TNOT B;
}.
Proof.
  destruct 1, 1.
    apply PSN; assumption.
    apply QSN; assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_and
  (A B : Type) (PSN : StrongNegation A) (QSN : StrongNegation B)
  : StrongNegation (A * B) :=
{
  TNOT := TNOT A + TNOT B;
}.
Proof.
  destruct 1, 1.
    apply PSN; assumption.
    apply QSN; assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_fun
  (A B : Type) (QSN : StrongNegation B)
  : StrongNegation (A -> B) :=
{
  TNOT := A * TNOT B;
}.
Proof.
  destruct 1. intro pq. apply QSN.
    assumption.
    apply pq. assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_pi
  (A : Type) (P : A -> Type)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation (forall x : A, P x) :=
{
  TNOT := {x : A & TNOT (P x)};
}.
Proof.
  intros [x np] H.
  apply (PSN x).
    assumption.
    apply H.
Defined.

#[refine]
#[export]
Instance StrongNegation_subset
  (A : Type) (P : A -> Prop)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation {x : A | P x} :=
{
  TNOT := forall x : A, TNOT (P x);
}.
Proof.
  intros H [x np]. apply (PSN x).
    apply H.
    assumption.
Defined.

#[refine]
#[export]
Instance StrongNegation_sigma
  (A : Type) (P : A -> Type)
  (PSN : forall x : A, StrongNegation (P x))
  : StrongNegation {x : A & P x} :=
{
  TNOT := forall x : A, TNOT (P x);
}.
Proof.
  intros H [x np]. apply (PSN x).
    apply H.
    assumption.
Defined.

Compute TNOT (forall n : nat, True).
Compute TNOT (TNOT (forall n : nat, True)).
Compute TNOT nat.

End StrongNegation_Type.

(** Klasy zbierające poszczególne implementacje izomorficznych typów są
    w ogólności potrzebne nawet jeżeli mamy homotopiczną teorię typów,
    bo przecież używanie izomorfizmów zrobionych ze ścieżek kosztuje. *)

Module Natural.

Class Natural (A : Type) : Type :=
{
  zero : A;
  succ : A -> A;
  rect :
    forall P : A -> Type,
      P zero -> (forall n : A, P n -> P (succ n)) ->
        forall n : A, P n;

  add : A -> A -> A;
  sub : A -> A -> A;

  mul : A -> A -> A;

  pred : A -> option A;
}.

#[export]
Instance Natural_nat : Natural nat :=
{
  zero := 0;
  succ := S;
  rect := nat_rect;

  add := plus;
  sub := minus;

  mul := mult;

  pred n := match n with | 0 => None | S n' => Some n' end
}.

End Natural.

Require Import ZArith.

Module Integral.

Class Integral (A : Type) : Type :=
{
  zero : A;
  succ : A -> A;
  pred : A -> A;

  add : A -> A -> A;
  sub : A -> A -> A;

  mul : A -> A -> A;
}.

#[export]
Instance Integral_Z : Integral Z :=
{
  zero := 0;
  succ := Z.succ;
  pred := Z.pred;

  add := Z.add;
  sub := Z.sub;

  mul := Z.mul;
}.

End Integral.

Require Import QArith.

Module Rational.

Class Rational (A : Type) : Type :=
{
  zero : A;

  add : A -> A -> A;
  sub : A -> A -> A;

  mul : A -> A -> A;
  div : A -> A -> option A;
}.

#[export]
Instance Rational_Q : Rational Q :=
{
  zero := 0;
  add := Qplus;
  sub := Qminus;

  mul := Qmult;
  div p q := if Qeq_bool q 0 then None else Some (Qdiv p q);
}.

End Rational.

Module Sequence.

Class Sequence (A L : Type) : Type :=
{
  nil : L;
  cons : A -> L -> L;

  rect :
    forall P : L -> Type,
      P nil -> (forall (h : A) (t : L), P t -> P (cons h t)) ->
        forall l : L, P l;

  snoc : L -> A -> L;

  app : L -> L -> L;
  rev : L -> L -> L;

  (* no map with this definition *)
}.

End Sequence.

(** TODO:
    - HoTTowa baza
    - hierarchia algebraiczna
    - typy skończone
*)

(** Trzeba mieć pod ręką zarówno trójstronne porównania, jak i te klasyczne (mniejszy lub równy).
    Dzięki eleganckiej koercji można tych bardziej ogólnych, czyli trójstronnych, używać też tam
    gdzie potrzeba nam [bool]a. Koercja w drugą stronę jest upierdliwsza, a raczej brak jej wcale. *)

Inductive Cmp : Type := Lt | Eq | Gt.

Definition Cmp2bool (c : Cmp) : bool :=
match c with
| Lt => true
| Eq => true
| Gt => false
end.

Coercion Cmp2bool : Cmp >-> bool.

(** Uwaga: daje nam to też koercję [(A -> A -> comparison) >-> (A -> A -> bool)], czyli elegancko. *)

(** Uwaga2: [Cmp] jest już w bibliotece standardowej i nazywa się [comparison]. *)

(** Inna fajna rzecz: generyczne Exists/Forall, w tym generyczne w sensie ilości argumentów (vararg). *)