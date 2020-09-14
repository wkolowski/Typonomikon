(** TODO: inne pomysły na bibliotekę standardową Coqa: klasy na liczby
    (coby nat, BinNat, N etc. miały taki sam interfejs; to samo dla
    liczb wymiernych, ale nie np. dla floatów, które są czymś innym)
    i listy, HoTTowa baza *)

Require Import Recdef Bool.

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
Notation "x == y" := (42) (at level 70).
End theory.

End Dec.

Import Dec.theory.
Print Dec.Class.

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

Module WeakEquality.

(** TODO: induktywne charakteryzacje równości dla typów induktywnych,
    koinduktywne dla typów koinduktywnych. *)
Class WeakEquality (A : Type) : Type :=
{
    weq : A -> A -> Prop;
    weq_spec :
      forall x y : A, x = y -> weq x y;
}.

Notation "x ~=~ y" := (weq x y) (at level 50).

#[refine]
Instance WeakEquality_Fun
  {A B : Type} : WeakEquality (A -> B) :=
{
    weq := fun f g => forall x : A, f x = g x;
}.
Proof.
  intros f g [] x. reflexivity.
Defined.

End WeakEquality.

Module StrongInequality.

(** TODO: induktywne charakteryzacje nierówności zarówno dla typów
    induktywnych jak i koinduktywnych. *)
Class StrongDisequality (A : Type) : Type :=
{
    sdeq : A -> A -> Prop;
    sdeq_spec :
      forall x y : A, sdeq x y -> x <> y;
}.

Notation "x =/= y" := (sdeq x y) (at level 50).

#[refine]
Instance StrongDisequality_Fun
  {A B : Type} : StrongDisequality (A -> B) :=
{
    sdeq := fun f g => exists x : A, f x <> g x;
}.
Proof.
  intros f g [x H] p. subst. contradiction.
Defined.

End StrongInequality.

(** TODO: klasy są słuszniejsze niż moduły *)

Module StrongNegation.

Class StrongNegation (A : Type) : Type :=
{
    NOT : Type;
    NOT_spec : NOT -> A -> False;
}.

Arguments NOT A {StrongNegation}.

#[refine]
Instance StrongNegation_Default
  (A : Type) : StrongNegation A | 999 :=
{
    NOT := A -> False;
}.
Proof.
  trivial.
Defined.

#[refine]
Instance StrongNegation_True :
  StrongNegation True :=
{
    NOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
Instance StrongNegation_False :
  StrongNegation False :=
{
    NOT := True;
}.
Proof.
  trivial.
Defined.

#[refine]
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

Class Inhabited (A : Type) : Prop :=
{
    inhabitant : A;
}.

#[refine]
Instance StrongNegation_Inhabited
  (A : Type) (inst : Inhabited A)
  : StrongNegation A :=
{
    NOT := False;
}.
Proof.
  trivial.
Defined.

Instance Inhabited_nat : Inhabited nat :=
{
    inhabitant := 0
}.

Compute NOT (forall n : nat, True).
Compute NOT (NOT (forall n : nat, True)).
Compute NOT nat.