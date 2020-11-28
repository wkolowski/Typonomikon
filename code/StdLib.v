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

Module ThisMustWork.

Class Dec (P : Prop) : Type :=
{
    dec : bool;
    dec_spec : reflect P dec;
}.

Arguments dec      _ {Dec}.
Arguments dec_spec _ {Dec}.

#[refine]
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

End ThisMustWork.

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

Class Pointed (A : Type) : Type :=
{
    point : A;
}.

Class Inhabited (A : Type) : Prop :=
{
    inhabitant : A;
}.

Instance Inhabited_Pointed
  (A : Type) (inst : Pointed A)
  : Inhabited A :=
{
    inhabitant := point;
}.

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
Instance StrongNegation_Default
  (A : Type) : StrongNegation A | 999 :=
{
    NOT := A -> False;
}.
Proof.
  trivial.
Defined.

#[refine]
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
Instance StrongNegation_Default
  (A : Prop) : StrongNegation A | 999 :=
{
    NOT := A -> False;
}.
Proof.
  trivial.
Defined.

#[refine]
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
    NOT := NOT P /\ NOT Q;
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
    NOT := NOT P \/ NOT Q;
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
    NOT := P /\ NOT Q;
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
    NOT := exists x : A, NOT (P x);
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
Instance StrongNegation_Default
  (A : Type) : StrongNegation A | 999 :=
{
    TNOT := A -> False;
}.
Proof.
  trivial.
Defined.

#[refine]
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
Instance StrongNegation_True :
  StrongNegation unit :=
{
    TNOT := False;
}.
Proof.
  trivial.
Defined.

#[refine]
Instance StrongNegation_False :
  StrongNegation False :=
{
    TNOT := True;
}.
Proof.
  trivial.
Defined.

#[refine]
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

Require Import ZArith.

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

Module Rational.

Require Import QArith.

Class Rational (A : Type) : Type :=
{
    zero : A;

    add : A -> A -> A;
    sub : A -> A -> A;

    mul : A -> A -> A;
    div : A -> A -> option A;
}.

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
    - porządne rozwiązanie rozstrzygalności
    - hierarchia algebraiczna
    - typy skończone


*)

(** Trzeba mieć pod ręką zarówno trójstronne porównania, jak i te klasyczne (mniejszy lub równy).
    Dzięki eleganckiej koercji można tych bardziej ogólnych, czyli trójstronnych, używać też tam
    gdzie potrzeba nam boola. Koercja w drugą stronę jest upierdliwsza, a raczej brak jej wcale. *)

Inductive Cmp : Type := Lt | Eq | Gt.

Definition Cmp2bool (c : Cmp) : bool :=
match c with
    | Lt => true
    | Eq => true
    | Gt => false
end.

Coercion Cmp2bool : Cmp >-> bool.

(** Uwaga: daje nam to też koercję (A -> A -> comparison) >-> (A -> A -> bool), czyli elegancko. *)

(** Uwaga2: [Cmp] jest już w bibliotece standardowej i nazywa się [comparison]. *)

(** Inna fajna rzecz: generyczne Exists/Forall, w tym generyczne w sensie ilości argumentów (vararg). *)