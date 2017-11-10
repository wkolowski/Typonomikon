Require Import List.
Import ListNotations.

Module Finite.

Class Finite (A : Type) : Type :=
{
    enumerate : list A;
    spec : forall x : A, In x enumerate
}.

Arguments Finite _.
Arguments enumerate _ [Finite].

Instance Finite_bool : Finite bool :=
{
    enumerate := [false; true]
}.
Proof.
  destruct x; compute; auto.
Defined.

Instance Finite_option {A : Type} (FA : Finite A) : Finite (option A) :=
{
    enumerate := None :: map (@Some A) (enumerate A)
}.
Proof.
  destruct x.
    right. apply in_map. apply spec.
    left. trivial.
Defined.

End Finite.

Module Enumerable.

Class Enumerable (A : Type) : Type :=
{
    size : A -> nat;
    enum : nat -> list A;
    enum_spec : forall (n : nat) (x : A), size x = n <-> In x (enum n)
}.

Arguments size [A Enumerable] _.
Arguments enum _ [Enumerable] _.

Instance Enumerable_bool : Enumerable bool :=
{
    size b := 1;
    enum n :=
    match n with
        | 0 => []
        | 1 => [false; true]
        | _ => []
    end
}.
Proof.
  Require Import Omega.
  destruct n as [| [| n']], x; compute; repeat split; auto; omega.
Defined.

Fixpoint bind {A B : Type} (x : list A) (f : A -> list B) : list B :=
match x with
    | [] => []
    | h :: t => f h ++ bind t f
end.

Fixpoint all_lists {A : Type} (E : Enumerable A) (n : nat)
  : list (list A) :=
match n with
    | 0 => [[]]
    | 1 => map (fun x => [x]) (enum A 1)
    | S n' =>
        bind (enum A 1) (fun h =>
        bind (all_lists E n') (fun t => [h :: t]))
end.

Compute all_lists (Enumerable_bool) 3.

Instance Enumerable_list {A : Type} (FA : Enumerable A)
  : Enumerable (list A) :=
{
    size := @length A;
    enum := all_lists FA
}.
Proof.
  induction n as [| n']; simpl.
    destruct x; simpl; split; auto.
      inversion 1.
      destruct 1; inversion H.
    destruct x; simpl; split; auto.
      inversion 1.
      destruct n'.
Abort.

End Enumerable.

Module Cardinality.

Require Import List.
Import ListNotations.

Inductive FinType (A : Type) : list A -> Prop :=
    | empty_fin : (A -> False) -> FinType A []
    | singl_fin : forall x : A, FinType A [x]
    | nonempty_fin : forall (h : A) (t : list A),
        FinType A t -> ~ In h t -> FinType A (h :: t).

Theorem unit_finite : FinType unit [tt].
Proof.
  constructor.
Qed.

Theorem unit_no_2 : forall l : list unit, 2 <= length l -> ~ FinType unit l.
Proof.
  induction l as [| h t].
    inversion 1.
    destruct t as [| h' t'].
      inversion 1. inversion H1.
      simpl. do 2 intro. do 2 apply le_S_n in H. inversion H0; subst.
        destruct h, h'. apply H4. constructor. trivial.
Qed.

Theorem bool_finite : FinType bool [true; false].
Proof.
  repeat constructor. inversion 1; inversion H0.
Qed.

Theorem unit_not_bool : ~ unit = bool.
Proof.
  intro. pose proof unit_no_2. unfold not in H0.
  rewrite H in H0. apply (H0 [true; false]).
    trivial.
    apply bool_finite.
Qed.

Require Import FinFun.

Theorem no_bij_peu_peb :
  ~ exists f : prod Empty_set unit -> prod Empty_set bool,
    Bijective f.
Proof.
  destruct 1.
Abort.

Theorem wut : ~ prod Empty_set unit = prod Empty_set bool.
Proof.
  intro.
  remember (prod Empty_set unit) as A.
  remember (prod Empty_set bool) as B.
  cut (forall P : Type -> Prop, P A <-> P B).
    intro.
Abort.

Goal ~ forall A B C : Type, prod A B = prod A C -> B = C.
Proof.
  intro. cut (unit = bool).
    apply unit_not_bool.
    specialize (H Empty_set unit bool).
Abort. (* TODO *)

End Cardinality.