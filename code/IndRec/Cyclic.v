(** Zainspirowane przez:
    - https://gallais.github.io/blog/cyclic-list-purely.html
    - https://www.cs.gunma-u.ac.jp/~hamana/Papers/tfp06.pdf *)

Require Import Recdef.
Require Import List.
Import ListNotations.

Module HOAS_Like.

Unset Positivity Checking.
Inductive CList (A : Type) : Type :=
    | Nil
    | Cons (h : A) (t : CList A)
    | Rec  (h : A) (r : CList A -> CList A).
Set Positivity Checking.

Arguments Nil  {A}.
Arguments Cons {A} _ _.
Arguments Rec  {A} _.

Inductive CoListF (A R : Type) : Type :=
    | CoNilF
    | CoConsF (h : A) (t : R).

Arguments CoNilF  {A R}.
Arguments CoConsF {A R} _ _.

CoInductive CoList (A : Type) : Type :=
{
    uncons : CoListF A (CoList A);
}.

Arguments uncons {A} _.

Definition CoNil {A : Type} : CoList A :=
{|
    uncons := CoNilF;
|}.

Definition CoCons {A : Type} (h : A) (t : CoList A) : CoList A :=
{|
    uncons := CoConsF h t;
|}.

Function unwind {A : Type} (l : CList A) : CoList A :=
match l with
    | Nil => CoNil
    | Cons h t => CoCons h (unwind t)
    | Rec h r => CoCons h (unwind (r l))
end.

Inductive FiniteCList {A : Type} : CList A -> Type :=
    | FNil  : FiniteCList Nil
    | FCons :
        forall (h : A) (t : CList A),
          FiniteCList t -> FiniteCList (Cons h t).

Inductive FiniteCoList {A : Type} (l : CoList A) : Type :=
    | FiniteCoNil :
        uncons l = CoNilF -> FiniteCoList l
    | FiniteCoCons :
        forall (h : A) (t: CoList A),
          uncons l = CoConsF h t ->
            FiniteCoList t -> FiniteCoList l.

Lemma Finite_check :
  forall {A : Type} (l : CList A),
    FiniteCList l -> FiniteCoList (unwind l).
Proof.
  induction 1; cbn.
    constructor. cbn. reflexivity.
    econstructor 2.
      reflexivity.
      assumption.
Qed.

(** ** There is no guarantee on the way pointers are used (if at all). *)

(** Explanation: [FiniteCList] is a syntactic definition of finiteness.
    [FiniteCoList] is, on the other hand, a semantic definition of
    finiteness.

    It turns out that there are some (semantically) finite CLists which
    are not finite according to the syntactic definition. This is caused
    by the misuse of the [Rec] constructor to construct phony cycles. *)

Definition finite : CList nat :=
  Cons 1 (Rec 2 (fun _ => Nil)).

Lemma finite_not_FiniteCList :
  FiniteCList finite -> False.
Proof.
  inversion 1. subst.
  inversion H1.
Qed.

Lemma FiniteCoList_unwind_finite :
  FiniteCoList (unwind finite).
Proof.
  cbn.
  econstructor 2; try reflexivity.
  econstructor 2; try reflexivity.
  constructor; reflexivity.
Defined.

(** Nice observation: problems are caused by not using the name bound
    by [Rec] (or possibly also by using it more that once). So maybe
    this could be fixed by a type of linear functions? *)

(** ** Normal forms are not guaranteed *)

Definition ex1 : CList nat :=
  Cons 4 (Rec 2 (fun l => l)).

Definition ex2 : CList nat :=
  Rec 4 (fun _ => Rec 2 (fun l => l)).

(** Here we have two syntactically distinct [CList]s whose normal
    forms are different. *)

Inductive simF {A : Type} (l1 l2 : CoList A) (R : CoList A -> CoList A -> Type) : Type :=
    | CoNilsF (H1 : uncons l1 = CoNilF) (H2 : uncons l2 = CoNilF)
    | CoConssF :
        forall (h1 h2 : A) (t1 t2 : CoList A),
          uncons l1 = CoConsF h1 t1 -> uncons l2 = CoConsF h2 t2 ->
            h1 = h2 -> R t1 t2 -> simF l1 l2 R.

CoInductive sim {A : Type} (l1 l2 : CoList A) : Type :=
{
    sim' : simF l1 l2 sim;
}.

Lemma sim_refl :
  forall {A : Type} (l : CoList A),
    sim l l.
Proof.
  cofix CH.
  destruct l as [[| h t]].
    do 2 constructor; cbn; reflexivity.
    constructor. econstructor 2; try reflexivity. apply CH.
Qed.

Lemma syntactically_different :
  ex1 <> ex2.
Proof.
  inversion 1.
Qed.

Lemma semantically_equal :
  sim (unwind ex1) (unwind ex2).
Proof.
  cofix CH.
  constructor. econstructor 2.
    unfold ex1. rewrite unwind_equation. reflexivity.
    unfold ex2. rewrite unwind_equation. reflexivity.
    reflexivity.
    apply sim_refl.
Qed.

Fixpoint take (n : nat) {A : Type} (l : CList A) : list A :=
match n with
    | 0    => []
    | S n' =>
        match l with
            | Nil => []
            | Cons h t => h :: take n' t
            | Rec h r => h :: take n' (r l)
        end
end.

Fixpoint app {A : Type} (l1 l2 : CList A) : CList A :=
match l1 with
    | Nil => l2
    | Cons h t => Cons h (app t l2)
    | Rec h r => Rec h (fun l => (app (r l) l2))
end.

(** It's probably impossible to define [map]. *)
Unset Guard Checking.
Fixpoint mapS (l : CList nat) : CList nat :=
match l with
    | Nil => Nil
    | Cons h t => Cons (S h) (mapS t)
    | Rec h r => Rec (S h) (fun l => r (mapS l))
end.
Set Guard Checking.

(** If we try, mapping successor over a recursive list results in computing powers of two... *)
Compute take 10 (mapS (mapS ex1)).
(* ===> [6; 4; 6; 10; 18; 34; 66; 130; 258; 514] : list nat *)

End HOAS_Like.

Module Phantom.

Inductive Closed : SProp := closed.

Unset Positivity Checking.
Inductive CList (A : Type) : SProp -> Type :=
    | Nil  : CList A Closed
    | Cons : forall (B : SProp) (h : A) (t : CList A B), CList A B
    | Rec  : forall (h : A) (r : forall {B : SProp}, CList A B -> CList A B), CList A Closed.
Set Positivity Checking.



End Phantom.
