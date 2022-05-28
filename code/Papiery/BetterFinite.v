(** Wzięte z pracy
    #<a class='link' href='https://doisinkidney.com/pdfs/masters-thesis.pdf'>
    Finiteness in Cubical Type Theory</a>#. *)

From Typonomikon Require Import D5.

Require Import Equality.

Inductive Elem {A : Type} (x : A) : list A -> Type :=
    | ElemZ : forall l : list A, Elem x (x :: l)
    | ElemS : forall (h : A) (t : list A), Elem x t -> Elem x (h :: t).

Arguments Elem  {A} _ _.
Arguments ElemZ {A} _ _.
Arguments ElemS {A} _ _ _.

Module RedundantlyFinite.

(** W [FinCuTT] mówią na to "Split Enumerability".
    Listy w różnej kolejności i nadprogramowe, dużo dowodów. *)
Class RedundantlyFinite (A : Type) : Type :=
{
    elems : list A;
    elems_all : forall x : A, Elem x elems;
}.

End RedundantlyFinite.

Module ExactlyFinite.

(** W [FinCuTT] mówią na to "Manifest Bishop Finite".
    Listy w różnej kolejności, implikuje rozstrzygalną równość.
    Inna nazwa: OrderedDecidablyFinite. *)
Class ExactlyFinite (A : Type) : Type :=
{
    elems : list A;
    elems_all : forall x : A, Elem x elems;
    elems_unique :
      forall (x : A) (e1 e2 : Elem x elems), e1 = e2;
}.

#[refine]
#[export]
Instance ExactlyFinite_False : ExactlyFinite False :=
{
    elems := [];
}.
Proof.
  all: destruct x.
Defined.

#[refine]
#[export]
Instance ExactlyFinite_unit : ExactlyFinite unit :=
{
    elems := [tt];
}.
Proof.
  destruct x. constructor.
  {
    intros.
    refine (
      match e1, e2 with
          | ElemZ _ _, ElemZ _ _ => _
          | ElemS _ _ _ _, ElemS _ _ _ _ => _
          | _, _ => _
      end).
      destruct x, l, l0; try red; trivial.
      destruct x, u, l, l0; try red; trivial; inversion e.
      destruct x, u, l, l0; try red; trivial; inversion e.
      destruct x, u, l, l0; try red; trivial; inversion e.
  }
Defined.

End ExactlyFinite.

Inductive Squash (A : Type) : Prop :=
    | squash : A -> Squash A.

Inductive Truncated (A : Type) : SProp :=
    | truncated : A -> Truncated A.

Arguments truncated {A} _.

Module MerelyExactlyFinite.

Import ExactlyFinite.

(** W [FinCutt] mówią na to "Cardinally Finite".
    Jedyny słuszny dowód, implikuje rozstrzygalną równość.
    Inna nazwa: DecidablyFinite. *)
Class MerelyExactlyFinite (A : Type) : Type :=
{
    mef : Truncated (ExactlyFinite A)
}.

Lemma test :
  forall {A : Type} (x y : MerelyExactlyFinite A),
    x = y.
Proof.
  destruct x, y.
  reflexivity.
Qed.

#[export]
Instance MerelyExactlyFinite_False : MerelyExactlyFinite False :=
{
    mef := truncated ExactlyFinite_False
}.

#[export]
Instance MerelyExactlyFinite_unit : MerelyExactlyFinite unit :=
{
    mef := truncated ExactlyFinite_unit
}.

End MerelyExactlyFinite.

Module MerelyRedundantlyFinite.

(** W [FinCuTT] mówią na to "Manifest Enumerability".
    Listy w różnej kolejności i nadprogramowe.
    Inna nazwa: OrderedFinite. *)
Class MerelyRedundantlyFinite (A : Type) : Type :=
{
    elems : list A;
    elems_all : forall x : A, Truncated (Elem x elems);
}.

Lemma test :
  forall {A : Type} (p1 p2 : MerelyRedundantlyFinite A),
    @elems _ p1 = @elems _ p2 -> p1 = p2.
Proof.
  intros A [] []. cbn.
  destruct 1.
  reflexivity.
Qed.

End MerelyRedundantlyFinite.

Module Finite.

Import MerelyRedundantlyFinite.

(** W [FinCuTT] mówią na to "Kuratowski Finite".
    Jest jedyny słuszny dowód i nie implikuje
    rozstrzygalnej równości. *)
Class Finite (A : Type) : Type :=
{
    finite : Truncated (@MerelyRedundantlyFinite A)
}.

End Finite.