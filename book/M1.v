(** * M1: Typy skończone [TODO] *)

(** * Pięć dziwnych definicji skończoności *)

(** Wzięte z pracy
    #<a class='link' href='https://doisinkidney.com/pdfs/masters-thesis.pdf'>
    Finiteness in Cubical Type Theory</a>#. *)

Require Import Equality.

From Typonomikon Require Import D5.

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

(** * Skończoność a rozstrzygalna równość (TODO) *)

Record Finite (A : Type) : Type :=
{
  enum : list A;
  NoDup_enum : NoDup enum;
  elem_enum : forall x : A, elem x enum;
}.

Lemma dec :
  forall {A : Type} (l : list A),
    NoDup l -> forall x y : A, elem x l -> elem y l -> x = y \/ x <> y.
Proof.
  induction 1 as [| h l' Hnot HND IH].
  - inversion 1.
  - intros x y.
    rewrite 2!elem_cons'.
    intros [-> | Hx] [-> | Hy].
    + left. reflexivity.
    + right. intros ->. contradiction.
    + right. intros ->. contradiction.
    + apply IH; assumption.
Qed.

Lemma dec_from_Finite :
  forall {A : Type} (F : Finite A),
    forall x y : A, x = y \/ x <> y.
Proof.
  intros A [enum ND Helem] x y.
  now apply (dec enum ND), Helem.
Qed.

Lemma dec' :
  forall {A : Type} (l : list A),
    NoDup l -> forall x y : A, In x l -> In y l -> {x = y} + {x <> y}.
Proof.
  induction l as [| h t].
  - inversion 2.
  - Fail intros ND x y [-> | Hx] [-> | Hy].
    (* ===> The command has indeed failed with message:
            Case analysis on sort Set is not allowed for inductive definition or. *)
Abort.

(** * Typy skończone (TODO) *)

Import ExactlyFinite.

#[refine]
#[export]
Instance ExactlyFinite_bool : ExactlyFinite bool :=
{|
  elems := [false; true];
|}.
Proof.
  destruct x; repeat constructor.
  intros. dependent destruction e1; dependent destruction e2.
    reflexivity.
    exfalso. inv e2. inv H0.
    exfalso. inv e1. inv H0.
    f_equal. dependent destruction e1; dependent destruction e2.
      reflexivity.
      exfalso. inv e2.
      exfalso. inv e1.
      f_equal. inv e1.
Defined.

Lemma Elem_map :
  forall {A B : Type} (f : A -> B) (x : A) (l : list A),
    Elem x l -> Elem (f x) (map f l).
Proof.
  induction l as [| h t]; cbn; intros.
    dependent destruction X.
    dependent destruction X; constructor. apply IHt. assumption.
Defined.

Lemma Elem_map_inv :
  forall {A B : Type} (f : A -> B) (b : B) (l : list A),
    Elem b (map f l) -> {a : A | f a = b}.
Proof.
  induction l as [| h t]; cbn; intros.
    inv X.
    inv X.
      exists h. reflexivity.
      apply IHt. assumption.
Qed.

Lemma Elem_map_Some :
  forall {A : Type} (a : A) (l : list A),
    Elem (Some a) (map Some l) -> Elem a l.
Proof.
  induction l as [| h t]; cbn; intros.
    dependent destruction X.
    dependent destruction X; constructor. apply IHt. assumption.
Defined.

Lemma Elem_map__Elem_map_Some :
  forall {A : Type} (a : A) (l : list A) (H : Elem a l),
    Elem_map_Some a l (Elem_map Some a l H) = H.
Proof.
  dependent induction H.
Admitted.

Lemma Elem_map_Some__Elem_map :
  forall {A : Type} (a : A) (l : list A) (H : Elem (Some a) (map Some l)),
    Elem_map Some a l (Elem_map_Some a l H) = H.
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    dependent destruction H.
Admitted.

#[refine]
#[export]
Instance Finite_option
  {A : Type} (FA : ExactlyFinite A) : ExactlyFinite (option A) :=
{|
  elems := None :: map Some (@elems _ FA);
|}.
Proof.
  all: destruct FA as [els H1 H2]; cbn.
    destruct x as [a |].
      constructor. apply Elem_map. apply H1.
      constructor.
    destruct x as [a |]; intros.
      2: {
        dependent destruction e1; dependent destruction e2.
          reflexivity.
          exfalso. apply Elem_map_inv in e2. destruct e2. congruence.
          exfalso. apply Elem_map_inv in e1. destruct e1. congruence.
          exfalso. apply Elem_map_inv in e2. destruct e2. congruence.
      }
      {
        dependent destruction e1; dependent destruction e2. f_equal.
        rewrite <- (Elem_map_Some__Elem_map _ _ e1), <- (Elem_map_Some__Elem_map _ _ e2).
        f_equal. apply H2.
      }
Defined.

Fixpoint sum (l : list nat) : nat :=
match l with
| [] => 0
| h :: t => h + sum t
end.

Lemma elem_sum :
  forall {n : nat} {l : list nat},
    Elem n l -> n <= sum l.
Proof.
  induction 1; cbn; lia.
Qed.

Lemma nat_not_Finite :
  ExactlyFinite nat -> False.
Proof.
  intros [els H1 H2].
  specialize (H1 (S (sum els))).
  apply elem_sum in H1.
  lia.
Qed.

Lemma join_elem_length :
  forall {A : Type} {l : list A} {ll : list (list A)},
    Elem l ll -> length l <= length (join ll).
Proof.
  induction 1; cbn;
  rewrite length_app;
  lia.
Qed.

Lemma list_not_Finite :
  forall A : Type,
    ExactlyFinite (list A) -> A -> False.
Proof.
  intros A [els H1 H2] x.
  specialize (H1 (x :: join els)).
  apply join_elem_length in H1; cbn in H1.
  lia.
Qed.