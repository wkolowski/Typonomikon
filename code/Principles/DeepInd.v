Require Import List.
Import ListNotations.

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
| ForallT_nil  : ForallT P []
| ForallT_cons :
    forall (h : A) (t : list A),
      P h -> ForallT P t -> ForallT P (h :: t).

Fixpoint ForallT' {A : Type} (P : A -> Type) (l : list A) : Type :=
match l with
| [] => unit
| h :: t => P h * ForallT' P t
end.

Fixpoint list_ind_deep
  {A : Type} (P : list A -> Type) (Q : A -> Type)
  (nil : P [])
  (cons : forall (h : A) (t : list A),
            Q h -> P t -> P (h :: t))
  (l : list A) (l' : ForallT' Q l) {struct l} : P l.
Proof.
  destruct l as [| h t].
    exact nil.
    destruct l'. apply cons.
      exact q.
      apply (list_ind_deep _ P Q); assumption.
Defined.

Fixpoint list_ind_deep'
  {A : Type} (P : list A -> Type) (Q : A -> Type)
  (nil : P [])
  (cons : forall (h : A) (t : list A),
            Q h -> P t -> P (h :: t))
  (l : list A) (l' : ForallT Q l) {struct l'} : P l.
Proof.
  destruct l' as [| h t Qh FQh].
    exact nil.
    apply cons.
      exact Qh.
      apply (list_ind_deep' _ P Q); assumption.
Defined.

Inductive RoseTree (A : Type) : Type :=
| E : RoseTree A
| N : A -> list (RoseTree A) -> RoseTree A.

Arguments E {A}.
Arguments N {A} _ _.

Scheme RoseTree_ind' := Induction for RoseTree Sort Prop.

Inductive RoseTree' {A : Type} (P : A -> Type) : RoseTree A -> Type :=
| E' : RoseTree' P E
| N' : forall (x : A) (ts : list (RoseTree A)),
         P x -> ForallT (RoseTree' P) ts -> RoseTree' P (N x ts).

Arguments E' {A P}.
Arguments N' {A P x ts} _ _.

Fixpoint RoseTree_ind_deep'
  {A : Type} (P : RoseTree A -> Type) (Q : A -> Type)
  (e : P E)
  (n : forall (x : A) (ts : list (RoseTree A)),
         Q x -> ForallT P ts -> P (N x ts))
  {t : RoseTree A} (t' : RoseTree' Q t) {struct t'} : P t.
Proof.
  destruct t' as [| x l Qx FQt].
    exact e.
    apply n.
      exact Qx.
      induction FQt as [| hFQt tFQt]; constructor.
        apply (RoseTree_ind_deep' _ P Q); assumption.
        apply IHFQt.
Defined.