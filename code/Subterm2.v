Inductive ITree (A : Type) : Type :=
| ILeaf | INode (a : A) (f : nat -> ITree A).

Arguments ILeaf {A}.
Arguments INode {A} _ _.

Inductive itree_child A : ITree A -> ITree A -> Prop :=
| ichild_at n a f : itree_child A (f n) (INode a f).

Lemma tree_child_wf A : well_founded (itree_child A).
Proof.
  intros t; induction t; constructor;
    inversion 1; subst; auto.
Qed.

Require Import Relations Equality.
Require Import Relations.Relation_Operators.

Definition Subterm {A : Type} : ITree A -> ITree A -> Prop :=
  clos_trans_n1 _ (@itree_child A).

Lemma wf_Subterm_aux :
  forall {A : Type} (t1 t2 : ITree A),
    Subterm t1 t2 -> Acc Subterm t2 -> Acc Subterm t1.
Proof.
  inversion 2.
  apply H1.
  assumption.
Defined.

Lemma wf_Subterm :
  forall A : Type,
    well_founded (@Subterm A).
Proof.
  intros A t.
  induction t as [| a f IH].
  - constructor.
    intros y H.
    dependent induction H; inversion H.
  - constructor.
    intros y H.
    inversion H; subst; clear H.
    + inversion H0; subst.
      apply IH.
    + inversion H0; subst.
      eapply wf_Subterm_aux.
      * apply H1.
      * apply IH.
Defined.