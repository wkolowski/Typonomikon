Inductive ITree (A : Type) : Type :=
| INode : A -> (nat -> ITree A) -> ITree A.

Arguments INode {A} _ _.

Inductive DirectSubterm {A : Type} : ITree A -> ITree A -> Prop :=
| DS : forall (a : A) (f : nat -> ITree A) (n : nat), DirectSubterm (f n) (INode a f).

Lemma Irreflexive_DirectSubterm :
  forall {A : Type} (t : ITree A),
    ~ DirectSubterm t t.
Proof.
  induction t as [a f IH].
  inversion 1 as [a' f' n H1 H2].
  rewrite H1 in H2; inversion H2; subst; clear H2.
  rewrite <- H1 in H.
  eapply IH, H.
Qed.

Lemma WellFounded_DirectSubterm :
  forall {A : Type},
    well_founded (@DirectSubterm A).
Proof.
  intros A t.
  induction t as [a f IH].
  constructor.
  inversion 1; subst.
  apply IH.
Qed.

Lemma Irreflexive_DirectSubterm' :
  forall {A : Type} (t1 t2 : ITree A),
    DirectSubterm t1 t2 -> t1 <> t2.
Proof.
  intros A t1 t2 H <-; revert H.
  induction t1.
  inversion 1.
  rewrite H2 in H3; inversion H3; subst.
  rewrite <- H2 in H0.
  eapply H, H0.
Qed.

Require Import Relations.
Require Import Relations.Relation_Operators.

Definition Subterm {A : Type} : ITree A -> ITree A -> Prop :=
  clos_trans_1n _ DirectSubterm.

Lemma Irreflexive_Subterm :
  forall {A : Type} (t1 t2 : ITree A),
    Subterm t1 t2 -> t1 <> t2.
Proof.
  induction 1 as [ |]; intros ->.
  - eapply Irreflexive_DirectSubterm, H.
  -
Abort.

Require Import Program.Wf.

Lemma oh_god :
  forall A : Type, ITree A -> False.
Proof.
  induction 1.
  apply H.
  exact 0.
Qed.

Lemma Wf_Subterm :
  forall A : Type,
    well_founded (@Subterm A).
Proof.
  intros A t.
  exfalso.
  eapply oh_god.
  eassumption.
Qed.

Require Import Setoid.

Lemma Irreflexive_Subterm :
  forall {A : Type} (t : ITree A),
    ~ Subterm t t.
Proof.
  induction t as [a f IH].
  remember (INode a f) as t1.
  remember (INode a f) as t2.
  rewrite Heqt2 in Heqt1.
  rewrite Heqt1 at 2. rewrite <- Heqt2.
  rewrite <- Heqt2 in Heqt1.
  clear Heqt2.
  induction 1.
  - subst. eapply Irreflexive_DirectSubterm, H.
Abort.
(*   inversion 1 as [t HDS Heq | t1 t2 HDS HS Heq].
  - eapply Irreflexive_DirectSubterm', HDS.
  - subst.
  rewrite H1 in H2; inversion H2; subst; clear H2.
  rewrite <- H1 in H.
  eapply IH, H.
Qed. *)

Inductive R : nat -> nat -> Prop :=
| R' : forall n : nat, R n (S n).

Require Import Equality.

Lemma wf_Rstar :
  well_founded (clos_trans_1n _ R).
Proof.
  intros n.
  induction n as [| n'].
  - constructor. intros y H. exfalso.
    dependent induction H.
    + inversion H.
    + apply IHclos_trans_1n. reflexivity.
  -
 constructor. intros y H.
    dependent induction H.
    + inversion H. assumption.
    +
Abort.