Require Import List.
Import ListNotations.

Require Import Relations Equality.
Require Import Relations.Relation_Operators.

Module List.

Inductive DirectSubterm {A : Type} : list A -> list A -> Prop :=
| DS_tail : forall (h : A) (t : list A), DirectSubterm t (h :: t).

Inductive Subterm {A : Type} : list A -> list A -> Prop :=
| S_step  : forall {l1 l2 : list A}, DirectSubterm l1 l2 -> Subterm l1 l2
| S_trans : forall {l1 l2 l3 : list A}, DirectSubterm l1 l2 -> Subterm l2 l3 -> Subterm l1 l3.

Lemma wf_DirectSubterm :
  forall {A : Type},
    well_founded (@DirectSubterm A).
Proof.
  unfold well_founded.
  now induction a; constructor; inversion 1.
Qed.

Inductive DeepDirectSubterm {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| DDS_head : forall (h1 h2 : A) (t : list A), R h1 h2 -> DeepDirectSubterm R (h1 :: t) (h2 :: t)
| DDS_tail : forall (h : A) (t : list A), DeepDirectSubterm R t (h :: t).

Inductive DeepSubterm {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| DS_step  :
    forall {l1 l2 : list A},
      DeepDirectSubterm R l1 l2 -> DeepSubterm R l1 l2
| DS_trans :
    forall {l1 l2 l3 : list A},
      DeepDirectSubterm R l1 l2 -> DeepSubterm R l2 l3 -> DeepSubterm R l1 l3.

Lemma wf_DeepDirectSubterm :
  forall {A : Type} {R : A -> A -> Prop},
    well_founded R -> well_founded (DeepDirectSubterm R).
Proof.
  unfold well_founded.
  intros A R wf.
  induction a as [| h t]; constructor; [now inversion 1 |].
  intros t' HDS; inversion HDS; subst; clear HDS; [| easy].
  specialize (wf h1).
  clear H1.
  induction wf.
  constructor.
  intros t'' HDS; inversion HDS; subst; clear HDS; [| easy].
  now apply H0.
Qed.

Lemma DS_DDS :
  forall {A : Type} (l1 l2 : list A),
    DirectSubterm l1 l2 <-> DeepDirectSubterm (fun _ _ => False) l1 l2.
Proof.
  split.
  - now intros []; constructor.
  - now intros []; [| constructor].
Qed.

Lemma DDS_DS :
  forall {A : Type} (R : A -> A -> Prop) (l1 l2 : list A),
    DeepDirectSubterm R l1 l2
      <->
    DirectSubterm l1 l2
      \/
    exists (h1 h2 : A) (t : list A),
      (l1 = h1 :: t)%list /\
      (l2 = h2 :: t)%list /\
      R h1 h2.
Proof.
  split.
  - intros [].
    + now right; eauto 7.
    + now left.
  - intros [| (h1 & h2 & t & -> & -> & r)].
    + now inversion H; right.
    + now left.
Qed.

Inductive VeryDeepDirectSubterm {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| VDDS_head :
    forall {h1 h2 : A} (t : list A),
      R h1 h2 -> VeryDeepDirectSubterm R (h1 :: t) (h2 :: t)
| VDDS_tail :
    forall (h : A) {t1 t2 : list A},
      VeryDeepDirectSubterm R t1 t2 -> VeryDeepDirectSubterm R (h :: t1) (h :: t2).

Lemma wf_VeryDeepDirectSubterm :
  forall {A : Type} {R : A -> A -> Prop},
    well_founded R -> well_founded (VeryDeepDirectSubterm R).
Proof.
  unfold well_founded.
  intros A R wf.
  induction a as [| h t]; constructor; [now inversion 1 |].
  intros t' VDDS.
  remember (h :: t) as l.
  revert h t Heql IHt.
  induction VDDS as [h1 h2 t'' r | h' t1 t2 VDDS].
  - intros h t [= -> ->] HAcc.
    admit.
  - intros h t [= -> ->] HAcc.
Abort.

End List.

Module BT.

Inductive BT (A : Type) : Type :=
| E : BT A
| N : A -> BT A -> BT A -> BT A.

Arguments E {A}.
Arguments N {A} _ _ _.

Inductive DeepDirectSubterm {A : Type} (R : A -> A -> Prop) : BT A -> BT A -> Prop :=
| DDS_v :
    forall {v1 v2 : A} (l r : BT A),
      R v1 v2 -> DeepDirectSubterm R (N v1 l r) (N v2 l r)
| DDS_l :
    forall (v : A) (l r : BT A),
      DeepDirectSubterm R l (N v l r)
| DDS_r :
    forall (v : A) (l r : BT A),
      DeepDirectSubterm R r (N v l r).