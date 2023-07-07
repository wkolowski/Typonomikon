(** * H4: Translacja parametryczna [TODO] *)

(** * Domknięcie przechodnie (TODO) *)

From stdpp Require Import prelude well_founded.

Lemma wf_tc :
  forall {A : Type} (R : A -> A -> Prop),
    wf R -> wf (tc R).
Proof.
  unfold wf.
  intros A R Hwf a.
  specialize (Hwf a).
  induction Hwf as [a H IH].
  constructor.
  intros y Hy.
  induction Hy.
  - by apply IH.
  - by apply IHHy; [| | constructor].
Qed.

Module Fail.

Require Import Equality.

Inductive step : nat -> nat -> Prop :=
| step' : forall n : nat, step n (S n).

Lemma wf_step :
  wf step.
Proof.
  intro n.
  induction n as [| n' IH].
  - constructor. inversion 1.
  - constructor. inversion 1; subst. apply IH.
Defined.

Lemma wf_tc_step :
  wf (tc step).
Proof.
  apply wf_tc, wf_step.
Defined.

End Fail.

(** * Podtermy (TODO) *)

Require Import Relations Equality.
Require Import Relations.Relation_Operators.

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

(** * Translacja dobrze ufundowana (TODO) *)

Require Import List.
Import ListNotations.

Require Import Relations Equality.
Require Import Relations.Relation_Operators.

Class WfTranslation (A : Type) : Type :=
{
  smaller : A -> A -> Prop;
  well_founded_smaller : well_founded smaller;
}.

Arguments smaller {A _} _ _.
Arguments well_founded_smaller {A _}.

#[export, refine] Instance WfTranslation_False : WfTranslation False :=
{
  smaller := fun _ _ => False;
}.
Proof.
  now intros [].
Defined.

#[export, refine] Instance WfTranslation_unit : WfTranslation unit :=
{
  smaller := fun _ _ => False;
}.
Proof.
  constructor.
  now intros _ [].
Defined.

Inductive smaller_bool : bool -> bool -> Prop :=
| smaller_false_true : smaller_bool false true.

#[export, refine] Instance WfTranslation_bool : WfTranslation bool :=
{
  smaller := smaller_bool;
}.
Proof.
  constructor.
  intros ? [].
  constructor.
  now inversion 1.
Defined.

Inductive smaller_sum
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A + B -> A + B -> Prop :=
| smaller_sum_l :
    forall (a1 a2 : A), RA a1 a2 -> smaller_sum RA RB (inl a1) (inl a2)
| smaller_sum_r :
    forall (b1 b2 : B), RB b1 b2 -> smaller_sum RA RB (inr b1) (inr b2).

#[export, refine] Instance WfTranslation_sum
  {A B : Type} {WA : WfTranslation A} {WB : WfTranslation B} : WfTranslation (A + B) :=
{
  smaller := smaller_sum smaller smaller;
}.
Proof.
  intros [a | b].
  - pose proof (Acc_a := well_founded_smaller a).
    induction Acc_a as [a H IH].
    constructor.
    inversion 1; subst.
    now apply IH.
  - pose proof (Acc_b := well_founded_smaller b).
    induction Acc_b as [b H IH].
    constructor.
    inversion 1; subst.
    now apply IH.
Defined.

(** Tym razem lewy sumand mniejszy od prawego. *)
Inductive smaller_sum'
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A + B -> A + B -> Prop :=
| smaller_sum'_l :
    forall (a1 a2 : A), RA a1 a2 -> smaller_sum' RA RB (inl a1) (inl a2)
| smaller_sum'_r :
    forall (b1 b2 : B), RB b1 b2 -> smaller_sum' RA RB (inr b1) (inr b2)
| smaller_sum'_l_r :
    forall (a : A) (b : B), smaller_sum' RA RB (inl a) (inr b).

#[export, refine] Instance WfTranslation_sum'
  {A B : Type} {WA : WfTranslation A} {WB : WfTranslation B} : WfTranslation (A + B) :=
{
  smaller := smaller_sum' smaller smaller;
}.
Proof.
  assert (Acc_A : forall a : A, Acc (smaller_sum' smaller smaller) (inl a)).
  {
    intros a.
    pose proof (Acc_a := well_founded_smaller a).
    induction Acc_a as [a H IH].
    constructor.
    inversion 1; subst.
    now apply IH.
  }
  intros [a | b]; [now apply Acc_A |].
  pose proof (Acc_b := well_founded_smaller b).
  induction Acc_b as [b H IH].
  constructor.
  inversion 1; subst.
  - now apply IH.
  - now apply Acc_A.
Defined.

Inductive smaller_prod
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A * B -> A * B -> Prop :=
| smaller_prod_l :
    forall (a1 a2 : A) (b : B), RA a1 a2 -> smaller_prod RA RB (a1, b) (a2, b)
| smaller_prod_r :
    forall (a : A) (b1 b2 : B), RB b1 b2 -> smaller_prod RA RB (a, b1) (a, b2).

#[export, refine] Instance WfTranslation_prod
  {A B : Type} {WA : WfTranslation A} {WB : WfTranslation B} : WfTranslation (A * B) :=
{
  smaller := smaller_prod smaller smaller;
}.
Proof.
  intros [a b].
  pose proof (Acc_a := well_founded_smaller a).
  revert b.
  induction Acc_a as [a Ha IHa].
  intros b.
  constructor.
  intros [a' b']; inversion 1; subst.
  - now apply IHa.
  - clear Ha H H1.
    pose proof (Acc_b := well_founded_smaller b').
    revert a IHa; induction Acc_b as [b' Hb IHb].
    constructor.
    intros [a'' b'']; inversion 1; subst.
    + now apply IHa.
    + now apply IHb.
Defined.

(* TODO: inna translacja dobrze ufundowana dla produktu
Inductive smaller_prod'
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A * B -> A * B -> Prop :=
| smaller_prod'_l :
    forall (a1 a2 a3 : A) (b1 b3 : B),
      RA a1 a2 -> smaller_prod' RA RB (a2, b1) (a3, b3) ->
        smaller_prod' RA RB (a1, b1) (a3, b3)
| smaller_prod'_r :
    forall (a1 a3 : A) (b1 b2 b3 : B),
      RB b1 b2 -> smaller_prod' RA RB (a1, b2) (a3, b3) ->
        smaller_prod' RA RB (a1, b1) (a3, b3).

#[export, refine] Instance WfTranslation_prod'
  {A B : Type} {WA : WfTranslation A} {WB : WfTranslation B} : WfTranslation (A * B) :=
{
  smaller := smaller_prod' smaller smaller;
}.
Proof.
  intros [a b].
  pose proof (Acc_a := well_founded_smaller a).
  revert b.
  induction Acc_a as [a Ha IHa].
  intros b.
  constructor.
  intros [a' b']; inversion 1; subst.
  - now apply IHa.
  - clear Ha H H1.
    pose proof (Acc_b := well_founded_smaller b').
    revert a IHa; induction Acc_b as [b' Hb IHb].
    constructor.
    intros [a'' b'']; inversion 1; subst.
    + now apply IHa.
    + now apply IHb.
Defined.
*)

Inductive smaller_sigT
  {A : Type} {B : A -> Type}
  (RA : A -> A -> Prop) (RB : forall {a : A}, B a -> B a -> Prop)
  : sigT B -> sigT B -> Prop :=
| smaller_sigT_l :
    forall (a1 a2 : A) (b1 : B a1) (b2 : B a2),
      RA a1 a2 -> smaller_sigT RA (@RB) (existT a1 b1) (existT a2 b2)
| smaller_sigT_r :
    forall (a : A) (b1 b2 : B a),
      RB b1 b2 -> smaller_sigT RA (@RB) (existT a b1) (existT a b2).

#[export, refine] Instance WfTranslation_sigT
  {A : Type} {B : A -> Type}
  {WA : WfTranslation A} {WB : forall a : A, WfTranslation (B a)}
  : WfTranslation (sigT B) :=
{
  smaller := smaller_sigT smaller (fun a => @smaller _ (WB a));
}.
Proof.
  intros [a b].
  pose proof (Acc_a := well_founded_smaller a).
  revert b; induction Acc_a as [a Ha IHa]; intros b.
  constructor.
  intros [a' b']; inversion 1; subst.
  - now apply IHa.
  - clear Ha H H1.
    pose proof (Acc_b := well_founded_smaller b').
    revert IHa; induction Acc_b as [b' Hb IHb].
    constructor.
    intros [a'' b'']; inversion 1; subst.
    + now apply IHa.
    + apply IHb; only 3: easy.
Abort.


Module List.

Inductive DirectSubterm {A : Type} : list A -> list A -> Prop :=
| DS_tail : forall (h : A) (t : list A), DirectSubterm t (h :: t).

(** Domknięcie przechodnie relacji [DirectSubterm]. *)
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
    clear h r.
    specialize (wf h1).
    revert t HAcc; induction wf as [h1 H IH]; intros t HAcc.
    constructor.
    inversion 1; subst.
    + now apply IH.
    + clear IH. constructor. admit. 
  - intros h t [= -> ->] HAcc.
Restart.
  unfold well_founded.
  intros A R wf [| h t]; constructor; [now inversion 1 |].
  intros t' VDDS.
  remember (h :: t) as l.
  revert h t Heql.
  induction VDDS as [h1 h2 t'' r | h' t1 t2 VDDS].
  - intros h t [= -> ->].
    clear h r.
    specialize (wf h1).
    revert t; induction wf as [h1 H IH]; intros t.
    constructor; inversion 1; subst.
    + now apply IH.
    + clear IH H0.
      induction H3.
      *
Abort.

Inductive Hydra  {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| Hydra_hydra : forall (a : A) (l : list A), Forall (fun x => R x a) l -> Hydra R l [a]
| Hydra_head :
    forall {h1 h2 : A} (t : list A),
      R h1 h2 -> Hydra R (h1 :: t) (h2 :: t)
| Hydra_tail :
    forall (h : A) {t1 t2 : list A},
      Hydra R t1 t2 -> Hydra R (h :: t1) (h :: t2).

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

End BT.