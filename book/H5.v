(** * H5: Liczby porządkowe [TODO] *)

Require Import Arith Lia.

From Typonomikon Require Import B3c.

(** * Relacje dobrze ufundowane, ekstensjonalne i dobre porządki *)

(** ** Relacje słabo ekstensjonalne *)

Class WeaklyExtensional {A : Type} (R : rel A) : Prop :=
{
  weakly_extensional : forall x y : A, (forall t : A, R t x <-> R t y) -> x = y;
}.

Lemma WeaklyExtensional_lt :
  WeaklyExtensional lt.
(* begin hide *)
Proof.
  split; intros x y H.
  cut (~ x < y /\ ~ y < x); [lia |].
  rewrite <- (H x), (H y).
  lia.
Qed.
(* end hide *)

Lemma WeaklyExtensional_le :
  WeaklyExtensional le.
(* begin hide *)
Proof.
  split; intros x y H.
  cut (x <= y /\ y <= x); [lia |].
  rewrite <- (H x), (H y).
  lia.
Qed.
(* end hide *)

Lemma WeaklyExtensional_gt :
  WeaklyExtensional gt.
(* begin hide *)
Proof.
  split; intros x y H.
  cut (~ x < y /\ ~ y < x); [lia |].
  rewrite <- (H x), (H y).
  lia.
Qed.
(* end hide *)

Lemma WeaklyExtensional_ge :
  WeaklyExtensional ge.
(* begin hide *)
Proof.
  split; intros x y H.
  cut (x <= y /\ y <= x); [lia |].
  rewrite <- (H x), (H y).
  lia.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_RTrue :
  exists A : Type,
    ~ WeaklyExtensional (@RTrue A A).
(* begin hide *)
Proof.
  exists bool.
  intros [WE]; unfold RTrue in *.
  assert (bool -> True <-> True) by intuition.
  specialize (WE true false H).
  congruence.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_RFalse :
  exists A : Type,
    ~ WeaklyExtensional (@RFalse A A).
(* begin hide *)
Proof.
  exists bool.
  intros [WE]; unfold RFalse in *.
  assert (bool -> False <-> False) by intuition.
  specialize (WE true false H).
  congruence.
Qed.
(* end hide *)

Lemma WeaklyExtensional_Rid :
  forall A : Type,
    WeaklyExtensional (@eq A).
(* begin hide *)
Proof.
  split; compute.
  intros x y H.
  destruct (H x) as [Heq _].
  apply Heq. reflexivity.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_Rinv :
  exists (A : Type) (R : rel A),
    WeaklyExtensional R /\ ~ WeaklyExtensional (Rinv R).
(* begin hide *)
Proof.
  exists
    comparison,
    (fun x y =>
      x = Eq /\ y = Lt
        \/
      x = Eq /\ y = Gt).
  split; [split |].
(*   - intros x y H. destruct x, y; try reflexivity.
    + specialize (H true). intuition.
    + specialize (H true). intuition. *)
  - intros x y H. specialize (H Eq).
Abort.
(* end hide *)

Lemma not_WeaklyExtensional_Rcomp :
  exists (A : Type) (R S : rel A),
    WeaklyExtensional R /\ WeaklyExtensional S /\ ~ WeaklyExtensional (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt.
  repeat split.
  1-2: apply WeaklyExtensional_lt.
  intros [WE]; unfold Rcomp in WE.
  cut (0 = 1); [congruence |]. (* TODO: opisać taktykę [enough] *)
  apply WE. split.
  - intros (b & H1 & H2). lia.
  - intros (b & H1 & H2). lia.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_Rnot :
  exists (A : Type) (R : rel A),
    WeaklyExtensional R /\ ~ WeaklyExtensional (Rnot R).
(* begin hide *)
Proof.
  exists
    bool,
    (fun x y => x = false \/ y = true).
  repeat split.
  - intros x y H.
    specialize (H true) as Ht.
    specialize (H false) as Hf.
    destruct x, y; intuition.
  - intros [WE]; unfold Rnot in WE.
    specialize (WE true false).
Abort.
(* end hide *)

Lemma not_WeaklyExtensional_Ror :
  exists (A : Type) (R S : rel A),
    WeaklyExtensional R /\ WeaklyExtensional S /\ ~ WeaklyExtensional (Ror R S).
(* begin hide *)
Proof.
  exists nat, lt, ge.
  repeat split.
  - apply WeaklyExtensional_lt.
  - apply WeaklyExtensional_ge.
  - intros [WE]; unfold Ror in WE.
    cut (1 = 2); [lia |].
    apply WE. lia.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_Rand :
  exists (A : Type) (R S : rel A),
    WeaklyExtensional R /\ WeaklyExtensional S /\ ~ WeaklyExtensional (Rand R S).
(* begin hide *)
Proof.
  exists nat, lt, ge.
  repeat split.
  - apply WeaklyExtensional_lt.
  - apply WeaklyExtensional_ge.
  - intros [WE]; unfold Rand in WE.
    cut (1 = 2); [lia |].
    apply WE. lia.
Qed.
(* end hide *)

(** ** Relacje dobrze ufundowane *)

Class WellFounded {A : Type} (R : rel A) : Prop :=
  well_founded : forall x : A, Acc R x.

CoInductive Inaccessible {A : Type} (R : rel A) (x : A) : Prop :=
{
  inaccessible : exists y : A, R y x /\ Inaccessible R y
}.

Class IllFounded {A : Type} (R : rel A) : Prop :=
  ill_founded : exists x : A, Inaccessible R x.

Lemma not_IllFounded_WellFounded :
  forall {A : Type} (R : rel A),
    WellFounded R -> IllFounded R -> False.
(* begin hide *)
Proof.
  unfold WellFounded, IllFounded.
  intros A R WF [x IA]; revert IA.
  specialize (WF x).
  induction WF as [x H IH].
  intros [(y & r & IA')].
  apply (IH y); assumption.
Qed.
(* end hide *)

#[export]
Instance WellFounded_Empty :
  forall R : rel Empty_set, WellFounded R.
(* begin hide *)
Proof.
  intros R [].
Qed.
(* end hide *)

Lemma not_IllFounded_Empty :
  forall R : rel Empty_set, ~ IllFounded R.
(* begin hide *)
Proof.
  intros R [[]].
Qed.
(* end hide *)

Lemma IllFounded_RTrue_inhabited :
  forall A : Type, A -> IllFounded (@RTrue A A).
(* begin hide *)
Proof.
  unfold IllFounded, RTrue.
  intros A x. exists x.
  cofix CH.
  constructor. exists x.
  split; [trivial | assumption].
Qed.
(* end hide *)

Lemma not_WellFounded_RTrue_inhabited :
  forall A : Type, A -> ~ WellFounded (@RTrue A A).
(* begin hide *)
Proof.
  intros A x WF.
  eapply not_IllFounded_WellFounded; [eassumption |].
  apply IllFounded_RTrue_inhabited; assumption.
Qed.
(* end hide *)

#[export]
Instance WellFounded_RFalse :
  forall A : Type, WellFounded (@RFalse A A).
(* begin hide *)
Proof.
  unfold WellFounded, RFalse.
  intros A x.
  constructor.
  intros y [].
Qed.
(* end hide *)

Lemma not_IllFounded_RFalse :
  forall A : Type, ~ IllFounded (@RFalse A A).
(* begin hide *)
Proof.
  unfold IllFounded, RFalse.
  intros A [x [(y & [] & IA)]].
Qed.
(* end hide *)

#[export]
Instance IllFounded_eq :
  forall A : Type, A -> IllFounded (@eq A).
(* begin hide *)
Proof.
  unfold IllFounded.
  intros A x; exists x.
  unfold WellFounded.
  cofix CH.
  constructor; exists x.
  split; [reflexivity | assumption].
Qed.
(* end hide *)

Lemma not_WellFounded_eq :
  forall A : Type, A -> ~ WellFounded (@eq A).
(* begin hide *)
Proof.
  intros A x WF.
  eapply not_IllFounded_WellFounded; [eassumption |].
  apply IllFounded_eq; assumption.
Qed.
(* end hide *)

#[export]
Instance WellFounded_lt :
  WellFounded lt.
(* begin hide *)
Proof.
  unfold WellFounded.
  induction x as [| n'].
  + constructor. inversion 1.
  + constructor. inversion 1; subst.
    * assumption.
    * apply IHn'. lia.
Qed.
(* end hide *)

#[export]
Instance IllFounded_le :
  IllFounded le.
(* begin hide *)
Proof.
  unfold IllFounded.
  cut (forall n : nat, Inaccessible le n).
  - intros. exists 0. apply H.
  - intros n.
    cofix CH.
    constructor. exists n. split; [lia | assumption].
Qed.
(* end hide *)

#[export]
Instance IllFounded_ge :
  IllFounded ge.
(* begin hide *)
Proof.
  unfold IllFounded.
  cut (forall n : nat, Inaccessible ge n).
  - intros. exists 0. apply H.
  - intros n.
    cofix CH.
    constructor. exists n. split; [lia | assumption].
Qed.
(* end hide *)

#[export]
Instance IllFounded_gt :
  IllFounded gt.
(* begin hide *)
Proof.
  unfold IllFounded.
  cut (forall n : nat, Inaccessible gt n).
  - intros. exists 0. apply H.
  - cofix CH.
    constructor; exists (S n).
    split; [lia | apply CH].
Qed.
(* end hide *)

Lemma not_WellFounded_Rinv :
  exists (A : Type) (R : rel A),
    WellFounded R /\ ~ WellFounded (Rinv R).
(* begin hide *)
Proof.
  exists nat, lt.
  split; [apply lt_wf |].
  intros WF.
  eapply not_IllFounded_WellFounded; [eassumption |].
  unfold Rinv. fold gt.
  apply IllFounded_gt.
Qed.
(* end hide *)

Lemma not_IllFounded_Rinv :
  exists (A : Type) (R : rel A),
    IllFounded R /\ ~ IllFounded (Rinv R).
(* begin hide *)
Proof.
  exists nat, gt.
  split; [apply IllFounded_gt | intros IlF].
  eapply not_IllFounded_WellFounded; [| eassumption].
  unfold Rinv, gt.
  apply WellFounded_lt.
Qed.
(* end hide *)

#[export]
Instance WellFounded_Rcomp :
  forall (A : Type) (R S : rel A),
    WellFounded R -> WellFounded S -> WellFounded (Rcomp R S).
(* begin hide *)
Proof.
  unfold WellFounded, Rcomp.
  intros A R S WFR WFS x.
  specialize (WFR x); revert WFS.
  induction WFR as [x H IH]; intros.
  constructor; intros y (b & r & s).
  apply IH.
Abort.
(* end hide *)

Lemma not_WellFounded_Rcomp :
  exists (A : Type) (R S : rel A),
    WellFounded R /\ WellFounded S /\ IllFounded (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt.
  unfold WellFounded.
  split; [| split]; [apply WellFounded_lt | apply WellFounded_lt |].
  - cut (forall n : nat, Inaccessible (Rcomp lt lt) (1 + n)); unfold Rcomp.
Abort.
(* end hide *)

Lemma not_IllFounded_Rcomp :
  exists (A : Type) (R S : rel A),
    IllFounded R /\ IllFounded S /\ ~ IllFounded (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, le, ge.
  split; [| split]; unfold IllFounded.
Abort.
(* end hide *)

Lemma not_WellFounded_Rnot :
  exists (A : Type) (R : rel A),
    WellFounded R /\ ~ WellFounded (Rnot R).
(* begin hide *)
Proof.
  exists nat, lt.
  split; [apply WellFounded_lt | intros WF].
  eapply not_IllFounded_WellFounded; [eassumption |].
  unfold IllFounded, Rnot.
  cut (forall n : nat, Inaccessible (fun a b => ~ a < b) n).
  - intros IlF. exists 0. apply IlF.
  - cofix CH.
    constructor. exists (S n). split; [lia |]. apply CH.
Qed.
(* end hide *)

Lemma not_IllFounded_Rnot :
  exists (A : Type) (R : rel A),
    IllFounded R /\ ~ IllFounded (Rnot R).
(* begin hide *)
Proof.
  exists nat, ge.
  split; [apply IllFounded_ge |].
  intros IlF.
  eapply not_IllFounded_WellFounded; [| eassumption].
  unfold WellFounded, Rnot, ge.
  induction x as [| n'].
  + constructor. lia.
  + constructor. intros y H.
    assert (Hlt : y < S n') by lia; clear H. inversion Hlt; subst.
    * assumption.
    * apply IHn'. lia.
Qed.
(* end hide *)

Lemma not_WellFounded_Ror :
  exists (A : Type) (R S : rel A),
    WellFounded R /\ WellFounded S /\ ~ WellFounded (Ror R S).
(* begin hide *)
Proof.
  exists
    (nat * nat)%type,
    (fun x y => fst x < fst y),
    (fun x y => snd x < snd y).
  split; [| split]; unfold WellFounded, Ror.
  - admit.
  - admit.
  - intros WF. specialize (WF (1, 1)). inversion WF. cbn in *.
    induction WF; subst; cbn in *.
    specialize (H (0, 0) ltac:(cbn; lia)). inversion H.
Abort.
(* end hide *)

#[export]
Instance WellFounded_Rand :
  forall (A : Type) (R S : rel A),
    WellFounded R -> WellFounded S -> WellFounded (Rand R S).
(* begin hide *)
Proof.
  unfold WellFounded, Rand.
  intros A R S WFR WFS x.
  specialize (WFR x).
  induction WFR as [x Hlt IH].
  constructor; intros y [r s].
  apply IH; assumption.
Qed.
(* end hide *)

Lemma not_IllFounded_Ror :
  exists (A : Type) (R S : rel A),
    IllFounded R /\ IllFounded S /\ ~ IllFounded (Ror R S).
(* begin hide *)
Proof.
  exists
    (nat * nat)%type,
    (fun x y => fst x < fst y),
    (fun x y => snd x < snd y).
  split; [| split]; unfold IllFounded, Ror.
  - admit.
  - admit.
  - intros WF.
Abort.
(* end hide *)

#[export]
Instance IllFounded_Rand :
  forall (A : Type) (R S : rel A),
    IllFounded R -> IllFounded S -> IllFounded (Rand R S).
(* begin hide *)
Proof.
  unfold IllFounded, Rand.
Abort.
(* end hide *)

#[export] Instance Antireflexive_WellFounded
  {A : Type} {R : rel A} (WF : WellFounded R) : Antireflexive R.
(* begin hide *)
Proof.
  split; intros x rxx.
  specialize (WF x).
  induction WF as [x _ IH].
  now apply (IH x).
Qed.
(* end hide *)

(** ** Dobre porządki *)

(* begin hide *)
Class WellPreorder {A : Type} (R : rel A) : Prop :=
{
  WellPreorder_StrictPreorder :> StrictPreorder R;
  WellPreorder_WellFounded :> WellFounded R;
  WellPreorder_WeaklyExtensional :> WeaklyExtensional R;
}.

Class WellPartialOrder {A : Type} (R : rel A) : Prop :=
{
  WellPartialOrder_StrictPartialOrder :> StrictPartialOrder R;
  WellPartialOrder_WellFounded :> WellFounded R;
  WellPartialOrder_WeaklyExtensional :> WeaklyExtensional R;
}.

Class WellQuasiorder {A : Type} (R : rel A) : Prop :=
{
  WellQuasiorder_Quasiorder :> Quasiorder R;
  WellQuasiorder_WellFounded :> WellFounded R;
  WellQuasiorder_WeaklyExtensional :> WeaklyExtensional R;
}.
(* Class WellOrder {A : Type} (R : rel A) : Prop :=
{
  WellOrder_PartialOrder :> StrictTotalOrder R;
  WellOrder_WellFounded :> WellFounded R;
  WellOrder_WeaklyExtensional :> WeaklyExtensional R;
}. *)
(* end hide *)

Class WellOrder {A : Type} (R : rel A) : Prop :=
{
  WellOrder_Transitive :> Transitive R;
  WellOrder_WellFounded :> WellFounded R;
  WellOrder_WeaklyExtensional :> WeaklyExtensional R;
}.

#[export]
Instance Antisymmetric_WellOrder :
  forall {A : Type} (R : rel A),
    WellOrder R -> Antisymmetric R.
(* begin hide *)
Proof.
  intros A R [[HT] HWF [HWE]]; split; intros x y rxy ryx.
  apply (Antireflexive_WellFounded HWF) with x.
  now apply HT with y.
Qed.
(* end hide *)

Lemma WellOrder_not_Total :
  forall {A : Type} (R : rel A) (x : A),
    WellOrder R -> ~ Total R.
(* begin hide *)
Proof.
  intros A R x [_ HWF _] [HT].
  apply (Antireflexive_WellFounded HWF) with x.
  now destruct (HT x x).
Qed.
(* end hide *)