(** * H3b: Mało ciekawe relacje [TODO] *)

Require Import FunctionalExtensionality Nat Arith Lia.

Require Import List.
Import ListNotations.

From Typonomikon Require Export H3a.

(** * Relacje prawie równoważności (TODO) *)

(** ** Częściowe relacje równoważności *)

Class PER {A : Type} (R : rel A) : Prop :=
{
  PER_Symmetric :> Symmetric R;
  PER_Transitive :> Transitive R;
}.

#[export]
Instance PER_Empty :
  forall R : rel Empty_set, PER R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance PER_RTrue :
  forall A : Type, PER (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance PER_RFalse :
  forall A : Type, PER (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance PER_eq :
  forall A : Type, PER (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance PER_Rinv :
  forall (A : Type) (R : rel A),
    PER R -> PER (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_PER_Rcomp :
  exists (A : Type) (R S : rel A),
    PER R /\ PER S /\ ~ PER (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => f x = f y),
    (fun x y => g x = g y).
  split; [| split].
  - rel.
  - rel.
  - unfold Rcomp; intros [[HS] [HT]].
    specialize (HS 0 1).
    assert (exists b : nat, f 0 = f b /\ g b = g 1).
    {
      exists 2. split.
      - rewrite f_0, f_2. reflexivity.
      - rewrite g_1, g_2. reflexivity.
    }
    specialize (HS H).
    destruct HS as (b & H1 & H2).
Abort.
(* end hide *)

Lemma not_PER_Rnot :
  exists (A : Type) (R : rel A),
    PER R /\ ~ PER (Rnot R).
(* begin hide *)
Proof.
  exists bool, (@eq bool).
  split.
  - apply PER_eq.
  - unfold Rnot; intros [[HS] [HT]].
    specialize (HT true false true).
    destruct HT; congruence.
Qed.
(* end hide *)

Lemma not_PER_Ror :
  exists (A : Type) (R S : rel A),
    PER R /\ PER S /\ ~ PER (Ror R S).
(* begin hide *)
Proof.
  exists
    (list nat),
    (fun l1 l2 => length l1 = length l2),
    (fun l1 l2 => head l1 = head l2).
  split; [| split].
  - rel.
  - rel.
  - intros [S [T]].
    specialize (T [1] [2] [2; 3]).
    compute in T. intuition congruence.
Qed.
(* end hide *)

#[export]
Instance PER_Rand :
  forall (A : Type) (R S : rel A),
    PER R -> PER S -> PER (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** ** Relacje tolerancji *)

Class Tolerance {A : Type} (R : rel A) : Prop :=
{
  Tolerance_Reflexive :> Reflexive R;
  Tolerance_Symmetric :> Symmetric R;
}.

#[export]
Instance Tolerance_Empty :
  forall R : rel Empty_set, Tolerance R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Tolerance_RTrue :
  forall A : Type, Tolerance (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Tolerance_RFalse_inhabited :
  forall A : Type, A -> ~ Tolerance (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Tolerance_eq :
  forall A : Type, Tolerance (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Tolerance_Rinv :
  forall (A : Type) (R : rel A),
    Tolerance R -> Tolerance (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Tolerance_Rcomp :
  exists (A : Type) (R S : rel A),
    Tolerance R /\ Tolerance S /\ ~ Tolerance (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y =>
      x = y
        \/
      x = 0 /\ y = 1
        \/
      x = 1 /\ y = 0),
    (fun x y =>
      x = y
        \/
      x = 2 /\ y = 3
        \/
      x = 3 /\ y = 2).
  split; [| split].
  - rel.
  - rel.
  - unfold Rcomp. intros [[HR] [HS]].
    destruct (HS 2 3).
    + exists 2. lia.
    + decompose [and or] H; subst; try lia.
Abort.
(* end hide *)

Lemma not_Tolerance_Rnot :
  exists (A : Type) (R : rel A),
    Tolerance R /\ ~ Tolerance (Rnot R).
(* begin hide *)
Proof.
  exists bool, (@eq bool).
  split.
  - apply Tolerance_eq.
  - unfold Rnot; intros [[HS] [HT]].
    destruct (HS true). reflexivity.
Qed.
(* end hide *)

#[export]
Instance Tolerance_Ror :
  forall {A : Type} (R S : rel A),
    Tolerance R -> Tolerance S -> Tolerance (Ror R S).
(* begin hide *)
Proof.
  intros A R S [[RR] [RS]] [[SR] [SS]].
  split; split; unfold Ror.
  - intros x. left; apply RR; assumption.
  - intros x y [rxy | sxy].
    + left; apply RS; assumption.
    + right; apply SS; assumption.
Qed.
(* end hide *)

#[export]
Instance Tolerance_Rand :
  forall (A : Type) (R S : rel A),
    Tolerance R -> Tolerance S -> Tolerance (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** * Słabe wersje relacji totalnych i trychotomicznych (TODO) *)

(** ** Relacje słabo totalne *)

Class WeaklyTotal {A : Type} (R : rel A) : Prop :=
{
  weakly_total : forall x y : A, ~ R x y -> R y x
}.

#[export]
Instance WeaklyTotal_RTrue :
  forall A : Type,
    WeaklyTotal (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma WeaklyTotal_Empty :
  forall R : rel Empty_set, WeaklyTotal R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTotal_RFalse_inhabited :
  forall A : Type,
    A -> ~ WeaklyTotal (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma WeaklyTotal_eq_Empty :
  WeaklyTotal (@eq Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma WeaklyTotal_eq_unit :
  WeaklyTotal (@eq unit).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTotal_eq_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ WeaklyTotal (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTotal_Rinv :
  forall (A : Type) (R : rel A),
    WeaklyTotal R -> WeaklyTotal (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTotal_Rcomp :
  forall (A : Type) (R S : rel A),
    WeaklyTotal R -> WeaklyTotal S -> WeaklyTotal (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS].
  unfold Rcomp; split; intros x y H.
Abort.
(* end hide *)

Lemma not_WeaklyTotal_Rnot :
  exists (A : Type) (R : rel A),
    WeaklyTotal R /\ ~ WeaklyTotal (Rnot R).
(* begin hide *)
Proof.
  exists unit, RTrue.
  split; rel.
Qed.
(* end hide *)

#[export]
Instance WeaklyTotal_Ror :
  forall (A : Type) (R S : rel A),
    WeaklyTotal R -> WeaklyTotal S -> WeaklyTotal (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTotal_Rand :
  exists (A : Type) (R S : rel A),
    WeaklyTotal R /\ WeaklyTotal S /\ ~ WeaklyTotal (Rand R S).
(* begin hide *)
Proof.
  exists bool, (fun x y => x = true \/ y = false), (fun x y => x = false \/ y = true).
  split; [| split].
  - rel. destruct y; rel.
  - rel. destruct y; rel.
  - intros [H]; unfold Rand in H.
    specialize (H true false).
    intuition.
Qed.
(* end hide *)

Lemma not_Antireflexive_WeaklyTotal_inhabited :
  forall (A : Type) (R : rel A) (x : A),
    WeaklyTotal R -> ~ Antireflexive R.
(* begin hide *)
Proof.
  intros A R x [HWT] [HA]. rel.
Qed.
(* end hide *)

(** ** Relacje słabo trychotomiczne *)

Class WeaklyTrichotomous {A : Type} (R : rel A) : Prop :=
{
  weakly_trichotomous : forall x y : A, x <> y -> R x y \/ R y x
}.

#[export]
Instance WeaklyTrichotomous_Total :
  forall (A : Type) (R : rel A),
    Total R -> WeaklyTrichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_Empty :
  forall R : rel Empty_set, WeaklyTrichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_unit :
  forall R : rel unit, WeaklyTrichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_RTrue :
  forall A : Type,
    WeaklyTrichotomous (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTrichotomous_RFalse_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ WeaklyTrichotomous (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_Rinv :
  forall (A : Type) (R : rel A),
    WeaklyTrichotomous R -> WeaklyTrichotomous (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTrichotomous_Rcomp :
  exists (A : Type) (R S : rel A),
    WeaklyTrichotomous R /\ WeaklyTrichotomous S /\ ~ WeaklyTrichotomous (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt. split; [| split].
  1-2: split; lia.
  destruct 1 as [H]; unfold Rcomp in H.
  destruct (H 0 1 ltac:(lia)) as [[b Hb] | [b Hb]]; lia.
Qed.
(* end hide *)

Lemma not_WeaklyTrichotomous_Rnot :
  exists (A : Type) (R : rel A),
    WeaklyTrichotomous R /\ ~ WeaklyTrichotomous (Rnot R).
(* begin hide *)
Proof.
  exists bool, RTrue.
  split.
  - rel.
  - intros [H]. specialize (H true false ltac:(congruence)). rel.
Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_Ror :
  forall (A : Type) (R S : rel A),
    WeaklyTrichotomous R -> WeaklyTrichotomous S -> WeaklyTrichotomous (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTrichotomous_Rand :
  exists (A : Type) (R S : rel A),
    WeaklyTrichotomous R /\ WeaklyTrichotomous S /\ ~ WeaklyTrichotomous (Rand R S).
(* begin hide *)
Proof.
  exists bool, (fun x _ => x = true), (fun x _ => x = false).
  split; [| split].
  - rel. destruct x, y; intuition.
  - rel. destruct x, y; intuition.
  - intros [H].
    specialize (H true false ltac:(congruence)).
    rel.
Qed.
(* end hide *)

(** * Wariacje nt relacji zwrotnych (TODO) *)

(** ** Relacje kozwrotne *)

Class CoReflexive {A : Type} (R : rel A) : Prop :=
{
  coreflexive : forall x y : A, R x y -> x = y;
}.

#[export]
Instance CoReflexive_Empty :
  forall R : rel Empty_set, CoReflexive R.
(* begin hide *)
Proof.
  split; intros [].
Qed.
(* end hide *)

#[export]
Instance CoReflexive_RFalse :
  forall A : Type, CoReflexive (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ [].
Qed.
(* end hide *)

#[export]
Instance CoReflexive_eq :
  forall A : Type, CoReflexive (@eq A).
(* begin hide *)
Proof.
  split; trivial.
Qed.
(* end hide *)

Lemma CoReflexive_subrelation_eq :
  forall {A : Type} {R : rel A},
    CoReflexive R -> subrelation R (@eq A).
(* begin hide *)
Proof.
  intros A R [H] x y. apply H.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Rinv :
  forall (A : Type) (R : rel A),
    CoReflexive R -> CoReflexive (Rinv R).
(* begin hide *)
Proof.
  intros A R [HR].
  split; unfold Rinv.
  intros x y r.
  symmetry.
  apply HR.
  assumption.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    CoReflexive R -> CoReflexive S -> CoReflexive (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split.
  intros x y (z & r & s).
  rewrite (HR _ _ r), (HS _ _ s).
  reflexivity.
Qed.
(* end hide *)

Lemma not_CoReflexive_Rnot :
  exists (A : Type) (R : rel A),
    CoReflexive R /\ ~ CoReflexive (Rnot R).
(* begin hide *)
Proof.
  exists bool, (fun b1 b2 => b1 = true /\ b2 = true).
  split; [rel |].
  unfold Rnot; intros [WR].
  specialize (WR true false); intuition.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Ror :
  forall (A : Type) (R S : rel A),
    CoReflexive R -> CoReflexive S -> CoReflexive (Ror R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split.
  intros x y [r | s].
  - apply HR; assumption.
  - apply HS; assumption.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Rand_l :
  forall (A : Type) (R S : rel A),
    CoReflexive R -> CoReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HR]; split.
  intros x y [r s].
  apply HR; assumption.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Rand_r :
  forall (A : Type) (R S : rel A),
    CoReflexive S -> CoReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HS]; split.
  intros x y [r s].
  apply HS; assumption.
Qed.
(* end hide *)

(** ** Relacje kwazizwrotne *)

(** *** Relacje lewostronnie kwazizwrotne *)

Class LeftQuasiReflexive {A : Type} (R : rel A) : Prop :=
  left_quasireflexive : forall x y : A, R x y -> R x x.

#[export]
Instance LeftQuasiReflexive_Empty :
  forall R : rel Empty_set, LeftQuasiReflexive R.
(* begin hide *)
Proof.
  intros R [].
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_eq {A : Type} : LeftQuasiReflexive (@eq A).
(* begin hide *)
Proof.
  compute. trivial.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_RFalse :
  forall A : Type, LeftQuasiReflexive (@RFalse A A).
(* begin hide *)
Proof.
  compute. trivial.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_RTrue :
  forall A : Type, LeftQuasiReflexive (@RTrue A A).
(* begin hide *)
Proof.
  compute. trivial.
Qed.
(* end hide *)

Lemma not_LeftQuasiReflexive_Rcomp :
  exists (A : Type) (R S : rel A),
    LeftQuasiReflexive R /\ LeftQuasiReflexive S /\ ~ LeftQuasiReflexive (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 0 /\ m = 0),
    (fun n m =>
      n = 1 /\ m = 2
        \/
      n = 1 /\ m = 1).
  unfold LeftQuasiReflexive, Rcomp.
  split; [| split].
  - intuition.
  - intuition.
  - intro H. destruct (H 0 1) as (b & H1 & H2).
    + exists 1. intuition.
    + intuition congruence.
Qed.
(* end hide *)

Lemma not_LeftQuasiReflexive_Rinv :
  exists (A : Type) (R : rel A),
    LeftQuasiReflexive R /\ ~ LeftQuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive, Rinv.
  exists nat, (fun n m => Nat.even n = true).
  split.
  - firstorder.
  - intro H. specialize (H 1 0 eq_refl). cbn in H. congruence.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_Rand :
  forall (A : Type) (R S : rel A),
    LeftQuasiReflexive R -> LeftQuasiReflexive S -> LeftQuasiReflexive (Rand R S).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros A R S HR HS x y [r s]; red.
  split.
  - eapply HR; eassumption.
  - eapply HS; eassumption.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_Ror :
  forall (A : Type) (R S : rel A),
    LeftQuasiReflexive R -> LeftQuasiReflexive S -> LeftQuasiReflexive (Ror R S).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros A R S HR HS x y [r | s]; red.
  - left. eapply HR; eassumption.
  - right. eapply HS; eassumption.
Qed.
(* end hide *)

(** *** Relacje prawostronnie kwazizwrotne *)

Class RightQuasiReflexive {A : Type} (R : rel A) : Prop :=
  right_quasireflexive : forall x y : A, R x y -> R y y.

Lemma RightQuasiReflexive_spec :
  forall {A : Type} (R : rel A),
    RightQuasiReflexive R <-> LeftQuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive, RightQuasiReflexive, Rinv.
  split.
  - intros H x y r. eapply H; eassumption.
  - intros H x y r. eapply H; eassumption.
Qed.
(* end hide *)

(** *** Relacje kwazizwrotne *)

Class QuasiReflexive {A : Type} (R : rel A) : Prop :=
{
  QR_LeftQuasiReflexive :> LeftQuasiReflexive R;
  QR_RightQuasiReflexive :> RightQuasiReflexive R;
}.

#[export]
Instance LeftQuasiReflexive_Rinv :
  forall {A : Type} (R : rel A),
    RightQuasiReflexive R -> LeftQuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  compute. eauto.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Empty :
  forall R : rel Empty_set, QuasiReflexive R.
(* begin hide *)
Proof.
  split.
  - typeclasses eauto.
  - rewrite RightQuasiReflexive_spec. typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_eq {A : Type} : QuasiReflexive (@eq A).
(* begin hide *)
Proof.
  split.
  - typeclasses eauto.
  - red. trivial.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_RFalse :
  forall A : Type, QuasiReflexive (@RFalse A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_RTrue :
  forall A : Type, QuasiReflexive (@RTrue A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [RL RR] [SL SR].
  split; unfold LeftQuasiReflexive, RightQuasiReflexive, Rcomp in *.
Abort.
(* end hide *)

#[export]
Instance QuasiReflexive_Rinv :
  forall (A : Type) (R : rel A),
    QuasiReflexive R -> QuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  intros A R [HL HR].
  split; firstorder.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Rand :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HRL HRR] [HSL HSR].
  split; firstorder.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Ror :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Ror R S).
(* begin hide *)
Proof.
  intros A R S [HRL HRR] [HSL HSR].
  split; firstorder.
Qed.
(* end hide *)

(** * Relacje powiązane z relacjami przechodnimi (TODO) *)

(** ** Relacje antyprzechodnie *)

Class Antitransitive {A : Type} (R : rel A) : Prop :=
  antitransitive : forall x y z : A, R x y -> R y z -> ~ R x z.

#[export]
Instance Antitransitive_Empty :
  forall R : rel Empty_set, Antitransitive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antitransitive_RTrue_inhabited :
  forall A : Type, A -> ~ Antitransitive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Antitransitive_RFalse :
  forall A : Type, Antitransitive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antitransitive_eq_inhabited :
  forall A : Type, A -> ~ Antitransitive (@eq A).
(* begin hide *)
Proof.
  unfold Antitransitive.
  intros A a H.
  specialize (H a a a eq_refl eq_refl).
  contradiction.
Qed.
(* end hide *)

#[export]
Instance Antitransitive_successor :
  Antitransitive (fun x y => y = S x).
(* begin hide *)
Proof.
  unfold Antitransitive. lia.
Qed.
(* end hide *)

#[export]
Instance Antitransitive_Rinv :
  forall (A : Type) (R : rel A),
    Antitransitive R -> Antitransitive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antitransitive_Rcomp :
  exists (A : Type) (R S : rel A),
    Antitransitive R /\ Antitransitive S /\ ~ Antitransitive (Rcomp R S).
(* begin hide *)
Proof.
  unfold Antitransitive, Rcomp.
  exists nat, (fun x y => y = S x), (fun x y => y = S x).
  repeat split; [lia | lia |].
  intros H.
  apply (H 1 3 5).
  - exists 2. lia.
  - exists 4. lia.
  - exists 2.
Abort.
(* end hide *)

Lemma not_Antitransitive_Rnot :
  exists (A : Type) (R : rel A),
    Antitransitive R /\ ~ Antitransitive (Rnot R).
(* begin hide *)
Proof.
  unfold Antitransitive, Rnot.
  exists nat, (fun x y => y = S x).
  split; [lia |].
  intros H.
  apply (H 0 0 0); lia.
Qed.
(* end hide *)

Lemma not_Antitransitive_Ror :
  exists (A : Type) (R S : rel A),
    Antitransitive R /\ Antitransitive S /\ ~ Antitransitive (Ror R S).
(* begin hide *)
Proof.
  exists nat, (fun x y => y = S (S x)), (fun x y => x = S y).
  unfold Antitransitive, Ror.
  repeat split; [lia | lia |].
  intros AT.
Abort.
(* end hide *)

Lemma not_Antitransitive_Rand :
  exists (A : Type) (R S : rel A),
    Antitransitive R /\ Antitransitive S /\ ~ Antitransitive (Rand R S).
(* begin hide *)
Proof.
  unfold Antitransitive, Rand.
  exists nat, lt, lt.
Abort.
(* end hide *)

(** ** Relacje kwaziprzechodnie *)

Definition SymmetricPart {A : Type} (R : rel A) : rel A :=
  fun x y : A => R x y /\ R y x.

Definition AsymmetricPart {A : Type} (R : rel A) : rel A :=
  fun x y : A => R x y /\ ~ R y x.

Class Quasitransitive {A : Type} (R : rel A) : Prop :=
  quasitransitive :> Transitive (AsymmetricPart R).

#[export]
Instance Symmetric_SymmetricPart :
  forall {A : Type} (R : rel A),
    Symmetric (SymmetricPart R).
(* begin hide *)
Proof.
  intros A R. split; unfold SymmetricPart.
  intros x y [rxy ryx]. split; assumption.
Qed.
(* end hide *)

#[export]
Instance Quasitransitive_Symmetric :
  forall {A : Type} (R : rel A),
    Symmetric R -> Quasitransitive R.
(* begin hide *)
Proof.
  intros A R [HS]; split; unfold AsymmetricPart.
  intros x y z [rxy nryx] [ryz nrzy].
  contradict nryx. apply HS. assumption.
Qed.
(* end hide *)

#[export]
Instance Quasitransitive_Transitive :
  forall {A : Type} (R : rel A),
    Transitive R -> Quasitransitive R.
(* begin hide *)
Proof.
  intros A R [HT]; split; unfold AsymmetricPart.
  intros x y z [rxy nryx] [ryz nrzy]. split.
  - apply HT with y; assumption.
  - intro rzx. contradict nrzy. apply HT with x; assumption.
Qed.
(* end hide *)

Lemma Quasitransitive_char :
  forall {A : Type} (R : rel A),
    Quasitransitive R <-> (R <--> Ror (SymmetricPart R) (AsymmetricPart R)).
(* begin hide *)
Proof.
  assert (LEM : forall P : Prop, P \/ ~ P) by admit.
  split.
  - intros [QT]; unfold Ror, SymmetricPart, AsymmetricPart in *; split.
    + intros x y r. destruct (LEM (R y x)); auto.
    + intros x y [[rxy ryx] | [rxy nryx]]; assumption.
  - intros [HRL _].
    split; unfold same_hrel, subrelation, Ror, SymmetricPart, AsymmetricPart in *.
    intros x y z [rxy nryx] [ryz nrzy].
    destruct (LEM (R x z)).
    + split; [assumption |].
Abort.
(* end hide *)

#[export]
Instance Quasitransitive_Empty :
  forall R : rel Empty_set, Quasitransitive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Quasitransitive_RTrue :
  forall A : Type, Quasitransitive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Quasitransitive_RFalse :
  forall A : Type, Quasitransitive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Quasitransitive_eq :
  forall A : Type, Quasitransitive (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Quasitransitive_Rinv :
  forall (A : Type) (R : rel A),
    Quasitransitive R -> Quasitransitive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Quasitransitive_Rcomp :
  exists (A : Type) (R S : rel A),
    Quasitransitive R /\ Quasitransitive S /\ ~ Quasitransitive (Rcomp R S).
(* begin hide *)
Proof.
  unfold Quasitransitive, Rcomp.
  exists nat, eq, (fun x y => x <> y).
  split; [| split]; [rel | rel |].
  intros [HT]; unfold AsymmetricPart in HT.
  specialize (HT 0 1 1).
Abort.
(* end hide *)

#[export]
Instance Quasitransitive_Rnot :
  forall {A : Type} (R : rel A),
    Quasitransitive R -> Quasitransitive (Rnot R).
(* begin hide *)
Proof.
  assert (DNE : forall P : Prop, ~ ~ P -> P) by admit.
  unfold Quasitransitive, Rnot, AsymmetricPart.
  intros A R [HT]; split; intros x y z [nrxy nnryx] [nryz nnrzy].
  apply DNE in nnryx, nnrzy. firstorder.
Admitted.
(* end hide *)

#[export]
Instance Quasitransitive_Rnot_conv :
  forall {A : Type} (R : rel A),
    Quasitransitive (Rnot R) -> Quasitransitive R.
(* begin hide *)
Proof.
  assert (DNE : forall P : Prop, ~ ~ P -> P) by admit.
  unfold Quasitransitive, Rnot, AsymmetricPart.
  intros A R [HT]; split; intros x y z [nrxy nnryx] [nryz nnrzy].
  destruct (HT z y x).
  - auto.
  - auto.
  - apply DNE in H0; auto.
Admitted.
(* end hide *)

#[export]
Instance Quasitransitive_Ror :
  forall (A : Type) (R S : rel A),
    Quasitransitive R -> Quasitransitive S -> Quasitransitive (Ror R S).
(* begin hide *)
Proof.

Abort.
(* end hide *)

#[export]
Instance Quasitransitive_Rand :
  forall {A : Type} (R S : rel A),
    Quasitransitive R -> Quasitransitive S -> Quasitransitive (Rand R S).
(* begin hide *)
Proof.
  unfold Quasitransitive, Rand.
  intros A R S [HR] [HS]; unfold AsymmetricPart in *.
  split; intros x y z [[rxy sxy] n1] [[ryz syz] n2]; split.
  - split.
    + apply HR with y. split; auto. intro ryx.
      assert (H : S x z /\ ~ S z x).
      {
        apply HS with y; auto. split; [assumption |].
Abort.
(* end hide *)

(** * Wariacje nt relacji przechodnich (TODO) *)

(** ** Relacje cyrkularne *)

Class Circular {A : Type} (R : rel A) : Prop :=
{
  circular : forall x y z : A, R x y -> R y z -> R z x;
}.

#[export]
Instance Circular_Empty :
  forall R : rel Empty_set, Circular R.
(* begin hide *)
Proof.
  split; intros [].
Qed.
(* end hide *)

#[export]
Instance Circular_RTrue :
  forall A : Type, Circular (@RTrue A A).
(* begin hide *)
Proof.
  split; compute. trivial.
Qed.
(* end hide *)

#[export]
Instance Circular_RFalse :
  forall A : Type, Circular (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ _ [].
Qed.
(* end hide *)

#[export]
Instance Circular_eq {A : Type} : Circular (@eq A).
(* begin hide *)
Proof.
  split; congruence.
Qed.
(* end hide *)

#[export]
Instance Circular_Rcomp :
  forall (A : Type) (R S : rel A),
    Circular R -> Circular S -> Circular (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split; red.
  intros x y z (w1 & r1 & s1) (w2 & r2 & s2).
Abort.
(* end hide *)

#[export]
Instance Circular_Rinv :
  forall (A : Type) (R : rel A),
    Circular R -> Circular (Rinv R).
(* begin hide *)
Proof.
  intros A R [HR].
  split; unfold Rinv.
  intros x y z r1 r2.
  specialize (HR _ _ _ r2 r1).
  assumption.
Qed.
(* end hide *)

Lemma Circular_Rcomp :
  exists (A : Type) (R S : rel A),
    Circular R /\ Circular S /\ ~ Circular (Rcomp R S).
(* begin hide *)
Proof.
  exists nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 2
        \/
      n = 2 /\ m = 0),
    (fun n m =>
      n = 2 /\ m = 3
        \/
      n = 3 /\ m = 4
        \/
      n = 4 /\ m = 2).
  unfold Rcomp.
  split; [| split].
  - split; lia.
  - split; lia.
  - destruct 1 as [H].
(*     Axiom x y z : nat. *)
    specialize (H 0 2 0). destruct H.
    + exists 2. intuition.
Admitted.
(* end hide *)

Lemma Circular_Ror :
  exists (A : Type) (R S : rel A),
    Circular R /\ Circular S /\ ~ Circular (Ror R S).
(* begin hide *)
Proof.
  exists nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 2
        \/
      n = 2 /\ m = 0),
    (fun n m =>
      n = 2 /\ m = 3
        \/
      n = 3 /\ m = 4
        \/
      n = 4 /\ m = 2).
  split; [| split].
  - split; lia.
  - split; lia.
  - unfold Ror; destruct 1 as [H].
    specialize (H 1 2 3). specialize (H ltac:(lia) ltac:(lia)).
    intuition; try lia.
Qed.
(* end hide *)

#[export]
Instance Circular_Rand :
  forall (A : Type) (R S : rel A),
    Circular R -> Circular S -> Circular (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split.
  intros x y z [r1 s1] [r2 s2].
  split.
  - eapply HR; eassumption.
  - eapply HS; eassumption.
Qed.
(* end hide *)

(** ** Relacje euklidesowe *)

(** *** Relacje prawostronnie euklidesowe *)

Class RightEuclidean {A : Type} (R : rel A) : Prop :=
  right_euclidean : forall x y z : A, R x y -> R x z -> R y z.

#[export]
Instance RightEuclidean_Empty :
  forall R : rel Empty_set, RightEuclidean R.
(* begin hide *)
Proof.
  intros R [].
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_eq {A : Type} : RightEuclidean (@eq A).
(* begin hide *)
Proof.
  compute. congruence.
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_RFalse :
  forall A : Type, RightEuclidean (@RFalse A A).
(* begin hide *)
Proof.
  compute; trivial.
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_RTrue :
  forall A : Type, RightEuclidean (@RTrue A A).
(* begin hide *)
Proof.
  compute; trivial.
Qed.
(* end hide *)

Lemma not_RightEuclidean_Rcomp :
  exists (A : Type) (R S : rel A),
    RightEuclidean R /\ RightEuclidean S /\ ~ RightEuclidean (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 1),
    (fun n m =>
      n = 1 /\ m = 2
        \/
      n = 2 /\ m = 2).
  split; [| split].
  - red. intuition.
  - red. intuition.
  - unfold RightEuclidean, Rcomp. intro H.
    specialize (H 0 2 2).
    destruct H as (b & H1 & H2).
    + exists 1. intuition.
    + exists 1. intuition.
    + intuition; try congruence.
Qed.
(* end hide *)

Lemma not_RightEuclidean_Rinv :
  exists (A : Type) (R : rel A),
    RightEuclidean R /\ ~ RightEuclidean (Rinv R).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 1).
  split; compute.
  - firstorder.
  - intro H. specialize (H 1 0 0 ltac:(lia)). intuition congruence.
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_Rand :
  forall (A : Type) (R S : rel A),
    RightEuclidean R -> RightEuclidean S -> RightEuclidean (Rand R S).
(* begin hide *)
Proof.
  unfold RightEuclidean, Rand.
  intros A R S HR HS x y z [r1 s1] [r2 s2].
  split; firstorder.
Qed.
(* end hide *)

Lemma not_RightEuclidean_Ror :
  exists (A : Type) (R S : rel A),
    RightEuclidean R /\ RightEuclidean S /\ ~ RightEuclidean (Ror R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 1),
    (fun n m =>
      n = 0 /\ m = 2
        \/
      n = 2 /\ m = 2).
  firstorder. compute. intro H.
  specialize (H 0 1 2 ltac:(lia) ltac:(lia)). intuition congruence.
Qed.
(* end hide *)

(** *** Relacje lewostronnie Euklidesowe *)

Class LeftEuclidean {A : Type} (R : rel A) : Prop :=
  left_euclidean : forall x y z : A, R y x -> R z x -> R y z.

Lemma RightEuclidean_Rinv :
  forall {A : Type} (R : rel A),
    RightEuclidean (Rinv R) <-> LeftEuclidean R.
(* begin hide *)
Proof.
  intros A R. split; compute; firstorder.
Qed.
(* end hide *)

(** *** Relacje euklidesowe *)

Class Euclidean {A : Type} (R : rel A) : Prop :=
{
  Euclidean_RightEuclidean :> RightEuclidean R;
  Euclidean_LeftEuclidean :> LeftEuclidean R;
}.

#[export]
Instance Euclidean_Empty :
  forall R : rel Empty_set, Euclidean R.
(* begin hide *)
Proof.
  intros R. split; intros [].
Qed.
(* end hide *)

#[export]
Instance Euclidean_eq {A : Type} : Euclidean (@eq A).
(* begin hide *)
Proof.
  split; compute; congruence.
Qed.
(* end hide *)

#[export]
Instance Euclidean_RFalse :
  forall A : Type, Euclidean (@RFalse A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance Euclidean_RTrue :
  forall A : Type, Euclidean (@RTrue A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance Euclidean_Rcomp :
  forall (A : Type) (R S : rel A),
    Euclidean R -> Euclidean S -> Euclidean (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [RR RL] [SR SL]; split; compute in *.
  - intros x y z (w1 & r1 & s1) (w2 & r2 & s2).
    assert (R w1 w2) by firstorder.
    assert (R w1 x) by firstorder.
Abort.
(* end hide *)

Lemma not_Euclidean_Rcomp :
  exists (A : Type) (R S : rel A),
    Euclidean R /\ Euclidean S /\ ~ Euclidean (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m => n <= 1 /\ m <= 1),
    (fun n m => 0 < n <= 2 /\ 0 < m <= 2).
  split; [| split].
  - split; compute; intuition.
  - split; compute; intuition.
  - intros [HR HL]; compute in *.
    specialize (HR 0 2 2).
    destruct HR as (b & H1 & H2).
    + exists 1. intuition.
    + exists 1. intuition.
    + intuition; lia.
Qed.
(* end hide *)

#[export]
Instance Euclidean_Rinv :
  forall (A : Type) (R : rel A),
    Euclidean R -> Euclidean (Rinv R).
(* begin hide *)
Proof.
  intros A R [HR HL].
  split; compute in *; firstorder.
Qed.
(* end hide *)

#[export]
Instance Euclidean_Rand :
  forall (A : Type) (R S : rel A),
    Euclidean R -> Euclidean S -> Euclidean (Rand R S).
(* begin hide *)
Proof.
  intros A R S [RR RL] [SR SL].
  split; compute in *; firstorder.
Restart.
  intros A R S [RR RL] [SR SL].
  split.
  - apply RightEuclidean_Rand; assumption.
  - rewrite <- RightEuclidean_Rinv.
Abort.
(* end hide *)

#[export]
Instance Euclidean_Ror :
  forall (A : Type) (R S : rel A),
    Euclidean R -> Euclidean S -> Euclidean (Ror R S).
(* begin hide *)
Proof.
  intros A R S [RR RL] [SR SL].
  split; compute in *. firstorder.
Abort.
(* end hide *)

Lemma not_Euclidean_Ror :
  exists (A : Type) (R S : rel A),
    Euclidean R /\ Euclidean S /\ ~ Euclidean (Ror R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m => n <= 1 /\ m <= 1),
    (fun n m => 22 < n <= 32 /\ 22 < m <= 32).
  split; [| split].
  - split; compute; firstorder.
  - split; compute; firstorder.
  - intros [HR HL]; compute in *.
    specialize (HL 0 1 1 ltac:(lia) ltac:(lia)).
Admitted.
(* end hide *)

(** * Zależności między różnymi rodzajami relacji *)

#[export]
Instance Transitive_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> Transitive R.
(* begin hide *)
Proof.
  intros A R [HC].
  split; intros x y z rxy ryz.
  apply HC in rxy; subst. assumption.
Qed.
(* end hide *)

#[export]
Instance Symmetric_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> Symmetric R.
(* begin hide *)
Proof.
  intros A R [HC].
  split; intros x y r.
  rewrite (HC _ _ r) in r |- *. assumption.
Qed.
(* end hide *)

#[export]
Instance LeftEuclidean_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> LeftEuclidean R.
(* begin hide *)
Proof.
  intros A R [HC] x y z ryx rzx.
  rewrite (HC _ _ rzx) in rzx |- *. assumption.
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> RightEuclidean R.
(* begin hide *)
Proof.
  intros A R [HC] x y z rxy rxz.
  rewrite <- (HC _ _ rxy) in rxy |- *. assumption.
Qed.
(* end hide *)

#[export]
Instance Quasitransitive_LeftEuclidean :
  forall {A : Type} (R : rel A),
    LeftEuclidean R -> Quasitransitive R.
(* begin hide *)
Proof.
  intros A R HLE.
  split; unfold LeftEuclidean, AsymmetricPart in *.
  intros x y z [rxy nryx] [ryz nrzy].
Restart.
  intros A R HLE.
  split; unfold LeftEuclidean, AsymmetricPart in *.
  intros x y z [rxy nryx] [ryz nrzy]. split.
  - 
Abort.
(* end hide *)

#[export]
Instance Quasitransitive_RightEuclidean :
  forall {A : Type} (R : rel A),
    RightEuclidean R -> Quasitransitive R.
(* begin hide *)
Proof.
  intros A R HRE.
  split; unfold RightEuclidean, AsymmetricPart in *.
  intros x y z [rxy nryx] [ryz nrzy].
  rel.
Abort.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> LeftQuasiReflexive R.
(* begin hide *)
Proof.
  intros A R [HWR] x y r.
  rewrite <- (HWR _ _ r) in r. assumption.
Qed.
(* end hide *)

#[export]
Instance RightQuasiReflexive_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> RightQuasiReflexive R.
(* begin hide *)
Proof.
  intros A R [HWR] x y r.
  rewrite (HWR _ _ r) in r. assumption.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> QuasiReflexive R.
(* begin hide *)
Proof.
  split; typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> LeftQuasiReflexive R.
(* begin hide *)
Proof.
  intros A R [HR] x y r. apply HR.
Qed.
(* end hide *)

#[export]
Instance Dense_LeftQuasiReflexive :
  forall {A : Type} (R : rel A),
    LeftQuasiReflexive R -> Dense R.
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros A R HLQR; split; intros x y r.
  exists x. split; [| assumption].
  apply HLQR with y; assumption.
Qed.
(* end hide *)

#[export]
Instance Dense_RightQuasiReflexive :
  forall {A : Type} (R : rel A),
    RightQuasiReflexive R -> Dense R.
(* begin hide *)
Proof.
  unfold RightQuasiReflexive.
  intros A R HRQR; split; intros x y r.
  exists y. split; [assumption |].
  apply HRQR with x; assumption.
Qed.
(* end hide *)

#[export]
Instance RightQuasiReflexive_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> RightQuasiReflexive R.
(* begin hide *)
Proof.
  intros A R [HR] x y r. apply HR.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> QuasiReflexive R.
(* begin hide *)
Proof.
  intros A R HR; split; typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> WeaklyAntisymmetric R.
(* begin hide *)
Proof.
  intros A R [WR]; split; intros x y rxy ryx.
  apply WR. assumption.
Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric_Antisymmetric :
  forall {A : Type} (R : rel A),
    Antisymmetric R -> WeaklyAntisymmetric R.
(* begin hide *)
Proof.
  intros A R [HA]; split; intros x y rxy ryx.
  apply HA in rxy. contradiction.
Qed.
(* end hide *)

#[export]
Instance Antireflexive_Antisymmetric :
  forall {A : Type} (R : rel A),
    Antisymmetric R -> Antireflexive R.
(* begin hide *)
Proof.
  intros A R [HAS]; split; intros x nr.
  eapply HAS; eassumption.
Qed.
(* end hide *)

#[export]
Instance Antireflexive_Antitransitive :
  forall {A : Type} (R : rel A),
    Antitransitive R -> Antireflexive R.
(* begin hide *)
Proof.
  unfold Antitransitive.
  intros A R HAT; split; intros x r.
  apply (HAT x x x); assumption.
Qed.
(* end hide *)

#[export]
Instance Antisymmetric_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> Antisymmetric R.
(* begin hide *)
Proof.
  intros A R [WR]; split; intros x y rxy ryx.
Abort.
(* end hide *)

#[export]
Instance CoReflexive_Symmetric_WeaklyAntisymmetric :
  forall {A : Type} (R : rel A),
    Symmetric R -> WeaklyAntisymmetric R -> CoReflexive R.
(* begin hide *)
Proof.
  intros A R [HS] [HWR]; split; intros x y r.
  apply HWR; [assumption |]. apply HS. assumption.
Qed.
(* end hide *)

Lemma CoReflexive_spec :
  forall {A : Type} (R : rel A),
    CoReflexive R <-> Symmetric R /\ WeaklyAntisymmetric R.
(* begin hide *)
Proof.
  split; [split | destruct 1]; typeclasses eauto.
Qed.
(* end hide *)

Lemma eq_greatest_Symmetric_WeaklyAntisymmetric :
  forall {A : Type} (R : rel A),
    Symmetric R -> Antisymmetric R -> R --> eq.
(* begin hide *)
Proof.
  intros A R [HS] [HAS] x y rxy.
  assert (ryx : R y x) by (apply HS; assumption).
  apply HAS in rxy. contradiction.
Qed.
(* end hide *)

Lemma Reflexive_Symmetric_WeaklyAntisymmetric_spec :
  forall {A : Type} (R : rel A),
    Reflexive R -> Symmetric R -> Antisymmetric R -> R <--> eq.
(* begin hide *)
Proof.
  intros A R HR HS HAS; split.
  - apply eq_greatest_Symmetric_WeaklyAntisymmetric; assumption.
  - apply eq_subrelation_Reflexive; assumption.
Qed.
(* end hide *)

Lemma Symmetric_Total_spec :
  forall {A : Type} (R : rel A),
    Symmetric R -> Total R -> R <--> RTrue.
(* begin hide *)
Proof.
  intros A R [HS] [HT]; split.
  - intros x y r. red. trivial.
  - intros x y _. destruct (HT x y); [| apply HS]; assumption.
Qed.
(* end hide *)

Lemma LeftEuclidean_spec :
  forall {A : Type} (R : rel A),
    LeftEuclidean R <-> forall x y z : A, R x y -> R x z -> R z y.
(* begin hide *)
Proof.
  unfold LeftEuclidean. firstorder.
Abort.
(* end hide *)

#[export]
Instance Equivalence_Reflexive_Circular :
  forall {A : Type} (R : rel A),
    Reflexive R -> Circular R -> Equivalence R.
(* begin hide *)
Proof.
  intros A R [HR] [HC].
  split; split.
  - assumption.
  - intros x y r. eapply HC.
    + apply HR.
    + assumption.
  - intros x y z rxy ryx. eapply HC.
    + apply HR.
    + eapply HC; eassumption.
Qed.
(* end hide *)