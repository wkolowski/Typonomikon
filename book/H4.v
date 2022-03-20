(** * H4: Wincyj relacji *)

Require Import H3.

(** W tym rozdziale dalej będziemy zajmować się relacjami (a konkretnie relacjami
    binarnymi i homogenicznymi), ale nudniejszymi i mniej ważnymi niż w poprzednim
    rozdziale. *)

(** * "Słabe" relacje *)

(** ** Relacje słabozwrotne *)

Class WeaklyReflexive {A : Type} (R : rel A) : Prop :=
{
    weaklyReflexive : forall x y : A, R x y -> x = y;
}.

Instance WeaklyReflexive_empty :
  forall R : rel Empty_set, WeaklyReflexive R.
(* begin hide *)
Proof.
  split; intros [].
Qed.
(* end hide *)

Instance WeaklyReflexive_RFalse :
  forall A : Type, WeaklyReflexive (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ [].
Qed.
(* end hide *)

Instance WeaklyReflexive_eq :
  forall A : Type, WeaklyReflexive (@eq A).
(* begin hide *)
Proof.
  split; trivial.
Qed.
(* end hide *)

Lemma WeaklyReflexive_subrelation_eq :
  forall {A : Type} {R : rel A},
    WeaklyReflexive R -> subrelation R (@eq A).
(* begin hide *)
Proof.
  intros A R [H] x y. apply H.
Qed.
(* end hide *)

Instance WeaklyReflexive_Rinv :
  forall (A : Type) (R : rel A),
    WeaklyReflexive R -> WeaklyReflexive (Rinv R).
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

Instance WeaklyReflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    WeaklyReflexive R -> WeaklyReflexive S -> WeaklyReflexive (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split.
  intros x y (z & r & s).
  rewrite (HR _ _ r), (HS _ _ s).
  reflexivity.
Qed.
(* end hide *)

Lemma not_WeaklyReflexive_Rnot :
  exists (A : Type) (R : rel A),
    WeaklyReflexive R /\ ~ WeaklyReflexive (Rnot R).
(* begin hide *)
Proof.
  exists bool, (fun b1 b2 => b1 = true /\ b2 = true).
  split; [rel |].
  unfold Rnot; intros [WR].
  specialize (WR true false); intuition.
Qed.
(* end hide *)

Instance WeaklyReflexive_Ror :
  forall (A : Type) (R S : rel A),
    WeaklyReflexive R -> WeaklyReflexive S -> WeaklyReflexive (Ror R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split.
  intros x y [r | s].
  - apply HR; assumption.
  - apply HS; assumption.
Qed.
(* end hide *)

Instance WeaklyReflexive_Rand_l :
  forall (A : Type) (R S : rel A),
    WeaklyReflexive R -> WeaklyReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HR]; split.
  intros x y [r s].
  apply HR; assumption.
Qed.
(* end hide *)

Instance WeaklyReflexive_Rand_r :
  forall (A : Type) (R S : rel A),
    WeaklyReflexive S -> WeaklyReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HS]; split.
  intros x y [r s].
  apply HS; assumption.
Qed.
(* end hide *)

Instance WeaklyReflexive_LeftUnique :
  forall {A : Type} (R : rel A),
    LeftUnique R -> WeaklyReflexive (Rcomp R (Rinv R)).
(* begin hide *)
Proof.
  intros A R [H].
  split; unfold Rinv.
  intros x y (z & r & r').
  eapply H; eassumption.
Qed.
(* end hide *)

(** * Ciekawostki *)

(** TODO *)

(** ** Relacje cyrkularne *)

Class Circular {A : Type} (R : rel A) : Prop :=
{
    circular : forall x y z : A, R x y -> R y z -> R z x;
}.

Instance Circular_empty :
  forall R : rel Empty_set, Circular R.
(* begin hide *)
Proof.
  split; intros [].
Qed.
(* end hide *)

Instance Circular_RTrue :
  forall A : Type, Circular (@RTrue A A).
(* begin hide *)
Proof.
  split; compute. trivial.
Qed.
(* end hide *)

Instance Circular_RFalse :
  forall A : Type, Circular (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ _ [].
Qed.
(* end hide *)

Instance Circular_eq {A : Type} : Circular (@eq A).
(* begin hide *)
Proof.
  split; congruence.
Qed.
(* end hide *)

Require Import Lia.

Instance Circular_Rcomp :
  forall (A : Type) (R S : rel A),
    Circular R -> Circular S -> Circular (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split; red.
  intros x y z (w1 & r1 & s1) (w2 & r2 & s2).
Abort.
(* end hide *)

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

(** ** Relacje lewostronnie kwazi-zwrotne *)

Class LeftQuasiReflexive {A : Type} (R : rel A) : Prop :=
  lqr : forall x y : A, R x y -> R x x.

Instance LeftQuasiReflexive_empty :
  forall R : rel Empty_set, LeftQuasiReflexive R.
(* begin hide *)
Proof.
  intros R [].
Qed.
(* end hide *)

Instance LeftQuasiReflexive_eq {A : Type} : LeftQuasiReflexive (@eq A).
(* begin hide *)
Proof.
  compute. trivial.
Qed.
(* end hide *)

Instance LeftQuasiReflexive_RFalse :
  forall A : Type, LeftQuasiReflexive (@RFalse A A).
(* begin hide *)
Proof.
  compute. trivial.
Qed.
(* end hide *)

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

Inductive LeftQuasiReflexiveClosure {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | step :
        forall x y : A, R x y -> LeftQuasiReflexiveClosure R x y
    | clos :
        forall x y : A, R x y -> LeftQuasiReflexiveClosure R x x.

Instance LeftQuasiReflexive_LeftQuasiReflexiveClosure
  {A : Type} (R : A -> A -> Prop) : LeftQuasiReflexive (LeftQuasiReflexiveClosure R).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros x y [r | r].
  - right with y0. assumption.
  - right with y0. assumption.
Qed.
(* end hide *)

(** ** Relacje prawostronnie kwazi-zwrotne *)

Class RightQuasiReflexive {A : Type} (R : rel A) : Prop :=
  rqr : forall x y : A, R x y -> R y y.

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

(** ** Relacje kwazi-zwrotne *)

Class QuasiReflexive {A : Type} (R : rel A) : Prop :=
{
    QR_LeftQuasiReflexive :> LeftQuasiReflexive R;
    QR_RightQuasiReflexive :> RightQuasiReflexive R;
}.

Instance LeftQuasiReflexive_Rinv :
  forall {A : Type} (R : rel A),
    RightQuasiReflexive R -> LeftQuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  compute. eauto.
Qed.
(* end hide *)

Instance QuasiReflexive_empty :
  forall R : rel Empty_set, QuasiReflexive R.
(* begin hide *)
Proof.
  split.
  - typeclasses eauto.
  - rewrite RightQuasiReflexive_spec. typeclasses eauto.
Qed.
(* end hide *)

Instance QuasiReflexive_eq {A : Type} : QuasiReflexive (@eq A).
(* begin hide *)
Proof.
  split.
  - typeclasses eauto.
  - red. trivial.
Qed.
(* end hide *)

Instance QuasiReflexive_RFalse :
  forall A : Type, QuasiReflexive (@RFalse A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

Instance QuasiReflexive_RTrue :
  forall A : Type, QuasiReflexive (@RTrue A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

Instance QuasiReflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [RL RR] [SL SR].
  split; unfold LeftQuasiReflexive, RightQuasiReflexive, Rcomp in *.
Abort.
(* end hide *)

Instance QuasiReflexive_Rinv :
  forall (A : Type) (R : rel A),
    QuasiReflexive R -> QuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  intros A R [HL HR].
  split; firstorder.
Qed.
(* end hide *)

Instance QuasiReflexive_Rand :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HRL HRR] [HSL HSR].
  split; firstorder.
Qed.
(* end hide *)

Instance QuasiReflexive_Ror :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Ror R S).
(* begin hide *)
Proof.
  intros A R S [HRL HRR] [HSL HSR].
  split; firstorder.
Qed.
(* end hide *)

(** ** Relacje prawostronnie Euklidesowe *)

Class RightEuclidean {A : Type} (R : rel A) : Prop :=
  re : forall x y z : A, R x y -> R x z -> R y z.

Instance RightEuclidean_empty :
  forall R : rel Empty_set, RightEuclidean R.
(* begin hide *)
Proof.
  intros R [].
Qed.
(* end hide *)

Instance RightEuclidean_eq {A : Type} : RightEuclidean (@eq A).
(* begin hide *)
Proof.
  compute. congruence.
Qed.
(* end hide *)

Instance RightEuclidean_RFalse :
  forall A : Type, RightEuclidean (@RFalse A A).
(* begin hide *)
Proof.
  compute; trivial.
Qed.
(* end hide *)

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

(** ** Relacje lewostronnie Euklidesowe *)

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

(** ** Relacje Euklidesowe *)

Class Euclidean {A : Type} (R : rel A) : Prop :=
{
    Euclidean_RightEuclidean :> RightEuclidean R;
    Euclidean_LeftEuclidean :> LeftEuclidean R;
}.

Instance Euclidean_empty :
  forall R : rel Empty_set, Euclidean R.
(* begin hide *)
Proof.
  intros R. split; intros [].
Qed.
(* end hide *)

Instance Euclidean_eq {A : Type} : Euclidean (@eq A).
(* begin hide *)
Proof.
  split; compute; congruence.
Qed.
(* end hide *)

Instance Euclidean_RFalse :
  forall A : Type, Euclidean (@RFalse A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

Instance Euclidean_RTrue :
  forall A : Type, Euclidean (@RTrue A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

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

Instance Euclidean_Rinv :
  forall (A : Type) (R : rel A),
    Euclidean R -> Euclidean (Rinv R).
(* begin hide *)
Proof.
  intros A R [HR HL].
  split; compute in *; firstorder.
Qed.
(* end hide *)

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

(** ** Relacje antyprzechodnie *)

Class Antitransitive {A : Type} (R : A -> A -> Prop) : Prop :=
  antitransitive : forall x y z : A, R x y -> R y z -> ~ R x z.

Definition TransitiveReduction {A : Type} (R : A -> A -> Prop) (x y : A) : Prop :=
  R x y /\ forall z : A, R x z -> R z y -> False.

Instance Antitransitive_TransitiveReduction
  {A : Type} (R : A -> A -> Prop)
  : Antitransitive (TransitiveReduction R).
(* begin hide *)
Proof.
  compute. intros x y z [H11 H12] [H21 H22] [H31 H32].
  firstorder.
Qed.
(* end hide *)

Definition TransitiveReduction' {A : Type} (R : A -> A -> Prop) (x y : A) : Prop :=
  R x y /\ forall z : A, rr R x z -> rr R z y -> False.

Instance Antitransitive_TransitiveReduction'
  {A : Type} (R : A -> A -> Prop)
  : Antitransitive (TransitiveReduction' R).
(* begin hide *)
Proof.
  compute. intros x y z [H11 H12] [H21 H22] [H31 H32].
Abort.
(* end hide *)

(** ** Relacje koprzechodnie *)

Class CoTransitive {A : Type} (R : rel A) : Prop :=
  cotransitive : forall {x z : A}, R x z -> forall y : A, R x y \/ R y z.

Instance CoTransitive_Empty :
  forall R : rel Empty_set, CoTransitive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance CoTransitive_RTrue :
  forall A : Type, CoTransitive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance CoTransitive_RFalse :
  forall A : Type, CoTransitive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma CoTransitive_eq_unit :
  CoTransitive (@eq unit).
(* begin hide *)
Proof. rel. intuition. Qed.
(* end hide *)

Lemma not_CoTransitive_eq_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ CoTransitive (@eq A).
(* begin hide *)
Proof.
  unfold CoTransitive.
  intros A x y Hneq CT.
  destruct (CT x x eq_refl y); congruence.
Qed.
(* end hide *)

Instance CoTransitive_Rinv :
  forall (A : Type) (R : rel A),
    CoTransitive R -> CoTransitive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_CoTransitive_Rcomp :
  exists (A : Type) (R S : rel A),
    CoTransitive R /\ CoTransitive S /\ ~ CoTransitive (Rcomp R S).
(* begin hide *)
Proof.
  unfold CoTransitive, Rcomp.
  exists nat, lt, lt.
  repeat split; [lia | lia |].
  intros H.
  assert (H012 : exists b : nat, 0 < b < 2) by (exists 1; lia).
  destruct (H 0 2 H012 1) as [[b Hb] | [b Hb]]; lia.
Qed.
(* end hide *)

Lemma not_CoTransitive_Rnot :
  exists (A : Type) (R : rel A),
    CoTransitive R /\ ~ CoTransitive (Rnot R).
(* begin hide *)
Proof.
  unfold CoTransitive, Rnot.
  exists nat, (fun x y => x <> y).
  split; [lia |].
  intros H.
  specialize (H 0 0 ltac:(lia) 1).
  lia.
Qed.
(* end hide *)

Instance not_CoTransitive_Ror :
  forall (A : Type) (R S : rel A),
    CoTransitive R -> CoTransitive S -> CoTransitive (Ror R S).
(* begin hide *)
Proof.
  unfold CoTransitive, Ror.
  intros A R S CTR CTS x y [r | s] z.
  - destruct (CTR _ _ r z); auto.
  - destruct (CTS _ _ s z); auto.
Qed.
(* end hide *)

Lemma not_CoTransitive_Rand :
  exists (A : Type) (R S : rel A),
    CoTransitive R /\ CoTransitive S /\ CoTransitive (Rand R S).
(* begin hide *)
Proof.
  unfold CoTransitive, Rand.
  exists nat, lt, gt.
  repeat split; [lia | lia |].
  intros x y [H1 H2]; lia.
Qed.
(* end hide *)

(** * To może być nawet ważne *)

(** ** Relacje słabo ekstensjonalne *)

Class WeaklyExtensional {A : Type} (R : rel A) : Prop :=
{
    weakly_extensional : forall x y : A, (forall t : A, R t x <-> R t y)-> x = y; 
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

(** * Wut *)

Lemma Reflexive_from_Symmetric_Transitive_RightTotal :
  forall {A : Type} (R : rel A),
    Symmetric R -> Transitive R -> RightTotal R -> Reflexive R.
(* begin hide *)
Proof.
  intros A R [HS] [HT] [HRT].
  split; intros x.
  destruct (HRT x) as [y r].
  apply HT with y.
  - apply HS. assumption.
  - assumption.
Qed.
(* end hide *)

(** * Wincyj domknięć *)

(** ** Domknięcie cyrkularne *)

Inductive CircularClosure {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | inj  :
        forall x y : A, R x y -> CircularClosure R x y
    | circ :
        forall x y z : A,
          CircularClosure R x y -> CircularClosure R y z ->
            CircularClosure R z x.

Instance Circular_CircularClosure
  {A : Type} (R : A -> A -> Prop) : Circular (CircularClosure R).
(* begin hide *)
Proof.
  split; intros x y z H1 H2; revert z H2.
  induction H1.
  - destruct 1.
    + eright; constructor; eassumption.
    + eright with z.
      * constructor; assumption.
      * eright; eassumption.
  - intros. eright with x.
    + eright with y; eassumption.
    + assumption.
Qed.
(* end hide *)

(** ** Domknięcie słabozwrotne (TODO) *)

Module WeaklyReflexiveClosure.

Private Inductive WeaklyReflexiveClosureCarrier {A : Type} (R : rel A) : Type :=
    | embed  : A -> WeaklyReflexiveClosureCarrier R.

Arguments embed {A R} _.

Axiom WRCC_equal :
  forall {A : Type} {x y : A} {R : rel A},
    R x y -> @embed _ R x = @embed _ R y.

Inductive WeaklyReflexiveClosure {A : Type} (R : rel A)
  : rel (WeaklyReflexiveClosureCarrier R) :=
  | step : forall x y : A, R x y -> WeaklyReflexiveClosure R (embed x) (embed y).

End WeaklyReflexiveClosure.