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

Instance WeaklyReflexive_eq {A : Type} : WeaklyReflexive (@eq A).
(* begin hide *)
Proof.
  split; trivial.
Qed.
(* end hide *)

Instance WeaklyReflexive_RFalse :
  forall A : Type, WeaklyReflexive (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ [].
Qed.
(* end hide *)

Lemma WeaklyReflexive_subrelation_eq :
  forall (A : Type) (R : rel A),
    WeaklyReflexive R -> subrelation R (@eq A).
(* begin hide *)
Proof.
  intros A R [H] x y. apply H.
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

Instance ProofWiki :
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

Instance Circular_eq {A : Type} : Circular (@eq A).
(* begin hide *)
Proof.
  split; congruence.
Qed.
(* end hide *)

Instance Circular_RFalse :
  forall A : Type, Circular (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ _ [].
Qed.
(* end hide *)

Instance Circular_RTrue :
  forall A : Type, Circular (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ _ [].
Qed.
(* end hide *)

Require Import Lia.

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
      n = 0 /\ m = 2
        \/
      n = 2 /\ m = 3
        \/
      n = 3 /\ m = 0).
  split; [| split].
  - split; lia.
  - split; lia.
  - unfold Rcomp; destruct 1 as [H].
(*     Axiom x y z : nat. *)
    specialize (H 1 2 3). destruct H.
    + exists 2. intuition.
Admitted.
(* end hide *)

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

Instance RandomWebsite :
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
