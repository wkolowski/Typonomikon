(** * H4: Wincyj relacji *)

Require Import H3.

(** W tym rozdziale dalej będziemy zajmować się relacjami (a konkretnie relacjami
    binarnymi i homogenicznymi), ale nudniejszymi i mniej ważnymi niż w poprzednim
    rozdziale. *)

(** * Relacje kozwrotne *)

(** TODO: Mądrzej byłoby nazwać to relacją słabozwrotną, gdyż jest to coś jak relacja
    antyzwrotna, ale z równością zamiast fałszu. *)

Class CoReflexive {A : Type} (R : rel A) : Prop :=
{
    coreflexive : forall x y : A, R x y -> x = y;
}.

Instance CoReflexive_empty :
  forall R : rel Empty_set, CoReflexive R.
(* begin hide *)
Proof.
  split; intros [].
Qed.
(* end hide *)

Instance CoReflexive_eq {A : Type} : CoReflexive (@eq A).
(* begin hide *)
Proof.
  split; trivial.
Qed.
(* end hide *)

Instance CoReflexive_RFalse :
  forall A : Type, CoReflexive (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ [].
Qed.
(* end hide *)

Lemma CoReflexive_subrelation_eq :
  forall (A : Type) (R : rel A),
    CoReflexive R -> subrelation R (@eq A).
(* begin hide *)
Proof.
  intros A R [H] x y. apply H.
Qed.
(* end hide *)

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

Instance ProofWiki :
  forall {A : Type} (R : rel A),
    LeftUnique R -> CoReflexive (Rcomp R (Rinv R)).
(* begin hide *)
Proof.
  intros A R [H].
  split; unfold Rinv.
  intros x y (z & r & r').
  eapply H; eassumption.
Qed.
(* end hide *)