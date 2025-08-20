Require Import Coq.Classes.RelationClasses.

Definition Compatible
  {X Y : Type} (RX : X -> X -> Prop) (RY : Y -> Y -> Prop) (S : X -> Y -> Prop) : Prop :=
    forall (x1 x2 : X) (y1 y2 : Y),
      S x1 y1 -> S x2 y2 -> (RX x1 x2 <-> RY y1 y2).

Definition Compatible'
  {X Y : Type} (RX : X -> X -> Prop) (RY : Y -> Y -> Prop) (S : X -> Y -> Prop) : Prop :=
    forall (x1 : X) (y1 : Y),
      S x1 y1 ->
        (forall x2 : X, RX x1 x2 -> exists y2 : Y, RY y1 y2 /\ S x2 y2)
          /\
        (forall y2 : Y, RY y1 y2 -> exists x2 : X, RX x1 x2 /\ S x2 y2).

Parameters
  (A : Type)
  (R : A -> A -> Prop).

Definition Congruence (S : A -> A -> Prop) : Prop :=
  Equivalence S /\ Compatible R R S.

Definition Congruence' (S : A -> A -> Prop) : Prop :=
  Equivalence S /\ Compatible' R R S.

Lemma Congruence_eq :
  Congruence (fun x y => x = y).
Proof.
  unfold Congruence, Compatible; split.
  - now typeclasses eauto.
  - now firstorder subst.
Qed.

Lemma Congruence'_eq :
  Congruence' (fun x y => x = y).
Proof.
  unfold Congruence', Compatible'; split.
  - now typeclasses eauto.
  - now intros ? ? ->; split; eauto.
Qed.

Definition Convex (P : A -> Prop) : Prop :=
  forall (x y w : A), P x -> P y -> R x w -> R w y -> P w.

Inductive Equiv (P : A -> Prop) (x y : A) : Prop :=
| Equiv_refl : x = y -> Equiv P x y
| Equiv_convex : P x -> P y -> Equiv P x y.

#[export] Hint Constructors Equiv : core.

#[export] Instance Equivalence_Equiv :
  forall P : A -> Prop, Equivalence (Equiv P).
Proof.
  split; red.
  - now constructor.
  - now intros x y [-> |]; constructor.
  - now intros x y z [-> |] [-> |]; constructor.
Qed.

Lemma Congruence_Convex :
  forall (P : A -> Prop),
    Convex P -> Congruence (Equiv P).
Proof.
  unfold Convex, Congruence, Compatible.
  intros P Hc; split; [now typeclasses eauto |].
  intros x1 x2 y1 y2 [-> |] [-> |]; [easy | ..].
  - admit.
  - admit.
Abort.

Theorem Congruence'_Convex :
  forall (P : A -> Prop),
    Convex P -> Congruence' (Equiv P).
Proof.
  unfold Convex, Congruence', Compatible'.
  intros P Hc; split; [now typeclasses eauto |].
  intros x1 y1 [Heq |].
  - split.
    + intros x2 rx. admit.
    + intros y2 ry. admit.
  - split.
    + intros x2 rx. admit.
    + intros y2 ry. admit.
Abort.
