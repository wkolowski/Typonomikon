(** * BC4e: Relacje różności i ostre porządki [TODO] *)

Require Import FunctionalExtensionality Nat Arith Lia.

Require Import List.
Import ListNotations.

From Typonomikon Require Export BC2g.

(** * Relacje różności (TODO) *)

(** ** Relacje koprzechodnie *)

Class CoTransitive {A : Type} (R : rel A) : Prop :=
  cotransitive : forall {x z : A}, R x z -> forall y : A, R x y \/ R y z.

#[export]
Instance CoTransitive_Empty :
  forall R : rel Empty_set, CoTransitive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance CoTransitive_RTrue :
  forall A : Type, CoTransitive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
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

#[export]
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

#[export]
Instance CoTransitive_Ror :
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
    CoTransitive R /\ CoTransitive S /\ ~ CoTransitive (Rand R S).
(* begin hide *)
Proof.
  unfold CoTransitive, Rand.
  exists nat, ge, lt.
  repeat split; [lia | lia |].
  intros H.
Abort.
(* end hide *)

(** ** Relacje apartheidu *)

Class Apartness {A : Type} (R : rel A) : Prop :=
{
  Apartness_Antireflexive :: Antireflexive R;
  Apartness_Symmetric :: Symmetric R;
  Apartness_Cotransitive :: CoTransitive R;
}.

#[export]
Instance Apartness_Empty :
  forall R : rel Empty_set, Apartness R.
(* begin hide *)
Proof.
  split.
  - apply Antireflexive_Empty.
  - apply Symmetric_Empty.
  - apply CoTransitive_Empty.
Qed.
(* end hide *)

Lemma not_Apartness_RTrue :
  forall {A : Type}, A -> ~ Apartness (@RTrue A A).
(* begin hide *)
Proof.
  intros A a [R _ _].
  eapply not_Antireflexive_RTrue_inhabited.
  - exact a.
  - assumption.
Qed.
(* end hide *)

#[export]
Instance Apartness_RFalse :
  forall {A : Type}, Apartness (@RFalse A A).
(* begin hide *)
Proof.
  split.
  - apply Antireflexive_RFalse.
  - apply Symmetric_RFalse.
  - apply CoTransitive_RFalse.
Qed.
(* end hide *)

Lemma not_Apartness_eq :
  forall {A : Type}, A -> ~ Apartness (@eq A).
(* begin hide *)
Proof.
  intros A a [R S C].
  apply (R a).
  reflexivity.
Qed.
(* end hide *)

From Typonomikon Require Import BC4a.

Lemma Apartness_neq :
  forall {A : Type}, Apartness (Rnot (@eq A)).
(* begin hide *)
Proof.
  split.
  - typeclasses eauto.
  - apply Symmetric_Rnot, Symmetric_eq.
  - unfold Rnot. intros x y p z.
    cut (~ ~ (x <> z \/ z <> y)); cycle 1.
    + intro H. apply H. left; intro q. subst.
      apply H. right. assumption.
    + left; intro q. subst. apply H. intro. destruct H0.
      * apply H0. reflexivity.
      * apply p.
Abort.
(* end hide *)

Lemma Apartnes_neq :
  (forall {A : Type}, Apartness (Rnot (@eq A))) ->
    (forall {A : Type} (x y : A), x <> y \/ ~ x <> y).
(* begin hide *)
Proof.
  unfold Rnot.
  intros H A x y.
  destruct (H A) as [R S C].
  right; intro p.
  specialize (C _ _ p).
Abort.
(* end hide *)

#[export]
Instance Apartness_Rinv :
  forall (A : Type) (R : rel A),
    Apartness R -> Apartness (Rinv R).
(* begin hide *)
Proof.
  unfold Rinv. intros A R [Anti Sym CoTrans].
  split; [| | unfold CoTransitive in *].
  - now apply Antireflexive_Rinv.
  - now apply Symmetric_Rinv.
  - intros x z rzx y.
    destruct (CoTrans _ _ rzx y); [right | left]; assumption.
Qed.
(* end hide *)

Lemma not_Apartness_Rcomp :
  exists (A : Type) (R S : rel A),
    Apartness R /\ Apartness S /\ ~ Apartness (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b1 b2 => b1 = negb b2).
  assert (H' : Apartness R).
  {
    unfold R. split.
    - now intros [] [=].
    - intros x [] ->; cbn; reflexivity.
    - intros x [] -> []; cbn; intuition.
  }
  exists bool, R, R.
  split; [| split]; [assumption | assumption |].
  unfold Rcomp, R.
  destruct 1 as [A _ _].
  apply A with true.
  exists false; cbn.
  intuition.
Qed.
(* end hide *)

Lemma not_Apartness_Rnot :
  exists (A : Type) (R : rel A),
    Apartness R /\ ~ Apartness (Rnot R).
(* begin hide *)
Proof.
  exists nat, (Rnot eq).
  split.
  - unfold Rnot; split; [red | red | unfold CoTransitive]; lia.
  - intros [HA HS HC]; unfold Rnot in *.
    apply (HA 0). lia.
Qed.
(* end hide *)

#[export]
Instance Apartness_Ror :
  forall (A : Type) (R S : rel A),
    Apartness R -> Apartness S -> Apartness (Ror R S).
(* begin hide *)
Proof.
  intros A R S [RA RS RC] [SA SS SC].
  unfold Ror; split.
  - now apply Antireflexive_Ror.
  - now apply Symmetric_Ror.
  - now apply CoTransitive_Ror.
Qed.
(* end hide *)

Lemma not_Rand_Apartness :
  exists (A : Type) (R S : rel A),
    Apartness R /\ Apartness S /\ ~ Apartness (Rand R S).
(* begin hide *)
Proof.
  exists
    (list (nat * nat)),
    (fun l1 l2 => map fst l1 <> map fst l2),
    (fun l1 l2 => map snd l1 <> map snd l2).
  split; [| split].
  - repeat split; unfold CoTransitive; repeat intro.
    + congruence.
    + congruence.
    + destruct (list_eq_dec Nat.eq_dec (map fst x) (map fst y)); subst.
      * rewrite <- e. right. assumption.
      * left. assumption.
  - repeat split; repeat intro.
    + congruence.
    + congruence.
    + destruct (list_eq_dec Nat.eq_dec (map snd x) (map snd y)); subst.
      * rewrite <- e. right. assumption.
      * left. assumption.
  - intros [A S C]; unfold CoTransitive, Rand in C.
    specialize (C [(1, 2)] [(2, 1)]); cbn in C.
    specialize (C ltac:(split; cbn in *; congruence) [(2, 2)]); cbn in C.
    decompose [and or] C; clear C; congruence.
Qed.
(* end hide *)

(** * Relacje trychotomiczne *)

Class Trichotomous {A : Type} (R : rel A) : Prop :=
  trichotomous : forall x y : A, R x y \/ x = y \/ R y x.

#[export]
Instance Trichotomous_Total :
  forall (A : Type) (R : rel A),
    Total R -> Trichotomous R.
(* begin hide *)
Proof.
  intros A R Ht x y.
  destruct (total x y).
  - left. assumption.
  - do 2 right. assumption.
Qed.
(* end hide *)

#[export]
Instance Trichotomous_Empty :
  forall R : rel Empty_set, Trichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Trichotomous_RTrue :
  forall A : Type, Trichotomous (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Trichotomous_RFalse_subsingleton :
  forall A : Type, (forall x y : A, x = y) -> Trichotomous (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Trichotomous_RFalse_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ Trichotomous (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Trichotomous_eq_subsingleton :
  forall A : Type, (forall x y : A, x = y) -> Trichotomous (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Trichotomous_eq :
  exists A : Type, ~ Trichotomous (@eq A).
(* begin hide *)
Proof.
  exists bool.
  intros Ht.
  destruct (Ht true false); rel.
Qed.
(* end hide *)

#[export]
Instance Trichotomous_Rinv :
  forall (A : Type) (R : rel A),
    Trichotomous R -> Trichotomous (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Trichotomous_Rcomp :
  exists (A : Type) (R S : rel A),
    Trichotomous R /\ Trichotomous S /\ ~ Trichotomous (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt.
  repeat split; [now red; lia.. |].
  unfold Rcomp, Trichotomous.
  now intros Ht; decompose [and or ex] (Ht 0 1); lia.
Qed.
(* end hide *)

Lemma not_Trichotomous_Rnot :
  exists (A : Type) (R : rel A),
    Trichotomous R /\ ~ Trichotomous (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => b = negb b').
  exists bool, R. repeat split; intros.
    now intros [] []; compute; auto.
    unfold Rnot, Trichotomous; intros Ht.
    destruct (Ht true false); compute in *; [easy |].
    destruct H; intuition.
Qed.
(* end hide *)

#[export]
Instance Trichotomous_Ror :
  forall (A : Type) (R S : rel A),
    Trichotomous R -> Trichotomous S -> Trichotomous (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Trichotomous_Ror_l :
  forall (A : Type) (R S : rel A),
    Trichotomous R -> Trichotomous (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Trichotomous_Ror_r :
  forall (A : Type) (R S : rel A),
    Trichotomous S -> Trichotomous (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Trichotomous_Rand :
  exists (A : Type) (R S : rel A),
    Trichotomous R /\ Trichotomous S /\ ~ Trichotomous (Rand R S).
(* begin hide *)
Proof.
  exists nat, lt, gt.
  repeat split; [now red; lia.. |].
  unfold Rand, Trichotomous.
  now intros Ht; decompose [and or] (Ht 0 1); lia.
Qed.
(* end hide *)

(** * Słabe wersje relacji trychotomicznych i totalnych (TODO) *)

(** ** Relacje spójne *)

Class Connected {A : Type} (R : rel A) : Prop :=
  connected : forall x y : A, ~ R x y /\ ~ R y x -> x = y.

#[export]
Instance Connected_Total :
  forall (A : Type) (R : rel A),
    Total R -> Connected R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Connected_Empty :
  forall R : rel Empty_set, Connected R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Connected_unit :
  forall R : rel unit, Connected R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Connected_RTrue :
  forall A : Type,
    Connected (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Connected_RFalse_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ Connected (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Connected_Rinv :
  forall (A : Type) (R : rel A),
    Connected R -> Connected (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Connected_Rcomp :
  exists (A : Type) (R S : rel A),
    Connected R /\ Connected S /\ ~ Connected (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt.
  repeat split; [now red; lia.. |].
  unfold Rcomp, Connected.
  intros HC.
  enough (0 = 1); [easy |].
  now apply HC; split; intros []; lia.
Qed.
(* end hide *)

Lemma not_Connected_Rnot :
  exists (A : Type) (R : rel A),
    Connected R /\ ~ Connected (Rnot R).
(* begin hide *)
Proof.
  exists bool, RTrue.
  split.
  - rel.
  - intros HC; compute in HC.
    specialize (HC true false ltac:(intuition)).
    congruence.
Qed.
(* end hide *)

#[export]
Instance Connected_Ror :
  forall (A : Type) (R S : rel A),
    Connected R -> Connected S ->
      Connected (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Connected_Rand :
  exists (A : Type) (R S : rel A),
    Connected R
      /\
    Connected S
      /\
    ~ Connected (Rand R S).
(* begin hide *)
Proof.
  exists bool, (fun x _ => x = true), (fun x _ => x = false).
  split; [| split].
  - rel. destruct x, y; intuition.
  - rel. destruct x, y; intuition.
  - intros HC; compute in HC.
    specialize (HC true false ltac:(intuition)).
    congruence.
Qed.
(* end hide *)

(** ** Relacje słabo totalne *)

Class WeaklyTotal {A : Type} (R : rel A) : Prop :=
  weakly_total : forall x y : A, ~ R x y -> R y x.

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
  unfold Rcomp, WeaklyTotal.
  intros A R S HR HS x y H.
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
  - unfold Rand, WeaklyTotal.
    intros H; specialize (H true false).
    intuition.
Qed.
(* end hide *)

Lemma not_Antireflexive_WeaklyTotal_inhabited :
  forall (A : Type) (R : rel A) (x : A),
    WeaklyTotal R -> ~ Antireflexive R.
(* begin hide *)
Proof.
  intros A R x HWT HA. rel.
Qed.
(* end hide *)

(** ** Relacje słabo trychotomiczne *)

Class WeaklyTrichotomous {A : Type} (R : rel A) : Prop :=
  weakly_trichotomous : forall x y : A, x <> y -> R x y \/ R y x.

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
  exists nat, lt, lt.
  repeat split; [now red; lia.. |].
  unfold Rcomp, WeaklyTrichotomous.
  now intros H; edestruct (H 0 1) as [[b Hb] | [b Hb]]; lia.
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
  - intros H. specialize (H true false ltac:(congruence)). rel.
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
  - intros H.
    specialize (H true false ltac:(congruence)).
    rel.
Qed.
(* end hide *)

(** * Ostre porządki (TODO) *)

Class StrictPreorder {A : Type} (R : rel A) : Prop :=
{
  StrictPreorder_Antireflexive :: Antireflexive R;
  StrictPreorder_CoTransitive :: CoTransitive R;
}.

Class StrictPartialOrder {A : Type} (R : rel A) : Prop :=
{
  StrictPartialOrder_Preorder :: StrictPreorder R;
  StrictPartialOrder_Antisymmetric :: Antisymmetric R;
}.

Class StrictTotalOrder {A : Type} (R : rel A) : Prop :=
{
  StrictTotalOrder_PartialOrder :: StrictPartialOrder R;
  StrictTotalOrder_Connected : Connected R;
}.

Class Quasiorder {A : Type} (R : rel A) : Prop :=
{
  Quasiorder_Antireflexive :: Antireflexive R;
  Quasiorder_Transitive :: Transitive R;
}.
