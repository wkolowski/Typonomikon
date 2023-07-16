(** * H3z: Domknięcia i redukcje relacji [TODO] *)

Require Import Lia.

From Typonomikon Require Import H3.

Require Import Classes.RelationClasses.

(** * Domknięcia (TODO) *)

(** ** Domknięcie zwrotne *)

Inductive rc {A : Type} (R : rel A) : rel A :=
| rc_step : forall x y : A, R x y -> rc R x y
| rc_refl : forall x : A, rc R x x.

(* begin hide *)
#[global] Hint Constructors rc : core.

Ltac rc := compute; repeat split; intros; rel;
repeat match goal with
| H : rc _ _ _ |- _ => induction H; eauto
end; rel.
(* end hide *)

#[export]
Instance Reflexive_rc :
  forall (A : Type) (R : rel A), Reflexive (rc R).
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma subrelation_rc :
  forall (A : Type) (R : rel A), subrelation R (rc R).
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Reflexive S -> subrelation (rc R) S.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_idempotent :
  forall (A : Type) (R : rel A),
    rc (rc R) <--> rc R.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (rc (Rinv R)) <--> rc R.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

(** ** Domknięcie symetryczne *)

Inductive sc {A : Type} (R : rel A) : rel A :=
| sc_step : forall x y : A, R x y -> sc R x y
| sc_symm : forall x y : A, R x y -> sc R y x.

(* begin hide *)
#[global] Hint Constructors sc : core.

Ltac sc := compute; repeat split; intros; rel;
repeat match goal with
| H : sc _ _ _ |- _ => inversion H; eauto
end.
(* end hide *)

#[export]
Instance Symmetric_sc :
  forall (A : Type) (R : rel A), Symmetric (sc R).
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma subrelation_sc :
  forall (A : Type) (R : rel A), subrelation R (sc R).
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Symmetric S -> subrelation (sc R) S.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_idempotent :
  forall (A : Type) (R : rel A),
    sc (sc R) <--> sc R.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (sc (Rinv R)) <--> sc R.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

(** **** Ćwiczenie (gorsze domknięcie symetryczne) *)

(** Przyjrzyj się poniższej alternatywnej definicji domknięcia symetrycznego.
    Udowodnij, że jest ona równoważna [sc]. Dlaczego jest ona gorsza niż [sc]? *)

Inductive sc' {A : Type} (R : rel A) : rel A :=
| sc'_step :
    forall x y : A, R x y -> sc' R x y
| sc'_symm :
    forall x y : A, sc' R x y -> sc' R y x.

(* begin hide *)
#[global] Hint Constructors sc' : core.

Ltac sc' := compute; repeat split; intros; rel;
repeat match goal with
| H : sc' _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

#[export]
Instance Symmetric_sc' :
  forall (A : Type) (R : rel A), Symmetric (sc' R).
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma subrelation_sc' :
  forall (A : Type) (R : rel A), subrelation R (sc' R).
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma sc'_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Symmetric S -> subrelation (sc' R) S.
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma sc'_idempotent :
  forall (A : Type) (R : rel A),
    sc' (sc' R) <--> sc' R.
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma sc'_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (sc' (Rinv R)) <--> sc' R.
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma sc_sc' :
  forall {A : Type} (R : rel A),
    sc R <--> sc' R.
(* begin hide *)
Proof.
  split; [sc |].
  intros x y H. induction H.
  - auto.
  - destruct IHsc'; auto.
Qed.
(* end hide *)

(** ** Domknięcie przechodnie *)

Inductive tc {A : Type} (R : rel A) : rel A :=
| tc_step : forall x y : A, R x y -> tc R x y
| tc_trans : forall x y z : A, R x y -> tc R y z -> tc R x z.

(* begin hide *)
#[global] Hint Constructors tc : core.

Ltac tc := compute; repeat split; intros; rel;
match goal with
| H : tc _ _ _ |- _ => inversion H; eauto
end.
(* end hide *)

#[export]
Instance Transitive_tc :
  forall (A : Type) (R : rel A),
    Transitive (tc R).
(* begin hide *)
Proof.
  unfold Transitive.
  intros A R x y z Hxy; revert z.
  induction Hxy.
  - intros z Hyz. constructor 2 with y; assumption.
  - intros w Hzw. constructor 2 with y.
    + assumption.
    + apply IHHxy. assumption.
Defined.
(* end hide *)

Lemma subrelation_tc :
  forall (A : Type) (R : rel A), subrelation R (tc R).
(* begin hide *)
Proof. tc. Qed.
(* end hide *)

Lemma tc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Transitive S ->
      subrelation (tc R) S.
(* begin hide *)
Proof.
  unfold subrelation, Transitive.
  intros A R S HRS HT x y.
  induction 1; eauto.
Qed.
(* end hide *)

Lemma tc_idempotent :
  forall (A : Type) (R : rel A),
    tc (tc R) <--> tc R.
(* begin hide *)
Proof.
  split.
  - induction 1.
    + assumption.
    + eapply Transitive_tc; eassumption.
  - induction 1.
    + auto.
    + eapply Transitive_tc; eauto.
Qed.
(* end hide *)

Lemma tc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (tc (Rinv R)) <--> tc R.
(* begin hide *)
Proof.
  unfold Rinv; intros A R; split.
  - intros x y H. induction H.
    + auto.
    + eapply Transitive_tc; eauto.
  - induction 1.
    + auto.
    + eapply Transitive_tc; eauto.
Qed.
(* end hide *)

(** **** Ćwiczenie (alternatywne domknięcie przechodnie) *)

(** Przyjrzyj się poniższej definicji domknięcia przechodniego. Udowodnij,
    że jest ona równoważna oryginalnej definicji. Czy poniższa definicja
    jest lepsza czy gorsza od oryginalnej? *)

Inductive tc' {A : Type} (R : rel A) : rel A :=
| tc'_step :
    forall x y : A, R x y -> tc' R x y
| tc'_trans :
    forall x y z : A,
      tc' R x y -> tc' R y z -> tc' R x z.

(* begin hide *)
#[global] Hint Constructors tc' : core.

Ltac tc' := compute; repeat split; intros; rel;
repeat match goal with
| H : tc' _ _ _ |- _ => induction H; eauto
end.

#[export]
Instance Transitive_tc' :
  forall (A : Type) (R : rel A), Transitive (tc' R).
Proof. tc'. Qed.
(* end hide *)

Lemma tc_tc' :
  forall (A : Type) (R : rel A),
    tc R <--> tc' R.
(* begin hide *)
Proof.
  split.
  - induction 1; eauto.
  - induction 1.
    + auto.
    + eapply Transitive_tc; eassumption.
Qed.
(* end hide *)

(** ** Domknięcie zwrotnosymetryczne *)

Definition rsc {A : Type} (R : rel A) : rel A :=
  rc (sc' R).

(* begin hide *)
Ltac rstc := compute; repeat split; intros; rel;
repeat match goal with
| H : rc _ _ _ |- _ => induction H; eauto
| H : sc' _ _ _ |- _ => induction H; eauto
| H : tc' _ _ _ |- _ => induction H; eauto
end; rel.
(* end hide *)

#[export]
Instance Reflexive_rsc :
  forall (A : Type) (R : rel A), Reflexive (rsc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

#[export]
Instance Symmetric_rsc :
  forall (A : Type) (R : rel A), Symmetric (rsc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma subrelation_rsc :
  forall (A : Type) (R : rel A), subrelation R (rsc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rsc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Reflexive S -> Symmetric S ->
      subrelation (rsc R) S.
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rsc_idempotent :
  forall (A : Type) (R : rel A),
    rsc (rsc R) <--> rsc R.
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rsc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (rsc (Rinv R)) <--> rsc R.
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

(** ** Domknięcie zwrotnoprzechodnie *)

Inductive rtc {A : Type} (R : rel A) : rel A :=
(* | rtc_step  : forall x y : A, R x y ->  *)
| rtc_refl  : forall x : A, rtc R x x
| rtc_trans : forall x y z : A, R x y -> rtc R y z -> rtc R x z.

Lemma rtc_step :
  forall {A : Type} (R : rel A) (x y : A),
    R x y -> rtc R x y.
(* begin hide *)
Proof.
  intros A R x y. right with y.
  - assumption.
  - constructor.
Qed.
(* end hide *)

#[export]
Instance Reflexive_rtc :
  forall {A : Type} (R : rel A),
    Reflexive (rtc R).
(* begin hide *)
Proof.
  intros A R x. constructor.
Qed.
(* end hide *)

#[export]
Instance Transitive_rtc :
  forall {A : Type} (R : rel A),
    Transitive (rtc R).
(* begin hide *)
Proof.
  intros A R x y z rxy ryz; revert z ryz.
  induction rxy.
  - intros. assumption.
  - intros w rzw.
    right with y; [assumption |].
    apply IHrxy. assumption.
Qed.
(* end hide *)

Lemma rtc_RTrue_spec :
  forall A : Type, rtc (@RTrue A A) <--> RTrue.
(* begin hide *)
Proof.
  split; compute.
  - trivial.
  - intros x y _. apply rtc_step. trivial.
Qed.
(* end hide *)

(** Ćwiczneie (alternatywna definicja) *)

(** Pokaż, że poniższa alternatywna definicja domknięcia zwrotno-przechodniego
    jest równoważna oryginalnej. Która jest lepsza? *)

Definition rtc' {A : Type} (R : rel A) : rel A :=
  rc (tc R).

Lemma rtc_rtc' :
  forall {A : Type} (R : rel A),
    rtc R <--> rtc' R.
(* begin hide *)
Proof.
  split.
  - induction 1.
    + reflexivity.
    +
Admitted.
(* end hide *)

(** ** Domknięcie równoważnościowe *)

Definition ec {A : Type} (R : rel A) : rel A :=
  rtc (sc R).

(* begin hide *)
Ltac ec := compute; repeat split; intros; rel;
repeat match goal with
| H : ec _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

#[export]
Instance Reflexive_ec :
  forall {A : Type} (R : rel A),
    Reflexive (ec R).
(* begin hide *)
Proof.
  typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance Symmetric_ec :
  forall {A : Type} (R : rel A),
    Symmetric (ec R).
(* begin hide *)
Proof.
  unfold ec, Symmetric.
  intros A R x y. induction 1.
  - constructor.
  - transitivity y.
    + auto.
    + eapply rtc_trans.
      * symmetry. eassumption.
      * reflexivity.
Qed.
(* end hide *)

#[export]
Instance Transitive_ec :
  forall {A : Type} (R : rel A),
    Transitive (ec R).
(* begin hide *)
Proof.
  typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance Equivalence_ec :
  forall (A : Type) (R : rel A), Equivalence (ec R).
(* begin hide *)
Proof.
  split; typeclasses eauto.
Qed.
(* end hide *)

Lemma subrelation_ec :
  forall (A : Type) (R : rel A), subrelation R (ec R).
(* begin hide *)
Proof.
  intros A R x y r. apply rtc_step. auto.
Qed.
(* end hide *)

Lemma ec_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Equivalence S ->
      subrelation (ec R) S.
(* begin hide *)
Proof.
  unfold subrelation.
  intros A R S HRS [HR HS HT] x y e.
  induction e.
  - apply HR.
  - inversion H; subst; eauto.
Qed.
(* end hide *)

Lemma ec_idempotent :
  forall (A : Type) (R : rel A),
    ec (ec R) <--> ec R.
(* begin hide *)
Proof.

Admitted.
(* end hide *)

Lemma ec_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (ec (Rinv R)) <--> ec R.
(* begin hide *)
Proof.

Admitted.
(* end hide *)

(** **** Ćwiczenie (alternatywne definicje) *)

(** Pokaż, że poniższe alternatywne definicje domknięcia równoważnościowego
    są równoważne oryginalnej. Która definicja jest najlepsza? *)

Inductive equiv_clos {A : Type} (R : rel A) : rel A :=
| equiv_clos_step :
    forall x y : A, R x y -> equiv_clos R x y
| equiv_clos_refl :
    forall x : A, equiv_clos R x x
| equiv_clos_symm :
    forall x y : A, equiv_clos R x y -> equiv_clos R y x
| equiv_clos_trans :
    forall x y z : A,
      equiv_clos R x y -> equiv_clos R y z -> equiv_clos R x z.

(* begin hide *)
#[global] Hint Constructors equiv_clos : core.

Ltac ec' := compute; repeat split; intros; rel;
repeat match goal with
| H : equiv_clos _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

#[export]
Instance Equivalence_equiv_clos :
  forall (A : Type) (R : rel A), Equivalence (equiv_clos R).
(* begin hide *)
Proof. ec'. Qed.
(* end hide *)

Lemma ec_equiv_clos :
  forall {A : Type} (R : rel A),
    ec R <--> equiv_clos R.
(* begin hide *)
Proof.
  unfold ec.
  split.
  - induction 1; [auto |].
    transitivity y; [| auto].
    inversion H; auto.
  - induction 1.
    + eapply rtc_trans; [eauto |]. apply rtc_refl.
    + apply rtc_refl.
    + symmetry. assumption.
    + transitivity y; assumption.
Qed.
(* end hide *)

Definition rstc {A : Type} (R : rel A) : rel A :=
  tc' (sc' (rc R)).

#[export]
Instance Reflexive_rstc :
  forall {A : Type} (R : rel A),
    Reflexive (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

#[export]
Instance Symmetric_rstc :
  forall {A : Type} (R : rel A),
    Symmetric (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

#[export]
Instance Transitive_rstc :
  forall {A : Type} (R : rel A),
    Transitive (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

#[export]
Instance Equivalence_rstc :
  forall (A : Type) (R : rel A),
    Equivalence (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rstc_equiv_clos :
  forall {A : Type} (R : rel A),
    rstc R <--> equiv_clos R.
(* begin hide *)
Proof.
  split.
    induction 1.
      induction H.
        destruct H; auto.
        auto.
      eauto.
    induction 1; auto.
      do 3 constructor. assumption.
      reflexivity.
      symmetry. assumption.
      rewrite IHequiv_clos1. assumption.
Qed.
(* end hide *)

Inductive EquivalenceClosure {A : Type} (R : rel A) : rel A :=
| EC_step  : forall x y   : A, R x y -> EquivalenceClosure R x y
| EC_refl  : forall x     : A,          EquivalenceClosure R x x
| EC_symm  : forall x y   : A, R x y -> EquivalenceClosure R y x
| EC_trans : forall x y z : A, R x y -> EquivalenceClosure R y z -> EquivalenceClosure R x z.

#[global] Hint Constructors EquivalenceClosure : core.

#[export]
Instance Reflexive_EquivalenceClosure :
  forall {A : Type} (R : rel A),
    Reflexive (EquivalenceClosure R).
(* begin hide *)
Proof.
  intros A R x. auto.
Qed.
(* end hide *)

#[export]
Instance Symmetric_EquivalenceClosure :
  forall {A : Type} (R : rel A),
    Symmetric (EquivalenceClosure R).
(* begin hide *)
Proof.
  intros A R x y H.
  induction H.
  - constructor 3. assumption.
  - constructor 2.
  - constructor 1. assumption.
Abort.
(* end hide *)

#[export]
Instance Transitive_EquivalenceClosure :
  forall {A : Type} (R : rel A),
    Transitive (EquivalenceClosure R).
(* begin hide *)
Proof.
  intros A R x y z Hxy Hyz; revert z Hyz.
  induction Hxy; intros.
  - eauto.
  - auto.
  - constructor 1.
Abort.
(* end hide *)

Lemma EquivalenceClosure_equiv_clos :
  forall {A : Type} (R : rel A),
    EquivalenceClosure R <--> equiv_clos R.
(* begin hide *)
Proof.
  split.
  - intros x y H. induction H; eauto.
  - intros x y H. induction H.
    1-2: auto.
Abort.
(* end hide *)

Definition EquivalenceClosure' {A : Type} (R : rel A) : rel A :=
  rc (tc' (sc' R)).

#[export]
Instance Reflexive_EquivalenceClosure' :
  forall {A : Type} (R : rel A),
    Reflexive (EquivalenceClosure' R).
(* begin hide *)
Proof.
  typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance Symmetric_EquivalenceClosure' :
  forall {A : Type} (R : rel A),
    Symmetric (EquivalenceClosure' R).
(* begin hide *)
Proof.
  unfold EquivalenceClosure', Symmetric.
  destruct 1; [| auto].
  constructor.
  induction H.
  - constructor. symmetry. assumption.
  - transitivity y; assumption.
Qed.
(* end hide *)

#[export]
Instance Transitive_EquivalenceClosure' :
  forall {A : Type} (R : rel A),
    Transitive (EquivalenceClosure' R).
(* begin hide *)
Proof.
  unfold EquivalenceClosure', Transitive.
  intros A R x y z Hxy Hyz.
  inversion Hxy as [? ? Hxy' |]; subst; clear Hxy; [| auto].
  inversion Hyz as [? ? Hyz' |]; subst; clear Hyz; [| auto].
  constructor. transitivity y; assumption.
Qed.
(* end hide *)

Lemma EquivalenceClosure'_equiv_clos :
  forall {A : Type} (R : rel A),
    EquivalenceClosure' R <--> equiv_clos R.
(* begin hide *)
Proof.
  unfold EquivalenceClosure'.
  split.
  - inversion_clear 1 as [? ? Ht |]; [| auto].
    induction Ht.
    + induction H; auto.
    + transitivity y; assumption.
  - induction 1; [auto | auto | | ].
    + symmetry. assumption.
    + transitivity y; assumption.
Qed.
(* end hide *)

(** ** Domknięcie cyrkularne *)

Inductive CircularClosure {A : Type} (R : rel A) : rel A :=
| CC_step  :
    forall x y : A, R x y -> CircularClosure R x y
| CC_circ :
    forall x y z : A,
      CircularClosure R x y -> CircularClosure R y z ->
        CircularClosure R z x.

#[export]
Instance Circular_CircularClosure
  {A : Type} (R : rel A) : Circular (CircularClosure R).
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

(** ** Domknięcie lewostronnie kwazizwrotne *)

Inductive LeftQuasiReflexiveClosure {A : Type} (R : rel A) : rel A :=
| LQRC_step :
    forall x y : A, R x y -> LeftQuasiReflexiveClosure R x y
| LQRC_clos :
    forall x y : A, R x y -> LeftQuasiReflexiveClosure R x x.

#[export]
Instance LeftQuasiReflexive_LeftQuasiReflexiveClosure
  {A : Type} (R : rel A) : LeftQuasiReflexive (LeftQuasiReflexiveClosure R).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros x y [r | r].
  - right with y0. assumption.
  - right with y0. assumption.
Qed.
(* end hide *)

(** ** Domknięcie kozwrotne (TODO) *)

Module CoReflexiveClosure.

Private Inductive CoReflexiveClosureCarrier {A : Type} (R : rel A) : Type :=
| embed  : A -> CoReflexiveClosureCarrier R.

Arguments embed {A R} _.

Axiom WRCC_equal :
  forall {A : Type} {x y : A} {R : rel A},
    R x y -> @embed _ R x = @embed _ R y.

Inductive CoReflexiveClosure {A : Type} (R : rel A)
  : rel (CoReflexiveClosureCarrier R) :=
| step : forall x y : A, R x y -> CoReflexiveClosure R (embed x) (embed y).

End CoReflexiveClosure.

(** ** Ogólne pojęcie domknięcia *)

(** Uwaga, najnowszy pomysł: przedstawić domknięcia w taki sposób, żeby
    niepostrzeżenie przywyczajały do monad. *)

Class Closure
  {A : Type}
  (Cl : rel A -> rel A) : Prop :=
{
  pres :
    forall R S : rel A,
      (forall x y : A, R x y -> S x y) ->
        forall x y : A, Cl R x y -> Cl S x y;
  step :
    forall R : rel A,
      forall x y : A, R x y -> Cl R x y;
  join :
    forall R : rel A,
      forall x y : A, Cl (Cl R) x y -> Cl R x y;
}.

#[refine]
#[export]
Instance Closure_rc {A : Type} : Closure (@rc A) :=
{
  step := rc_step;
}.
(* begin hide *)
Proof.
  induction 2.
    constructor. apply H. assumption.
    constructor 2.
  inversion 1; subst.
    assumption.
    constructor 2.
Qed.
(* end hide *)

(** * Redukcje (TODO) *)

(** ** Redukacja zwrotna *)

Definition rr {A : Type} (R : rel A) : rel A :=
  fun x y : A => R x y /\ x <> y.

#[export]
Instance Antireflexive_rr :
  forall (A : Type) (R : rel A), Antireflexive (rr R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

From Typonomikon Require Import B4.

Lemma rr_rc :
  LEM ->
    forall (A : Type) (R : rel A),
      Reflexive R -> rc (rr R) <--> R.
(* begin hide *)
Proof.
  intro lem. rc.
  destruct (lem (a = b)).
    subst. constructor 2.
    constructor. split; auto.
Qed.
(* end hide *)

(** ** Redukcja przechodnia *)

Definition TransitiveReduction {A : Type} (R : rel A) (x y : A) : Prop :=
  R x y /\ forall z : A, R x z -> R z y -> False.

#[export]
Instance Antitransitive_TransitiveReduction
  {A : Type} (R : rel A)
  : Antitransitive (TransitiveReduction R).
(* begin hide *)
Proof.
  compute. intros x y z [H11 H12] [H21 H22] [H31 H32].
  firstorder.
Qed.
(* end hide *)

Definition TransitiveReduction' {A : Type} (R : rel A) (x y : A) : Prop :=
  R x y /\ forall z : A, rr R x z -> rr R z y -> False.

#[export]
Instance Antitransitive_TransitiveReduction'
  {A : Type} (R : rel A)
  : Antitransitive (TransitiveReduction' R).
(* begin hide *)
Proof.
  compute. intros x y z [H11 H12] [H21 H22] [H31 H32].
Abort.
(* end hide *)

(** * Cosik o systemach przepisywania (TODO) *)

(** ** Właściwość diamentu *)

Class Diamond {A : Type} (R : rel A) : Prop :=
{
  diamond :
    forall x y z : A,
      R x y -> R x z ->
        exists w : A, R y w /\ R z w
}.

#[export]
Instance Diamond_RTrue :
  forall A : Type, Diamond (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Diamond_RFalse :
  forall A : Type, Diamond (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Diamond_eq :
  forall A : Type, Diamond (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Diamond_lt :
  Diamond lt.
(* begin hide *)
Proof.
  split; intros. exists (1 + y + z). lia.
Qed.
(* end hide *)

#[export]
Instance Diamond_le :
  Diamond le.
(* begin hide *)
Proof.
  split; intros. exists (1 + y + z). lia.
Qed.
(* end hide *)

Lemma not_Diamond_gt :
  ~ Diamond gt.
(* begin hide *)
Proof.
  intros [HC].
  destruct (HC 1 0 0 ltac:(lia) ltac:(lia)).
  lia.
Qed.
(* end hide *)

#[export]
Instance Diamond_ge :
  Diamond ge.
(* begin hide *)
Proof.
  split; intros. exists 0. lia.
Qed.
(* end hide *)

Lemma not_Diamond_Rinv :
  exists (A : Type) (R : rel A),
    Diamond R /\ ~ Diamond (Rinv R).
(* begin hide *)
Proof.
  exists nat, lt.
  split; [split |].
  - intros x y z Hxy Hxz. exists (1 + y + z). lia.
  - unfold Rinv; intros [HC].
    destruct (HC 2 0 0 ltac:(lia) ltac:(lia)) as (w & H1 & _).
    lia.
Qed.
(* end hide *)

Lemma not_Diamond_Rcomp :
  exists (A : Type) (R S : rel A),
    Diamond R /\ Diamond S /\ ~ Diamond (Rcomp R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma not_Diamond_Rnot :
  exists (A : Type) (R : rel A),
    Diamond R /\ ~ Diamond (Rnot R).
(* begin hide *)
Proof.
  exists nat, le.
  split; [split |].
  - apply Diamond_le.
  - unfold Rnot; intros [HC].
    destruct (HC 1 0 0 ltac:(lia) ltac:(lia)) as (w & H1 & H2).
    lia.
Qed.
(* end hide *)

Lemma not_Diamond_Ror :
  exists (A : Type) (R S : rel A),
    Diamond R /\ Diamond S /\ ~ Diamond (Ror R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 2 + x),
    (fun x y => y = 2 * x).
  split; [| split].
  - split. intros x y z -> ->. eauto.
  - split. intros x y z -> ->. eauto.
  - unfold Ror. intros [HC].
    destruct (HC 0 2 0) as (w & [Hw1 | Hw1] & [Hw2 | Hw2]); lia.
Qed.
(* end hide *)

Lemma not_Diamond_Rand :
  exists (A : Type) (R S : rel A),
    Diamond R /\ Diamond S /\ ~ Diamond (Rand R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 1 - x),
    (fun x y => y = 2 - x).
  split; [| split].
  - split. intros x y z -> ->. eauto.
  - split. intros x y z -> ->. eauto.
  - unfold Rand. intros [HC].
    destruct (HC 2 0 0) as [w [[Hw1 Hw2] [Hw3 Hw4]]]; lia.
Qed.
(* end hide *)

(** ** Relacje lokalnie konfluentne *)

Class LocallyConfluent {A : Type} (R : rel A) : Prop :=
  locally_confluent :
    forall x y z : A, R x y -> R x z -> exists w : A, rtc R y w /\ rtc R z w.

#[export]
Instance LocallyConfluent_RTrue :
  forall A : Type, LocallyConfluent (@RTrue A A).
(* begin hide *)
Proof.
  unfold LocallyConfluent.
  intros A x y z _ _.
  exists x. split; apply rtc_step; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance LocallyConfluent_RFalse :
  forall A : Type, LocallyConfluent (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance LocallyConfluent_eq :
  forall A : Type, LocallyConfluent (@eq A).
(* begin hide *)
Proof.
  unfold LocallyConfluent.
  intros A x y z -> ->.
  exists z. split; apply rtc_refl.
Qed.
(* end hide *)

#[export]
Instance LocallyConfluent_Diamond :
  forall {A : Type} (R : rel A),
    Diamond R -> LocallyConfluent R.
(* begin hide *)
Proof.
  intros A R [HD] x y z rxy rxz.
  destruct (HD _ _ _ rxy rxz) as (w & ryw & rzw).
  exists w. split; apply rtc_step; assumption.
Qed.
(* end hide *)

Lemma not_LocallyConfluent_gt :
  ~ LocallyConfluent gt.
(* begin hide *)
Proof.
  unfold LocallyConfluent.
  intros HD.
  destruct (HD 1 0 0 ltac:(lia) ltac:(lia)) as (w & Hw1 & Hw2).
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Rinv :
  exists (A : Type) (R : rel A),
    LocallyConfluent R /\ ~ LocallyConfluent (Rinv R).
(* begin hide *)
Proof.
  exists nat, lt.
  split.
  - apply LocallyConfluent_Diamond. typeclasses eauto.
  - unfold LocallyConfluent, Rinv. intros HD.
    specialize (HD 1 0 0 ltac:(lia) ltac:(lia)).
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Rcomp :
  exists (A : Type) (R S : rel A),
    LocallyConfluent R /\ LocallyConfluent S /\ ~ LocallyConfluent (Rcomp R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Rnot :
  exists (A : Type) (R : rel A),
    LocallyConfluent R /\ ~ LocallyConfluent (Rnot R).
(* begin hide *)
Proof.
  exists nat, le.
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Ror :
  exists (A : Type) (R S : rel A),
    LocallyConfluent R /\ LocallyConfluent S /\ ~ LocallyConfluent (Ror R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 2 + x),
    (fun x y => y = 2 * x).
  split; [| split].
  - intros x y z -> ->.
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Rand :
  exists (A : Type) (R S : rel A),
    LocallyConfluent R /\ LocallyConfluent S /\ ~ LocallyConfluent (Rand R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 1 - x),
    (fun x y => y = 2 - x).
Abort.
(* end hide *)

(** ** Relacje konfluentne *)

Class Confluent {A : Type} (R : rel A) : Prop :=
  confluent :
    forall x y z : A, rtc R x y -> rtc R x z -> exists w : A, rtc R y w /\ rtc R z w.

#[export]
Instance Confluent_RTrue :
  forall A : Type, Confluent (@RTrue A A).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A x y z _ _.
  exists x. split; apply rtc_step; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance Confluent_RFalse :
  forall A : Type, Confluent (@RFalse A A).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A x y z rrxy rrxz; revert z rrxz.
  induction rrxy.
  - intros z rrxz. exists z; split; [assumption | apply rtc_refl].
  - inversion H.
Qed.
(* end hide *)

#[export]
Instance Confluent_eq :
  forall A : Type, Confluent (@eq A).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A x y z rrxy rrxz; revert z rrxz.
  induction rrxy.
  - intros z rrxz. exists z. split; [assumption | apply rtc_refl].
  - intros w rrxw. subst. destruct (IHrrxy _ rrxw) as (w' & rrzw' & rrzw'').
    exists w'. split; assumption.
Qed.
(* end hide *)

Lemma not_Confluent_Rinv :
  exists (A : Type) (R : rel A),
    Confluent R /\ ~ Confluent (Rinv R).
(* begin hide *)
Proof.
  exists nat, lt.
Abort.
(* end hide *)

Lemma not_Confluent_Rcomp :
  exists (A : Type) (R S : rel A),
    Confluent R /\ Confluent S /\ ~ Confluent (Rcomp R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma not_Confluent_Rnot :
  exists (A : Type) (R : rel A),
    Confluent R /\ ~ Confluent (Rnot R).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma not_Confluent_Ror :
  exists (A : Type) (R S : rel A),
    Confluent R /\ Confluent S /\ ~ Confluent (Ror R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

#[export]
Instance Confluent_Rand :
  forall {A : Type} (R S : rel A),
    Confluent R -> Confluent S -> Confluent (Rand R S).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A R S HCR HCS x y z rs1 rs2; revert z rs2.
  induction rs1.
  - intros z rs. exists z. split; [assumption | apply rtc_refl].
  - intros w rs3. destruct H as [r s].
Abort.
(* end hide *)

Lemma not_Confluent_Rand :
  exists (A : Type) (R S : rel A),
    Confluent R /\ Confluent S /\ ~ Confluent (Rand R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 1 - x),
    (fun x y => y = 2 - x).
Abort.
(* end hide *)