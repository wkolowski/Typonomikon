(** * H4: Wincyj relacji *)

(* Module wut.

From stdpp Require Import prelude.

Print strict.
Print diamond.
Print locally_confluent.
Print confluent.
Print Trichotomy.
Print PartialOrder.
Print Total.
Print TotalOrder.
Print relation_equivalence.
Print Setoid_Theory.
Print TrichotomyT.
Print DefaultRelation.
Print order.
Print antisymmetric.
Print RewriteRelation.
Print StrictOrder.
Print all_loop.
Print strict.
Print nf.
Print red.

End wut. *)

Require Import H3.

Require Import Lia.

(** W tym rozdziale dalej będziemy zajmować się relacjami (a konkretnie relacjami
    binarnymi i homogenicznymi), ale nudniejszymi i mniej ważnymi niż w poprzednim
    rozdziale. *)

(*  left_unique           : forall (a a' : A) (b : B), R a b -> R a' b -> a = a'
    right_unique          : forall (a : A) (b b' : B), R a b -> R a b' -> b = b'

    left_total            : forall a : A, exists b : B, R a b
    right_total           : forall b : B, exists a : A, R a b

    reflexive             : forall x : A, R x x
    antireflexive         : forall x : A, ~ R x x
    irreflexive           : exists x : A, ~ R x x
(*  not_antireflexive     : exists x : A, R x x *)
    coreflexive           : forall x y : A, R x y -> x = y

    left_quasireflexive   : forall x y : A, R x y -> R x x
    right_quasireflexive  : forall x y : A, R x y -> R y y
    quasireflexive        : forall x y : A, R x y -> R x x /\ R y y

    symmetric             : forall x y : A, R x y -> R y x
    antisymmetric         : forall x y : A, R x y -> R y x -> False
    weakly_antisymmetric  : forall x y : A, R x y -> R y x -> x = y
    asymmetric            : exists x y : A, R x y /\ ~ R y x
(*  not_antisymmetric     : exists x y : A, R x y /\ R y x *)

    transitive            : forall x y z : A, R x y -> R y z -> R x z
    antitransitive        : forall x y z : A, R x y -> R y z -> R x z -> False
(*  weakly_antitransitive : forall x y z : A, R x y -> R y z -> R x z -> x = y /\ y = z *)
    cotransitive          : forall {x z : A}, R x z -> forall y : A, R x y \/ R y z
    quasitransitive       : Transitive (AsymmetricPart R)
(*  trans. of incomp.     : TOOD *)
(*  intransitive          : exists x y z : A, R x y /\ R y z /\ ~ R x z *)

    circular              : forall x y z : A, R x y -> R y z -> R z x
    right_euclidean       : forall x y z : A, R x y -> R x z -> R y z
    left_euclidean        : forall x y z : A, R y x -> R z x -> R y z
    diamond               : forall x y z : A, R x y -> R x z -> ∃ w : A, R y w /\ R z w
    locally_confluent     : forall x y z : A, R x y -> R x z -> ∃ w : A, R* y w /\ R* z w
    confluent             : forall x y z : A, R* x y -> R* x z -> ∃ w : A, R* y w /\ R* z w

    dense                 : forall x y : A, R x y -> exists z : A, R x z /\ R z y

    total                 : forall x y : A, R x y \/ R y x
    weakly_total          : forall x y : A, ~ R x y -> R y x

    trichotomous          : forall x y : A, R x y \/ x = y \/ R y x
    weakly_trichotomous   : forall x y : A, x <> y -> R x y \/ R y x
    connected             : forall x y : A, ~ R x y /\ ~ R y x -> x = y

    weakly_extensional    : forall x y : A, (forall t : A, R t x <-> R t y) -> x = y

    well_founded          : forall x : A, Acc R x
    ill_founded           : exists x : A, Inaccessible R x *)

(** * Cosik o systemach przepisywania *)

(** ** Właściwość diamentu *)

Class Diamond {A : Type} (R : rel A) : Prop :=
{
    diamond :
      forall x y z : A,
        R x y -> R x z ->
          exists w : A, R y w /\ R z w
}.

Instance Diamond_RTrue :
  forall A : Type, Diamond (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Diamond_RFalse :
  forall A : Type, Diamond (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Diamond_eq :
  forall A : Type, Diamond (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Diamond_lt :
  Diamond lt.
(* begin hide *)
Proof.
  split; intros. exists (1 + y + z). lia.
Qed.
(* end hide *)

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

(** ** Domknięcie zwrotnoprzechodnie *)

Inductive rtc {A : Type} (R : rel A) : rel A :=
(*     | rtc_step  : forall x y : A, R x y ->  *)
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

Instance Reflexive_rtc :
  forall {A : Type} (R : rel A),
    Reflexive (rtc R).
(* begin hide *)
Proof.
  intros A R; split. constructor.
Qed.
(* end hide *)

Instance Transitive_rtc :
  forall {A : Type} (R : rel A),
    Transitive (rtc R).
(* begin hide *)
Proof.
  intros A R; split; intros x y z rxy ryz; revert z ryz.
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

(** ** Relacje lokalnie konfluentne *)

Class LocallyConfluent {A : Type} (R : rel A) : Prop :=
  locally_confluent :
    forall x y z : A, R x y -> R x z -> exists w : A, rtc R y w /\ rtc R z w.

Instance LocallyConfluent_RTrue :
  forall A : Type, LocallyConfluent (@RTrue A A).
(* begin hide *)
Proof.
  unfold LocallyConfluent.
  intros A x y z _ _.
  exists x. split; apply rtc_step; compute; trivial.
Qed.
(* end hide *)

Instance LocallyConfluent_RFalse :
  forall A : Type, LocallyConfluent (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance LocallyConfluent_eq :
  forall A : Type, LocallyConfluent (@eq A).
(* begin hide *)
Proof.
  unfold LocallyConfluent.
  intros A x y z -> ->.
  exists z. split; apply rtc_refl.
Qed.
(* end hide *)

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

Instance Confluent_RTrue :
  forall A : Type, Confluent (@RTrue A A).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A x y z _ _.
  exists x. split; apply rtc_step; compute; trivial.
Qed.
(* end hide *)

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