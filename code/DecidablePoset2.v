Require Import Setoid.

Inductive Order' : Type :=
| Lt'
| Eq'
| Gt'.

Definition Order : Type := option Order'.

Definition Lt : Order := Some Lt'.
Definition Eq : Order := Some Eq'.
Definition Gt : Order := Some Gt'.

Module FirstTry.

Class DecidablePoset (A : Type) : Type :=
{
  cmp : A -> A -> Order;
  cmp_refl :
    forall x y : A, cmp x y = Eq <-> x = y;
  cmp_trans :
    forall x y z : A,
      cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt;
  cmp_antisym :
    forall x y : A, cmp x y = Lt <-> cmp y x = Gt;
}.

Class StrictPoset (A : Type) : Type :=
{
  rel : A -> A -> Prop;
  rel_antirefl :
    forall x : A, ~ rel x x;
  rel_trans :
    forall x y z : A, rel x y -> rel y z -> rel x z;
  rel_antisym :
    forall x y : A, rel x y -> rel y x -> False;
  rel_dec :
    forall x y : A, {rel x y} + {~ rel x y};
}.

Lemma DecidablePoset_to_StrictPoset :
  forall {A : Type}, DecidablePoset A -> StrictPoset A.
Proof.
  intros A [cmp refl trans antisym].
  split with (fun x y => cmp x y = Lt); intros.
  - intro. specialize (refl x x). specialize (antisym x x).
    unfold Lt, Gt in *. intuition congruence.
  - eapply trans; eassumption.
  - specialize (antisym x y). unfold Lt, Gt in *. intuition congruence.
  - unfold Lt. destruct (cmp x y) as [[| |] |] eqn: Hcmp; [left | | |]; try right; congruence.
Defined.

Lemma StrictPoset_to_DecidablePoset :
  forall {A : Type}, StrictPoset A -> DecidablePoset A.
Proof.
  intros A [R antirefl trans antisym dec].
  split with (
    fun x y =>
    match dec x y, dec y x with
    | left _ , left _  => None
    | left _ , right _ => Lt
    | right _, left _  => Gt
    | right _, right _ => Eq
    end);
  intros.
  - destruct (dec x y), (dec y x).
    + split; inversion 1; subst. elim (antirefl y). assumption.
    + unfold Lt, Eq. intuition; try congruence.
    + unfold Lt, Eq, Gt. intuition; try congruence.
    + intuition.
Abort.

End FirstTry.

Module SecondTry.

Class DecidablePoset (A : Type) : Type :=
{
  cmp : A -> A -> Order;
  cmp_refl :
    forall x y : A, cmp x y = Eq <-> x = y;
  cmp_trans :
    forall (x y z : A) (o : Order),
      o <> None -> cmp x y = o -> cmp y z = o -> cmp x z = o;
  cmp_antisym :
    forall x y : A, cmp x y = Lt <-> cmp y x = Gt;
}.

Class Poset (A : Type) : Type :=
{
  rel : A -> A -> Prop;
  rel_refl :
    forall x : A, rel x x;
  rel_trans :
    forall x y z : A, rel x y -> rel y z -> rel x z;
  rel_antisym :
    forall x y : A, rel x y -> rel y x -> x = y;
  rel_dec :
    forall x y : A, {rel x y} + {~ rel x y};
}.

Lemma DecidablePoset_to_Poset :
  forall {A : Type}, DecidablePoset A -> Poset A.
Proof.
  intros A [cmp refl trans antisym].
  split with (fun x y => cmp x y = Lt \/ cmp x y = Eq); intros.
  - right. now apply refl.
  - intuition.
    + left. eapply trans; eauto. inversion 1.
    + left. rewrite refl in *. congruence.
    + left. rewrite refl in *. congruence.
    + right. rewrite refl in *. congruence.
  - intuition.
    + apply antisym in H. unfold Lt, Gt in *. congruence.
    + apply antisym in H1. unfold Lt, Eq, Gt in *. congruence.
    + apply antisym in H. unfold Lt, Eq, Gt in *. congruence.
    + rewrite refl in *. congruence.
  - destruct (cmp x y) as [[] |] eqn: Hcmp.
    + left. now left.
    + left. now right.
    + right. unfold Lt, Eq, Gt. intuition congruence.
    + right. unfold Lt, Eq, Gt. intuition congruence.
Defined.

Lemma Poset_to_DecidablePoset :
  forall {A : Type}, Poset A -> DecidablePoset A.
Proof.
  intros A [R refl trans antisym dec].
  split with (
    fun x y =>
    match dec x y, dec y x with
    | left _ , left _  => Eq
    | left _ , right _ => Lt
    | right _, left _  => Gt
    | right _, right _ => None
    end);
  intros.
  - destruct (dec x y), (dec y x).
    + intuition; try congruence.
    + unfold Lt, Eq. intuition; try congruence.
    + unfold Eq, Gt. intuition; try congruence.
    + intuition; try congruence.
      * inversion H.
      * elim n. subst. apply refl.
  - destruct (dec x z), (dec z x).
    + specialize (antisym _ _ r r0); subst.
      unfold Lt, Eq, Gt in *.
      destruct (dec z y), (dec y z); intuition congruence.
    + unfold Lt, Eq, Gt in *. 
      destruct (dec x y), (dec y x), (dec y z), (dec z y); intuition; subst;
      repeat match goal with
      | H : R ?x ?y, H' : R ?y ?x |- _ => pose (antisym _ _ H H'); clearbody e; subst; clear H H'
      end; intuition; try congruence.
      clear H H1. assert (R x y) by (eapply trans; eauto). contradiction.
    + unfold Lt, Eq, Gt in *. 
      destruct (dec x y), (dec y x), (dec y z), (dec z y); intuition; subst;
      repeat match goal with
      | H : R ?x ?y, H' : R ?y ?x |- _ => pose (antisym _ _ H H'); clearbody e; subst; clear H H'
      end; intuition; try congruence.
      clear H H1. assert (R x z) by (eapply trans; eauto). contradiction.
    + unfold Lt, Eq, Gt in *. 
      destruct (dec x y), (dec y x), (dec y z), (dec z y); intuition; subst;
      repeat match goal with
      | H : R ?x ?y, H' : R ?y ?x |- _ => pose (antisym _ _ H H'); clearbody e; subst; clear H H'
      | H : R ?x ?x -> False |- _ => specialize (refl x); contradiction
      end; intuition; try congruence.
      * assert (R x z) by (eapply trans; eauto). contradiction.
      *  assert (R z x) by (eapply trans; eauto). contradiction.
  - unfold Lt, Eq, Gt in *. 
    destruct (dec x y), (dec y x); intuition congruence.
Defined.

End SecondTry.