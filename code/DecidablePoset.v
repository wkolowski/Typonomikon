Inductive Order : Type :=
    | Lt
    | Eq
    | Gt
    | Nc.

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
  - intro. specialize (refl x x). specialize (antisym x x). intuition congruence.
  - eapply trans; eassumption.
  - specialize (antisym x y). intuition congruence.
  - destruct (cmp x y) eqn: Hcmp; [left | | |]; try right; congruence.
Defined.

Lemma StrictPoset_to_DecidablePoset :
  forall {A : Type}, StrictPoset A -> DecidablePoset A.
Proof.
  intros A [R antirefl trans antisym dec].
  split with (
    fun x y =>
    match dec x y, dec y x with
        | left _ , left _  => Nc
        | left _ , right _ => Lt
        | right _, left _  => Gt
        | right _, right _ => Eq
    end);
  intros.
  - destruct (dec x y), (dec y x).
    + intuition; try congruence. subst. specialize (antirefl _ r). contradiction.
    + intuition; try congruence.
    + intuition; try congruence.
    + intuition; try congruence.
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
        o <> Nc -> cmp x y = o -> cmp y z = o -> cmp x z = o;
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

Require Import Setoid.

Lemma DecidablePoset_to_Poset :
  forall {A : Type}, DecidablePoset A -> Poset A.
Proof.
  intros A [cmp refl trans antisym].
  split with (fun x y => cmp x y = Lt \/ cmp x y = Eq); intros.
  - right. now apply refl.
  - intuition.
    + left. eapply trans; eauto. congruence.
    + left. rewrite refl in *. congruence.
    + left. rewrite refl in *. congruence.
    + right. rewrite refl in *. congruence.
  - intuition.
    + apply antisym in H. congruence.
    + apply antisym in H1. congruence.
    + apply antisym in H. congruence.
    + rewrite refl in *. congruence.
  - destruct (cmp x y) eqn: Hcmp.
    + left. now left.
    + left. now right.
    + right. intro. intuition congruence.
    + right. intro. intuition congruence.
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
        | right _, right _ => Nc
    end);
  intros.
  - destruct (dec x y), (dec y x).
    + intuition; try congruence.
    + intuition; try congruence.
    + intuition; try congruence.
    + intuition; try congruence. subst. specialize (refl y). contradiction.
  - destruct (dec x z), (dec z x).
    + specialize (antisym _ _ r r0); subst. destruct (dec z y), (dec y z); intuition congruence.
    + destruct (dec x y), (dec y x), (dec y z), (dec z y); intuition; subst;
      repeat match goal with
          | H : R ?x ?y, H' : R ?y ?x |- _ => pose (antisym _ _ H H'); clearbody e; subst; clear H H'
      end; intuition; try congruence.
      clear H H1. assert (R x y) by (eapply trans; eauto). contradiction.
    + destruct (dec x y), (dec y x), (dec y z), (dec z y); intuition; subst;
      repeat match goal with
          | H : R ?x ?y, H' : R ?y ?x |- _ => pose (antisym _ _ H H'); clearbody e; subst; clear H H'
      end; intuition; try congruence.
      clear H H1. assert (R x z) by (eapply trans; eauto). contradiction.
    + destruct (dec x y), (dec y x), (dec y z), (dec z y); intuition; subst;
      repeat match goal with
          | H : R ?x ?y, H' : R ?y ?x |- _ => pose (antisym _ _ H H'); clearbody e; subst; clear H H'
          | H : R ?x ?x -> False |- _ => specialize (refl x); contradiction
      end; intuition; try congruence.
      * assert (R x z) by (eapply trans; eauto). contradiction.
      *  assert (R z x) by (eapply trans; eauto). contradiction.
  - destruct (dec x y), (dec y x); intuition congruence.
Defined.