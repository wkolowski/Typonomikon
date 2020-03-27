Require Import Equality.

Print JMeq_eq.

Print eq.
Check eq_ind.

Print JMeq.
Check JMeq_ind.

Lemma JMeq_ind' :
  forall
    (A : Type) (x : A)
    (P : forall B : Type, B -> Prop),
      P A x -> forall (B : Type) (y : B), JMeq x y -> P B y.
Proof.
  destruct 2.
  assumption.
Qed.

Goal
  forall (A : Type) (x y : A),
    JMeq x y -> x = y.
Proof.
  intros A x y p.
  Check JMeq_ind' A x.

Abort.