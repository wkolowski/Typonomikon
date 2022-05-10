Require Import StrictProp.

Lemma SProp_is_not_a_strict_proposition :
  forall P : SProp, ~ @eq Type (Box P) SProp.
Proof.
  intros P H.
  pose (prop T := forall t1 t2 : T, t1 = t2).
  assert (prop (Box P)). red. intros [] []. reflexivity.
  assert (prop SProp). rewrite <- H. assumption.
  red in H1. specialize (H1 sUnit sEmpty).
  enough sEmpty.
  - destruct H2.
  - rewrite <- H1. constructor.
Qed.

(*
Inductive seq {A : SProp} (x : A) : A -> SProp :=
| srefl : seq x x.

Goal forall P : SProp, ~ @eq Type P SProp.
Proof.
  intros P H.
  pose (prop T := forall t1 t2 : T, eq t1 t2).
  assert (prop (Box P)). red. intros [] []. reflexivity.
  assert (forall p1 p2 : P, p1 = p2). reflexivity.
  assert (prop SProp). rewrite <- H. exact H1.
  red in H2. specialize (H2 sUnit sEmpty).
  enough sEmpty.
  - destruct H3.
  - destruct H2. constructor.
Qed.
*)