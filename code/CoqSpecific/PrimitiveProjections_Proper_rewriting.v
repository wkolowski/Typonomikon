From Coq Require Import Setoid Morphisms.
Set Primitive Projections.

Record a : Type := { f : nat }.

Parameter aa : a -> a -> Prop.
Parameter nn : nat -> nat -> Prop.

Declare Instance eqv_aa : Equivalence aa.
Declare Instance eqv_nn : Equivalence nn.

#[global] Instance Proper_f : Proper (aa ==> nn) f.
Admitted.

Theorem w : forall x y : a, aa x y -> nn (f x) (f y).
Proof.
  intros x y H.
  Fail rewrite H.
  (* Tactic failure: Nothing to rewrite. *)
Restart.
  intros x y H.
  change (nn ((fun x => f x) x) ((fun y => f y) y)).
  rewrite H.
Abort.

Definition f' (x : a) : nat := f x.

#[global] Instance Proper_f' : Proper (aa ==> nn) f'.
Admitted.

Theorem w : forall x y : a, aa x y -> nn (f' x) (f' y).
Proof.
  intros x y H.
  rewrite H.
  (* Tactic failure: setoid rewrite failed: Unable to satisfy the following constraints: *)
Abort.