Inductive sFalse : SProp := .

Goal
  forall (A : Type) (f g : A -> sFalse),
    f = g.
Proof.
  reflexivity.
Abort.

Goal
  forall (A : Type) (f g : sFalse -> A),
    f = g.
Proof.
  intros.
  change f with (fun x => f x).
  change g with (fun x => g x).
  reflexivity.

Abort.

Goal
  forall (A : Type) (f g : A -> False),
    f = g.
Proof.
  intros.
  Fail reflexivity.
Abort.

Goal
  forall (A : Type) (f g : False -> A),
    f = g.
Proof.
  intros.
  Fail reflexivity.
Abort.

Goal
  forall (n : nat) (p1 p2 : n <> 0),
    p1 = p2.
Proof.
  induction n as [| n']; cbn; intros.
    contradict p1. reflexivity.
    

Qed.