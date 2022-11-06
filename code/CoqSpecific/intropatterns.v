Record wut : Type :=
{
  w1 : nat;
  w4 : nat;
  w11 : nat * nat;
}.

Goal wut -> False.
Proof.
  intros [a b c].
Restart.
  intros (a, b, c).
Restart.
  Fail intros (a & b & c).
Restart.

Abort.