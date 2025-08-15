Require Import Recdef.

Inductive Z : Type :=
| Zero : Z
| MinusOne : Z
| Double : Z -> Z
| DoubleSucc : Z -> Z.

Definition double (k : Z) : Z :=
match k with
| Zero     => Zero
| k'       => Double k'
end.

Definition doubleSucc (k : Z) : Z :=
match k with
| MinusOne => MinusOne
| k'       => DoubleSucc k'
end.

Function norm (k : Z) : Z :=
match k with
| Zero          => Zero
| MinusOne      => MinusOne
| Double k'     => double (norm k')
| DoubleSucc k' => doubleSucc (norm k')
end.

Lemma norm_norm :
  forall k : Z,
    norm (norm k) = norm k.
Proof.
  intros k.
  functional induction (norm k); cbn; [easy.. | |].
  - destruct (norm k'); cbn in *; [easy.. | |].
    + now rewrite IHz.
    + now rewrite IHz.
  - destruct (norm k'); cbn in *; [easy.. | |].
    + now rewrite IHz.
    + now rewrite IHz.
Qed.

Record Z' : Type :=
{
  number : Z;
  norm_number : norm number = number;
}.