Require Import Nat Arith Lia.

From Typonomikon Require Import D1n.

Unset Guard Checking.
Fixpoint div' (n m : nat) {struct n} : nat :=
  if n <? (S m) then 0 else S (div' (n - S m) m).
Set Guard Checking.

Lemma div'_eq :
  forall n m : nat,
    div' n m = if n <? (S m) then 0 else S (div' (n - S m) m).
Proof.
  now intros [] [].
Qed.

Definition mydiv (n m : nat) : option nat :=
match m with
| 0 => None
| S m' => Some (div' n m')
end.

Print div.
Print div'.


Lemma div'_spec :
  forall n m : nat,
    div' n m = div n m.
Proof.
  intros n m.
  apply div_ind; clear n m; intros n m Hlt.
  - rewrite div'_eq.
    apply Nat.ltb_lt in Hlt.
    now rewrite Hlt.
  - intros IH.
    rewrite div'_eq.
    unfold ge in Hlt.
    apply Nat.ltb_ge in Hlt.
    now rewrite Hlt, IH.
Qed.

Compute mydiv 10 6.