Unset Guard Checking.
Fixpoint f (x : unit) : False := f x.
Set Guard Checking.

Theorem hehe : False.
Proof.
  apply f.
  exact tt.
Defined.

Lemma hehe_spec : hehe = f tt.
Proof.
  unfold hehe.
  reflexivity.
Qed.