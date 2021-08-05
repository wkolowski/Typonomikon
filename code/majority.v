Definition majority (a b c : bool) : bool :=
match a, b, c with
    | true , true , true  => true
    | x    , false, true  => x
    | true , y    , false => y
    | false, true , z     => z
    | false, false, false => false
end.

Require Import Bool.

Lemma majority_spec :
  forall a b c : bool,
    majority a b c = (a || b) && (b || c) && (c || a).
Proof.
  destruct a, b, c; cbn; reflexivity.
Qed.