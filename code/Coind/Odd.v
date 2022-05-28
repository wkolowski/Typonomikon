From Typonomikon Require Import F2.

CoInductive Odd (c : conat) : Type :=
{
    Oz  : c = zero -> False;
    Oss : forall {c' : conat}, c = succ (succ c') -> Odd c';
}.

Lemma p0 : Odd zero -> False.
Proof.
  destruct 1.
  apply Oz0.
  reflexivity.
Defined.

Lemma p2 : Odd (succ (succ zero)) -> False.
Proof.
  destruct 1.
  specialize (Oss0 _ eq_refl).
  apply p0.
  assumption.
Defined.

