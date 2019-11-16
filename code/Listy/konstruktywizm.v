Require Import D5.

Fixpoint different {A : Type} (l1 l2 : list A) : Prop :=
match l1, l2 with
    | [], [] => False
    | [], _ => True
    | _, [] => True
    | h1 :: t1, h2 :: t2 => h1 <> h2 \/ different t1 t2
end.

Lemma different_spec :
  forall (A : Type) (l1 l2 : list A),
    l1 <> l2 <-> different l1 l2.
Proof.
  induction l1 as [| h1 t1]; cbn.
    destruct l2 as [| h2 t2]; cbn.
      tauto.
      firstorder congruence.
    destruct l2 as [| h2 t2]; cbn.
      firstorder congruence.
      split.
        Focus 2. destruct 1.
          congruence.
          destruct (IHt1 t2). firstorder congruence.
        intro. assert (~ (h1 = h2 /\ t1 = t2)).
          firstorder congruence.
Abort.