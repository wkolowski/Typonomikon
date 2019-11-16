Require Import D5.

Fixpoint cycles_aux {A : Type} (n : nat) (l : list A) : list (list A) :=
match n with
    | 0 => []
    | S n' => cycle n l :: cycles_aux n' l
end.

Compute cycles_aux 10 [1; 2; 3; 4; 5].

Definition cycles {A : Type} (l : list A) : list (list A) :=
  cycles_aux (length l) l.

Compute cycles [1; 2; 3; 4; 5].

Lemma Cycle_cycles :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> elem l1 (cycles l2).
Proof.
  induction 1; cbn.
    admit.
Admitted.