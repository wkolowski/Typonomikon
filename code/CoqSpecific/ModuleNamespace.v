Inductive sometype : Type :=.

Module sometype.

Definition elim := sometype_ind.

End sometype.

Print sometype.elim.
(* ===> sometype_ind : forall (P : sometype -> Prop) (s : sometype), P s *)