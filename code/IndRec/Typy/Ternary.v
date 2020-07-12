(** * Ternary logic exercise *)

Module ternary_unknown.

Inductive bool3 : Set :=
    | true : bool3
    | false : bool3
    | unknown : bool3.

Definition andb3 (b1 b2 : bool3) : bool3 :=
match b1, b2 with
    | true, true => true
    | false, _ => false
    | _, false => false
    | _, _ => unknown
end.

Definition orb3 (b1 b2 : bool3) : bool3 :=
match b1, b2 with
    | false, false => false
    | true, _ => true
    | _, true => true
    | _, _ => unknown
end.

Definition negb3 (b : bool3) : bool3 :=
match b with
    | true => false
    | false => true
    | unknown => unknown
end.

Ltac solve_bool3 := intros;
match reverse goal with
    | b : bool3 |- _ => destruct b; solve_bool3
    | _ => cbn; reflexivity
end.

Notation "b1 & b2" := (andb3 b1 b2) (at level 40).
Notation "b1 | b2" := (orb3 b1 b2) (at level 40).

Lemma andb3_comm :
  forall b1 b2 : bool3, b1 & b2 = b2 & b1.
Proof. solve_bool3. Qed.

Lemma orb3_comm :
  forall b1 b2 : bool3, b1 | b2 = b2 | b1.
Proof. solve_bool3. Qed.

Lemma andb3_dist_orb3 :
  forall b1 b2 b3 : bool3,
    b1 & (b2 | b3) = (b1 & b2) | (b1 & b3).
Proof. solve_bool3. Qed.

Lemma orb3_dist_andb3 :
  forall b1 b2 b3 : bool3,
    b1 | (b2 & b3) = (b1 | b2) & (b1 | b3).
Proof. solve_bool3. Qed.

Lemma andb3_true_neutral_l :
  forall b : bool3, andb3 true b = b.
Proof. solve_bool3. Qed.

Lemma andb3_true_neutral_r :
  forall b : bool3, andb3 b true = b.
Proof. solve_bool3. Qed.

End ternary_unknown.