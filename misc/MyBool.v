Inductive bool : Type := true | false.

Ltac solve_bool := intros; match goal with
    | b : bool |- _ => destruct b; solve_bool
    | _ => auto
end.

Fixpoint negb (b : bool) : bool := match b with
    | true => false
    | false => true
end.

Fixpoint andb (b1 b2 : bool) : bool := match b1 with
    | true => b2
    | false => false
end.

Fixpoint orb (b1 b2 : bool) : bool := match b1 with
    | true => true
    | false => b2
end.

Fixpoint implb (b1 b2 : bool) : bool := match b1 with
    | true => b2
    | false => true
end.

Definition nandb (b1 b2 : bool) : bool := negb (andb b1 b2).
Definition norb (b1 b2 : bool) : bool := negb (orb b1 b2).
Definition andb3 (b1 b2 b3 : bool) : bool := andb b1 (andb b2 b3).

Fixpoint evenb (n : nat) : bool := match n with
    | 0 => true
    | S 0 => false
    | S (S n') => evenb n'
end.

Definition oddb (n : nat) : bool := negb (evenb n).

Definition negb' (b : bool) := if b then false else true.

Fixpoint beq (b1 b2 : bool) : bool := match b1, b2 with
    | false, false => true
    | false, true => false
    | true, false => false
    | true, true => true
end.

Theorem andb_eq_orb : forall b c : bool, andb b c = orb b c -> b = c.
solve_bool.
Restart.
intros b c. destruct b.
Case "b = true". destruct c.
    SCase "c = true". reflexivity.
    SCase "c = false". simpl. intro. rewrite H. trivial.
Case "b = false". simpl. intro. apply H. 
Qed.

Theorem negb_inv : forall b : bool, negb (negb b) = b.
solve_bool.
Restart.
intro. destruct b; reflexivity.
Qed.

(* Każda funkcjowa boolowska, która jest identycznością, jest inwolucją. *)
Theorem identity_fn_applied_twice : forall f : bool -> bool,
    (forall x : bool, f x = x) -> forall b : bool, f (f b) = b.
solve_bool; repeat rewrite H; trivial.
Restart.
intros. rewrite H, H. trivial.
Qed.

(* Każda funkcjowa boolowska, która jest negacją, jest inwolucją. *)
Theorem negation_fn_applied_twice : forall f : bool -> bool,
    (forall x : bool, f x = negb x) -> forall b : bool, f (f b) = b.
solve_bool; repeat rewrite H; trivial.
Restart.
intros. rewrite H, H. destruct b; reflexivity.
Qed.

Theorem andb_true_elim1 : forall b c : bool, andb b c = true -> b = true.
solve_bool.
Restart.
intros. destruct b.
Case "b = true". reflexivity.
Case "b = false". rewrite <- H. reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
solve_bool.
Restart.
intros. destruct c.
Case "c = true". reflexivity.
Case "c = false".
    rewrite <- H. destruct b.
    SCase "b = false". reflexivity.
    SCase "b = true". reflexivity.
Qed.

Theorem andb_true_elim : forall b c : bool,
    andb b c = true -> b = true /\ c = true.
solve_bool.
Restart.
intros. split.
Case "Left". apply andb_true_elim1 with c. apply H.
Case "Right". apply andb_true_elim2 with b. apply H.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
solve_bool.
Restart.
intro. destruct b.
Case "b = false". reflexivity.
Case "b = true". reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb (andb b c) (orb (negb b) (negb c)) = true.
solve_bool.
Restart.
intros. destruct b.
Case "b = true". simpl.
assert (H : orb c (negb c) = true).
    SCase "Proof of assertion". destruct c.
        SSCase "c = true". reflexivity.
        SSCase "c = false". reflexivity.
apply H.
Case "b = false". reflexivity.
Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
solve_bool; discriminate.
Restart.
destruct b.
Case "b = true". discriminate.
Case "b = false". discriminate.
Qed.

Section ex7_6.

Definition bool_xor (p q : bool) : bool := match p, q with
    | true, false => true
    | false, true => true
    | _, _ => false
end.

Definition bool_and (p q : bool) : bool := match p with
    | true => q
    | _ => false
end.

Definition bool_or (p q : bool) : bool := match p with
    | true => true
    | _ => q
end.

Definition bool_eq (p q : bool) : bool := match p, q with
    | true, true => true
    | false, false => true
    | _, _ => false
end.

Definition bool_not (b : bool) : bool := match b with
    | true => false
    | false => true
end.

Theorem ex7_6_1 : forall b b' : bool, bool_xor b b' = bool_not (bool_eq b b').
solve_bool.
Qed.

Theorem ex7_6_2 : forall b b' : bool, bool_not (bool_and b b') =
    bool_or (bool_not b) (bool_not b').
solve_bool.
Qed.

Theorem ex7_6_3 : forall b : bool, bool_not (bool_not b) = b.
solve_bool.
Qed.

Theorem ex7_6_4 : forall b : bool, bool_or b (bool_not b) = true.
solve_bool.
Qed.

Theorem ex7_6_5 : forall b b' : bool, bool_eq b b' = true -> b = b'. 
solve_bool.
Qed.

Theorem ex7_6_6 : forall b b' : bool,
    bool_not (bool_or b b') = bool_and (bool_not b) (bool_not b').
solve_bool.
Qed.

Theorem ex7_6_7 : forall b1 b2 b3 : bool,
    bool_or (bool_and b1 b3) (bool_and b2 b3) = bool_and (bool_or b1 b2) b3.
solve_bool.
Qed.

End ex7_6.
