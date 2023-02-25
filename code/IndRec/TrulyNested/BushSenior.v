Unset Positivity Checking.
Inductive BushSenior (A : Type) : Type :=
| E : BushSenior A
| N : A -> BushSenior (BushSenior (BushSenior A)) -> BushSenior A.
Set Positivity Checking.

Arguments E {A}.
Arguments N {A} _ _.

Unset Guard Checking.
Fixpoint map {A B : Type} (f : A -> B) (b : BushSenior A) {struct b} : BushSenior B :=
match b with
| E => E
| N x b' => N (f x) (map (map (map f)) b')
end.

Fixpoint sum (b : BushSenior nat) : nat :=
match b with
| E => 0
| N x b' => x + sum (map sum (map (map sum) b'))
end.

Fixpoint size {A : Type} (b : BushSenior A) {struct b} : nat :=
match b with
| E => 0
| N _ b' => 1 + sum (map sum (map (map size) b'))
end.

Fixpoint nums (n : nat) : BushSenior nat :=
match n with
| 0 => N 0 E
| S n' => N n (map (map nums) (map nums (nums n')))
end.

(* Compute size (nums 8). *)

Set Guard Checking.

