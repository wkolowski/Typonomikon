Require Import Div2.

SearchAbout div2.


Fixpoint evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

Require Import ZArith.
Search Z.

Fixpoint quickMul (fuel n m : nat) : nat :=
match fuel with
    | 0 => 42
    | S fuel' => match n with
        | 0 => 0
        | _ => let res := quickMul fuel' (div2 n) m in
            if evenb n then res + res else (m + res) + res
        end
end.

Time Eval compute in 430 * 220.
Time Eval compute in quickMul 1000 430 220.

Function qm (n m : nat) : nat :=
match n with
    | 0 => 0
    | _ => let r := qm (div2 n) m in
        if evenb n then 2 * r else m + 2 * r
end.


