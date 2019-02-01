Require Import ZArith.

CoInductive stream (A : Type) : Type :=
    | Cons : A -> stream A -> stream A.

Arguments Cons [A] _ _.

CoFixpoint rand (seed n1 n2 : Z) : stream Z :=
  let seed' := Zmod seed n2
  in Cons seed' (rand (seed' * n1) n1 n2).

Fixpoint take {A : Type} (n : nat) (s : stream A) : list A :=
match n, s with
    | 0, _ => nil
    | S n', Cons h t => h :: take n' t
end.

Compute take 10 (rand 1235 234567890 87654321).