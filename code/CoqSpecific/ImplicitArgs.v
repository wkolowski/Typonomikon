Require Import Nat.

Parameter n : nat.

About sub.

Eval cbn in sub 0 0.
Eval cbn in sub 0 2.
Eval cbn in sub 2 1.

Arguments sub !n !m.

Eval cbn in sub n 0.
Eval cbn in sub 0 n.
Eval cbn in sub n 1.
Eval cbn in sub (S n) 1.

Arguments sub !n m.

Eval cbn in sub n 0.
Eval cbn in sub 0 n.
Eval cbn in sub n 1.
Eval cbn in sub (S n) 1.

Arguments sub n !m.

Eval cbn in sub n 0.
Eval cbn in sub 0 n.
Eval cbn in sub n 1.
Eval cbn in sub (S n) 1.

Arguments sub n m : simpl nomatch.

Eval cbn in sub n 0.
Eval cbn in sub 0 n.
Eval cbn in sub n 1.
Eval cbn in sub (S n) 1.