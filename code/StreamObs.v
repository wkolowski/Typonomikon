Require Import Streams.

Inductive StreamObs (A B : Type) : Type :=
| result : B -> StreamObs A B
| observe : (A -> StreamObs A B) -> StreamObs A B.

Arguments result {A B} _.
Arguments observe {A B} _.

Fixpoint eval {A B : Type} (so : StreamObs A B) (s : Stream A) : B :=
match so with
| result b  => b
| observe f => eval (f (hd s)) (tl s)
end.

