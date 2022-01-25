(* It is known that [f = g] is undecidable in Coq. *)
Definition f (n : nat) := n.
Definition g (n : nat) := n + 0.

Axiom p1 : f = g.
Axiom p2 : f = g.

Axiom nonirrelevance : p1 <> p2.
