Set Definitional UIP.

Inductive seq {A : Type} (x : A) : A -> SProp :=
| srefl : seq x x.

(*
Inductive seq {A : Type} : A -> A -> SProp :=
| srefl : forall x : A, seq x x.
*)

Axiom all_eq : forall (P Q : SProp), P -> Q -> seq P Q.

Definition transport (P Q : SProp) (x : P) (y : Q) : Q :=
match all_eq P Q x y with
| srefl _ => x
end.

Definition top : SProp :=
  forall P : SProp, P -> P.

Definition c : top :=
  fun (P : SProp) (p : P) =>
    transport
    (top -> top)
    P
    (fun x : top => x (top -> top) (fun x => x) x)
    p.

Compute c.

Timeout 1 Eval lazy in c (top -> top) (fun x => x) c.
