Set Definitional UIP.

Inductive seq {A : Type} (x : A) : A -> SProp :=
| srefl : seq x x.

(*
Inductive seq {A : Type} : A -> A -> SProp :=
| srefl : forall x : A, seq x x.
*)

Axiom all_eq : forall (P Q : Prop), P -> Q -> seq P Q.

Definition transport (P Q : Prop) (x : P) (y : Q) : Q :=
match all_eq P Q x y with
| srefl _ => x
end.

Definition top : Prop :=
  forall P : Prop, P -> P.

Definition c : top :=
  fun (P : Prop) (p : P) =>
    transport
    (top -> top)
    P
    (fun x : top => x (top -> top) (fun x => x) x)
    p.

Compute c.

Fail Timeout 1 Eval lazy in c (top -> top) (fun x => x) c.
