Set Definitional UIP.

Definition False : SProp := forall A, A.

Definition Not (A : SProp) : SProp := A -> False.

Definition True : SProp := Not False.

Definition delta : True := fun z => z True z.

Inductive seq {A : Type} (x : A) : A -> SProp :=
| srefl : seq x x.

Definition cast (A B : SProp) (p : seq A B) : A -> B :=
match p with
| srefl _ => fun a => a
end.

Definition omega : Not (forall A B : SProp, seq A B) :=
  fun h A => cast _ _ (h True A) delta.

Definition Omega : Not (forall A B : SProp, seq A B) :=
  fun h => delta (omega h).

Compute Omega.

(* Fail Timeout 1 Eval lazy in Omega. *)