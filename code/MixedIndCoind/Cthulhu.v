Inductive CthulhuCI (C I A : Type) : Type :=
| E
| N : A -> C -> I -> CthulhuCI C I A.

Arguments E {C I A}.
Arguments N {C I A} _ _ _.

Module CI.

CoInductive CthulhuC (I A : Type) : Type := MkC
{
  Out : CthulhuCI (CthulhuC I A) I A;
}.

Arguments Out {I A} _.

Inductive Cthulhu (A : Type) : Type :=
| In : CthulhuC (Cthulhu A) A -> Cthulhu A.

Arguments In {A} _.

Definition out {A : Type} (c : Cthulhu A) : CthulhuC (Cthulhu A) A :=
match c with
| In c' => c'
end.

CoFixpoint replicateI (n : nat) : CthulhuC (Cthulhu nat) nat :=
{|
  Out := N n (replicateI (S n)) (In {| Out := E; |});
|}.

Definition replicate (n : nat) : Cthulhu nat :=
  In (replicateI n).

End CI.

Module IC.

Inductive CthulhuI (C A : Type) : Type :=
| In : CthulhuCI C (CthulhuI C A) A -> CthulhuI C A.

Arguments In {C A} _.

CoInductive Cthulhu (A : Type) : Type := MkC
{
  Out : CthulhuI (Cthulhu A) A;
}.

Arguments MkC {A} _.
Arguments Out {A} _.

CoFixpoint replicate (n : nat) : Cthulhu nat :=
{|
  Out := In (N n (replicate (S n)) (In E));
|}.

End IC.

(*
Fixpoint mapI
  {C D A B : Type} (f : A -> B)
  (map : C -> D)
  (c : CthulhuI C A) : CthulhuI C B :=
match c with
| In E => In E
| In (N v l (In r)) => In (N (f v) (map l) (map r))
end.

CoFixpoint map {A B : Type} (f : A -> B) (c : Cthulhu A) : Cthulhu B :=
{|
  Out :=
    match Out c with
    | In E => In E
    | In (N v l r) => In (N (f v) (map f l) (Out (map f (MkC r))))
    end;
|}.
*)