Inductive CthulhuIC (I C : Type -> Type) (A : Type) : Type :=
| E
| N : A -> C A -> I A -> CthulhuIC I C A.

Arguments E {I C A}.
Arguments N {I C A} _ _ _.

Inductive CthulhuI (C : Type -> Type) (A : Type) : Type :=
| In : CthulhuIC (CthulhuI C) C A -> CthulhuI C A.

Arguments In {C A} _.

CoInductive Cthulhu (A : Type) : Type := MkC
{
  Out : CthulhuI Cthulhu A;
}.

Arguments MkC {A} _.
Arguments Out {A} _.

Fixpoint mapI
  {C : Type -> Type} (map : forall {A B : Type}, (A -> B) -> C A -> C B)
  {A B : Type} (f : A -> B)
  (c : CthulhuI C A) : CthulhuI C B :=
match c with
| In E => In E
| In (N v l r) => In (N (f v) (map f l) (mapI (@map) f r))
end.

Fail
CoFixpoint map {A B : Type} (f : A -> B) (c : Cthulhu A) : Cthulhu B :=
{|
  Out :=
    match Out c with
    | In E => In E
    | In (N v l r) => In (N (f v) (map f l) (mapI (@map) f r))
    end;
|}.

Fail
Definition map {A B : Type} (f : A -> B) (c : Cthulhu A) : Cthulhu B :=
  cofix map (c : Cthulhu A) : Cthulhu B :=
  match Out c with
  | In E => MkC (In E)
  | In (N v l r) => MkC (In
      (fix mapI (ci : CthulhuI Cthulhu A) : CthulhuI Cthulhu B :=
      match ci with
      | In E => In E
      | In (N v l r) => In (N (f v) (map l) (mapI r))
      end) r)
  end.