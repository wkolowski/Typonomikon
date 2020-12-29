Inductive Rec' (F : Type -> Type) (A : Type) : Type :=
    | End  : A -> Rec' F A
    | Step : F A -> Rec' F A.

Arguments End  {F A} _.
Arguments Step {F A} _.

CoInductive Rec (A : Type) : Type :=
{
    rec : Rec' Rec A;
}.

Arguments rec {A}.

Fixpoint unpackn {A : Type} (n : nat) (x : Rec A) : option A :=
match n, rec x with
    | 0   , _       => None
    | _   , End a   => Some a
    | S n', Step x' => unpackn n' x'
end.

Unset Guard Checking.
(* Fixpoint mfix {A : Type} (f : A -> A) {struct f} : A :=
  f (let x := mfix (fun x => f x) in x).
 *)

CoFixpoint mfix_aux {A : Type} (f : A -> A) : A :=
  f (mfix_aux f).

Fixpoint unpack {A : Type} (x : Rec A) {struct x} : A :=
match rec x with
    | End a => a
    | Step x' => unpack x'
end.

Set Guard Checking.

CoFixpoint Euclid' (n m : nat) : Rec nat :=
{|
    rec :=
    match n with
        | 0 => End m
        | _ => Step (Euclid' m (n - m))
    end
|}.

Compute unpackn 3 (Euclid' 4 4).

(* Compute unpack (Euclid' 0 6). *)