From Typonomikon Require Import F3.

Unset Guard Checking.
(* CoFixpoint fib : Stream nat := scons 0 (zipWith plus fib (scons 1 fib)). *)
(* CoFixpoint fib : Stream nat := scons 0 (scons 1 (zipWith plus fib (tl fib))). *)
(* Compute take 3 fib. *)
Set Guard Checking.

Inductive CI : Type := Ind | Coind.

Inductive Base (C A : Type) : CI -> Type :=
| BCons    : forall {ci : CI}, A -> C -> Base C A ci
| BZipWith : forall {ci : CI}, (A -> A -> A) -> Base C A Ind -> Base C A Ind -> Base C A ci
| BInj     : C -> Base C A Ind.

Arguments BCons    {C A ci} _ _.
Arguments BZipWith {C A ci} _ _ _.
Arguments BInj     {C A} _.

CoInductive ZipWith (A : Type) : Type :=
{
    Out : Base (ZipWith A) A Coind;
}.

Arguments Out {A} _.

Definition Cons {A : Type} (h : A) (t : ZipWith A) : ZipWith A :=
{|
    Out := BCons h t;
|}.

Definition ZipWith' {A : Type} (f : A -> A -> A) (l r : ZipWith A) : ZipWith A :=
{|
    Out := BZipWith f (BInj l) (BInj r);
|}.

CoFixpoint fib' : ZipWith nat.
Proof.
  apply (Cons 0).
  refine (ZipWith' plus _ _).
    exact fib'.
    apply (Cons 1). exact fib'.
Defined.

(*
Fixpoint whnf {A : Type} (z : ZipWith A) : A * ZipWith A :=
match z with
| SConsX h t      => (h, t)
| SZipWithX f l r =>
        let '(h1, t1) := whnf l in
        let '(h2, t2) := whnf r in
          (f h1 h2, ZipWith' f t1 t2)
| Inj s           => whnf s
end.

CoFixpoint toStream {A : Type} (z : ZipWith A) : Stream A :=
match Out z with
| ConsXY h t      => scons h (toStream t)
| ZipWithXY f l r =>
        let (h1, t1) := whnf l in
        let (h2, t2) := whnf r in
          scons (f h1 h2) (toStream (ZipWith' f t1 t2))
(* | YXY s' => *)
(*         let (h, t) := whnf s' in scons h (toStream t) *)
end.

CoFixpoint fibSZW : ZipWith nat.
Proof.
  apply (Cons 0).
  refine {| Out := ZipWithXY plus _ _ |}.
    exact (ZipWith_to_ZipWith fibSZW).
    exact (SConsX 1 fibSZW). Show Proof.
Defined.

Compute take 5 (toStream fibSZW).
*)