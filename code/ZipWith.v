Require Import F3.

Unset Guard Checking.
CoFixpoint fib : Stream nat := scons 0 (scons 1 (zipWith plus fib (tl fib))).
Set Guard Checking.

Inductive TXY (X Y A : Type) : Type :=
    | ConsXY    : A -> X -> TXY X Y A
    | ZipWithXY : (A -> A -> A) -> Y -> Y -> TXY X Y A.
(*     | YXY       : Y -> TXY X Y A. *)

Arguments ConsXY    {X Y A} _ _.
Arguments ZipWithXY {X Y A} _ _ _.
(* Arguments YXY       {X Y A} _. *)

Inductive SX (X A : Type) : Type :=
    | SConsX    : A -> X -> SX X A
    | SZipWithX : (A -> A -> A) -> SX X A -> SX X A -> SX X A.

Arguments SConsX    {X A} _ _.
Arguments SZipWithX {X A} _ _ _.

CoInductive StreamZipWith (A : Type) : Type :=
{
    Out : TXY (StreamZipWith A) (SX (StreamZipWith A) A) A;
}.

Arguments Out {A} _.

Definition ZipWith (A : Type) : Type := SX (StreamZipWith A) A.

Definition StreamZipWith_to_ZipWith {A : Type} (s : StreamZipWith A) : ZipWith A :=
match Out s with
    | ConsXY h t      => SConsX h t
    | ZipWithXY f l r => SZipWithX f l r
(*     | YXY s'          => s' *)
end.

Definition Cons {A : Type} (h : A) (t : StreamZipWith A) : StreamZipWith A :=
{|
    Out := ConsXY h t;
|}.

Definition ZipWith' {A : Type} (f : A -> A -> A) (l r : StreamZipWith A) : StreamZipWith A :=
{|
    Out := ZipWithXY f (StreamZipWith_to_ZipWith l) (StreamZipWith_to_ZipWith r);
|}.

Fixpoint whnf {A : Type} (z : ZipWith A) : A * StreamZipWith A :=
match z with
    | SConsX h t      => (h, t)
    | SZipWithX f l r =>
        let '(h1, t1) := whnf l in
        let '(h2, t2) := whnf r in
          (f h1 h2, ZipWith' f t1 t2)
end.

CoFixpoint toStream {A : Type} (z : StreamZipWith A) : Stream A :=
match Out z with
    | ConsXY h t      => scons h (toStream t)
    | ZipWithXY f l r =>
        let (h1, t1) := whnf l in
        let (h2, t2) := whnf r in
          scons (f h1 h2) (toStream (ZipWith' f t1 t2))
(*     | YXY s' => *)
(*         let (h, t) := whnf s' in scons h (toStream t) *)
end.

CoFixpoint fibSZW : StreamZipWith nat.
Proof.
  apply (Cons 0).
  refine {| Out := ZipWithXY plus _ _ |}.
    exact (StreamZipWith_to_ZipWith fibSZW).
    exact (SConsX 1 fibSZW).
Defined.

Compute take 5 (toStream fibSZW).