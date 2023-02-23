From Typonomikon Require Import ApproximateCoinductive.

Set Primitive Projections.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) : P x -> P y :=
match p with
| eq_refl _ => fun u : P x => u
end.

Definition ap
  {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
match p with
| eq_refl => eq_refl
end.

Definition apd
  {A : Type} {P : A -> Type} (f : forall x : A, P x) {x y : A} (p : x = y)
  : transport P p (f x) = (f y) :=
match p with
| eq_refl => eq_refl
end.

Module InfSetF.

Record InfSetF (F : Type -> Type) (A : Type) : Type := ConsF
{
  hd : A;
  tl : F A;
}.

Arguments ConsF {F A} _ _.
Arguments hd {F A} _.
Arguments tl {F A} _.

Axiom swap :
  forall {F : Type -> Type} {A : Type} (x y : A) (s : InfSetF F A),
    ConsF x (ConsF y s) = ConsF y (ConsF x s).

Section case.

Context
  (F : Type -> Type)
  (A : Type)
  (P : Type)
  (ConsF' : A -> P -> P).

Definition InfSetF_case
  (swap'  : forall (x y : A) (s : P), ConsF' x (ConsF' y s) = ConsF' y (ConsF' x s))
  (s : InfSetF F A) : P :=
match s with
| ConsF x s' => ConsF' x s'
end.

Context
  (swap'  : forall (x y : A) (s : P), ConsF' x (ConsF' y s) = ConsF' y (ConsF' x s)).

Axiom InfSetF_rec_swap :
  forall (x y : A) (s : InfSetF A),
    ap (InfSetF_rec swap' idem') (swap x y s) = swap' x y (InfSetF_rec swap' idem' s).

Axiom InfSetF_rec_idem :
  forall (x : A) (s : InfSetF A),
    ap (InfSetF_rec swap' idem') (idem x s) = idem' x (InfSetF_rec swap' idem' s).

End rec.

End InfSetF.

CoInductive Stream (A : Type) : Type := MkStream
{
  out : StreamF Stream A;
}.

Arguments MkStream {A} _.
Arguments out {A} _.

Notation Stream' A := (StreamF Stream A).
Notation Cons h t := (MkStream (ConsF h t)).

Record BisimF
  {A1 A2 : Type} (R : A1 -> A2 -> Prop)
  {F1 F2 : Type -> Type} (Knot : F1 A1 -> F2 A2 -> Prop)
  (s1 : StreamF F1 A1) (s2 : StreamF F2 A2) : Prop :=
{
  BisimF_hd : R (hd s1) (hd s2);
  BisimF_tl : Knot (tl s1) (tl s2);
}.

CoInductive Bisim {A : Type} (s1 s2 : Stream A) : Prop :=
{
  Bisim_out : BisimF eq Bisim (out s1) (out s2);
}.

Fixpoint PartialStream (A : Type) (n : nat) : Type :=
match n with
| 0 => unit
| S n' => StreamF (fun A => PartialStream A n') A
end.

Definition Undefined {A : Type} : PartialStream A 0 := tt.

Definition Defined
  {n : nat} {A : Type} (ps : PartialStream A (S n)) : PartialStream A (S n) := ps.





