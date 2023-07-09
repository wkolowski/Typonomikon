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

Module PartialInfSet.

Private Inductive PartialInfSet (A : Type) : Type :=
| Undefined : PartialInfSet A
| Defined   : A -> PartialInfSet A -> PartialInfSet A.

Arguments Undefined {A}.
Arguments Defined   {A} _ _.

Axiom swap :
  forall {A : Type} (x y : A) (s : PartialInfSet A),
    Defined x (Defined y s) = Defined y (Defined x s).

Axiom idem :
  forall {A : Type} (x : A) (s : PartialInfSet A),
    Defined x (Defined x s) = Defined x s.

Section rec.

Context
  (A : Type)
  (P : Type)
  (Undefined' : P)
  (Defined' : A -> P -> P).

Fixpoint PartialInfSet_rec
  (swap'  : forall (x y : A) (s : P), Defined' x (Defined' y s) = Defined' y (Defined' x s))
  (idem'  : forall (x : A) (s : P), Defined' x (Defined' x s) = Defined' x s)
  (s : PartialInfSet A) : P :=
match s with
| Undefined => Undefined'
| Defined x s' => Defined' x (PartialInfSet_rec swap' idem' s')
end.

Context
  (swap' : forall (x y : A) (s : P), Defined' x (Defined' y s) = Defined' y (Defined' x s))
  (idem' : forall (x : A) (s : P), Defined' x (Defined' x s) = Defined' x s).

Axiom PartialInfSet_rec_swap :
  forall (x y : A) (s : PartialInfSet A),
    ap (PartialInfSet_rec swap' idem') (swap x y s) = swap' x y (PartialInfSet_rec swap' idem' s).

Axiom PartialInfSet_rec_idem :
  forall (x : A) (s : PartialInfSet A),
    ap (PartialInfSet_rec swap' idem') (idem x s) = idem' x (PartialInfSet_rec swap' idem' s).

End rec.

Section ind.

Context
  (A : Type)
  (P : PartialInfSet A -> Prop)
  (Undefined' : P Undefined)
  (Defined' : forall (x : A) {s : PartialInfSet A}, P s -> P (Defined x s)).

Fixpoint PartialInfSet_ind (s : PartialInfSet A) : P s :=
match s with
| Undefined => Undefined'
| Defined x s' => Defined' x s' (PartialInfSet_ind s')
end.

End ind.

Section rect.

Context
  (A : Type)
  (P : PartialInfSet A -> Type)
  (Undefined' : P Undefined)
  (Defined' : forall (x : A) {s : PartialInfSet A}, P s -> P (Defined x s))
  (Swap' :=
    forall (x y : A) (s : PartialInfSet A) (s' : P s),
      transport _ (swap x y s) (Defined' x (Defined' y s')) = Defined' y (Defined' x s'))
  (swap' : Swap')
  (Idem' :=
    forall (x : A) (s : PartialInfSet A) (s' : P s),
      transport _ (idem x s) (Defined' x (Defined' x s')) = Defined' x s')
  (idem' : Idem').

Fixpoint PartialInfSet_rect
  (swap' : Swap') (idem' : Idem') (s : PartialInfSet A) : P s :=
match s with
| Undefined => Undefined'
| Defined x s' => Defined' x s' (PartialInfSet_rect swap' idem' s')
end.

Axiom PartialInfSet_rect_swap :
  forall (x y : A) (s : PartialInfSet A),
    apd (PartialInfSet_rect swap' idem') (swap x y s) = swap' x y s (PartialInfSet_rect swap' idem' s).

Axiom PartialInfSet_rect_idem :
  forall (x : A) (s : PartialInfSet A),
    apd (PartialInfSet_rect swap' idem') (idem x s) = idem' x s (PartialInfSet_rect swap' idem' s).

End rect.

End PartialInfSet.