Inductive ListX (X A : Type) : Type :=
| Empty    : ListX X A
| NonEmpty : X -> ListX X A.

Inductive NonEmptyListY (Y A : Type) : Type :=
| Cons  : A -> Y -> NonEmptyListY Y A.

Arguments Empty    {X A}.
Arguments NonEmpty {X A} _.
Arguments Cons     {Y A} _ _.

CoInductive CoList' (A : Type) : Type :=
{
    CLOut : ListX (NonEmptyCoList A) A;
}

with NonEmptyCoList (A : Type) : Type :=
{
    NECLOut : NonEmptyListY (CoList' A) A;
}.

Arguments CLOut  {A} _.
Arguments NECLOut {A} _.

From Typonomikon Require Import F4.

Module DoesntWork.

Inductive CoListSimF
  {A : Type}
  (F : CoList' A -> CoList' A -> Prop)
  (G : NonEmptyCoList A -> NonEmptyCoList A -> Prop)
  (l1 l2 : CoList' A) : Prop :=
| Empty'    :
        CLOut l1 = Empty -> CLOut l2 = Empty -> CoListSimF F G l1 l2
| NonEmpty' :
        forall l1' l2' : NonEmptyCoList A,
          G l1' l2' -> CoListSimF F G l1 l2.

Inductive NonEmptyCoListSimF
  {A : Type} (F : CoList' A -> CoList' A -> Prop)
  (l1 l2 : NonEmptyCoList A) : Prop :=
| Cons' :
        forall (h1 h2 : A) (t1 t2 : CoList' A),
          h1 = h2 -> F t1 t2 -> NonEmptyCoListSimF F l1 l2.

Fail CoInductive CoListSim
  {A : Type} : CoList' A -> CoList' A -> Prop :=
{
    CLOut' : CoListSimF (NonEmptyCoListSim) l1 l2;
}

with NonEmptyCoListSim
  {A : Type} : NonEmptyCoList A -> NonEmptyCoList A -> Prop :=
{
    NECLOut' : NonEmptyCoListSimF CoListSim l1 l2;
}.

End DoesntWork.

Inductive CoListSimF
  {A : Type} (F : CoList' A -> CoList' A -> Prop)
  (l1 l2 : CoList' A) : Prop :=
| Empty'    :
        CLOut l1 = Empty ->
        CLOut l2 = Empty ->
          CoListSimF F l1 l2
| NonEmpty' :
        forall (h1 h2 : A) (t1 t2 : CoList' A),
          CLOut l1 = NonEmpty {| NECLOut := Cons h1 t1 |} ->
          CLOut l2 = NonEmpty {| NECLOut := Cons h2 t2 |} ->
            h1 = h2 -> F t1 t2 -> CoListSimF F l1 l2.

CoInductive CoListSim {A : Type} (l1 l2 : CoList' A) : Prop :=
{
    CLOut' : CoListSimF CoListSim l1 l2;
}.

Module TheSameAsOrdinary.

CoFixpoint f {A : Type} (l : CoList' A) : CoList A :=
{|
    uncons :=
      match CLOut l with
      | Empty => NilF
      | NonEmpty l' =>
              match  NECLOut l' with
              | Cons h t => ConsF h (f t)
              end
      end
|}.

CoFixpoint g {A : Type} (l : CoList A) : CoList' A :=
{|
    CLOut :=
      match uncons l with
      | NilF      => Empty
      | ConsF h t => NonEmpty {| NECLOut := Cons h (g t) |}
      end
|}.

Lemma fg :
  forall {A : Type} (l : CoList' A),
    CoListSim (g (f l)) l.
Proof.
  cofix CH.
  constructor.
  destruct l as [[| [[h t]]]].
    left; cbn; reflexivity.
    eright; cbn.
      1-3: reflexivity.
      apply CH.
Qed.

Lemma gf :
  forall {A : Type} (l : CoList A),
    lsim (f (g l)) l.
Proof.
  cofix CH.
  constructor.
  destruct l as [[| h t]].
    left; cbn; reflexivity.
    eright; cbn.
      1-3: reflexivity.
      apply CH.
Defined.

End TheSameAsOrdinary.