From Typonomikon Require Import F4.

Inductive CoRoseTreeF (X A : Type) : Type :=
| E
| N (v : A) (ts : CoList X).

Arguments E {X A}.
Arguments N {X A} _ _.

CoInductive CoRoseTree (A : Type) : Type :=
{
  Out : CoRoseTreeF (CoRoseTree A) A;
}.

Arguments Out {A} _.

Definition E' {A : Type} : CoRoseTree A :=
{|
    Out := E;
|}.

Definition N' {A : Type} (v : A) (ts : CoList (CoRoseTree A)) : CoRoseTree A :=
{|
    Out := N v ts;
|}.

Fail CoFixpoint crmap {A B : Type} (f : A -> B) (t : CoRoseTree A) : CoRoseTree B :=
{|
    Out :=
      match Out t with
      | E => E
      | N v ts => N (f v) (lmap (crmap f) ts)
      end
|}.

Fail CoFixpoint crmap {A B : Type} (f : A -> B) (t : CoRoseTree A) : CoRoseTree B :=
{|
    Out :=
      match Out t with
      | E => E
      | N v ts => N (f v) (clmap f ts)
      end
|}

with clmap {A B : Type} (f : A -> B) (ts : CoList (CoRoseTree A)) : CoList (CoRoseTree B) :=
{|
    uncons :=
      match uncons ts with
      | NilF        => NilF
      | ConsF t ts' => ConsF (crmap f t) (clmap f ts')
      end
|}.