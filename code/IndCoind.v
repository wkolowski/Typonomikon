CoInductive NETree (A : Type) : Type :=
{
  root  : A;
  left  : option (NETree A);
  right : option (NETree A);
}.

Arguments root  {A} _.
Arguments left  {A} _.
Arguments right {A} _.

Inductive WFL {A : Type} : NETree A -> Prop :=
    | WFL_None : forall t : NETree A, left t = None -> WFL t
    | WFL_Some : forall t t' : NETree A, left t = Some t' -> WFL t' -> WFL t.

