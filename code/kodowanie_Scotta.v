Unset Positivity Checking.

Require Import List.
Import ListNotations.

Inductive Scott (A : Type) : Type :=
{
    scott : forall X : Type, X -> (A -> Scott A -> X) -> X;
}.

Arguments scott {A}.

Definition nil {A : Type} : Scott A :=
  {| scott := fun _ n _ => n |}.

Definition cons {A : Type} (h : A) (t : Scott A) : Scott A :=
  {| scott := fun _ _ c => c h t |}.

Definition l : Scott nat :=
  cons 1 (cons 2 (cons 3 nil)).

Definition head {A : Type} (l : Scott A) : option A :=
  scott l _ None (fun a _ => Some a).

Unset Universe Checking.

Definition tail {A : Type} (l : Scott A) : option (Scott A) :=
  scott l _ None (fun _ t => Some t).

Compute tail l.

Unset Guard Checking.
Fixpoint toList {A : Type} (l : Scott A) {struct l} : list A :=
  scott l _ [] (fun h t => h :: toList t).

Compute toList l.

Compute toList (match tail l with None => nil | Some t => t end).

Definition ohnoes (l : Scott unit) : Scott unit -> bool.
destruct l. apply scott0.
Abort.