Require Import D5.

Definition DList (A : Type) : Type := list A -> list A.

Definition dnil {A : Type} : DList A := fun _ => [].

Definition dcons {A : Type} (h : A) (t : DList A) : DList A :=
  fun l => h :: t l.

Definition dapp {A : Type} (l1 l2 : DList A) : DList A :=
  fun l => l1 l ++ l2 l.