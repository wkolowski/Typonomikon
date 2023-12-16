Require Import List.
Import ListNotations.

Module typeOf.

Definition typeOf_hd {A : Type} (l : list A) : Type :=
match l with
| [] => unit
| _ :: _ => A
end.

Definition hd {A : Type} (l : list A) : typeOf_hd l :=
match l with
| [] => tt
| h :: _ => h
end.

Compute hd [] : unit.
Compute hd [42] : nat.

Definition typeOf_tail {A : Type} (l : list A) : Type :=
match l with
| [] => unit
| _ :: _ => list A
end.

Definition tail {A : Type} (l : list A) : typeOf_tail l :=
match l with
| [] => tt
| _ :: t => t
end.

Compute tail [] : unit.
Compute tail [42] : list nat.

Definition typeOf_uncons {A : Type} (l : list A) : Type :=
match l with
| [] => unit
| _ :: _ => A * list A
end.

Definition uncons {A : Type} (l : list A) : typeOf_uncons l :=
match l with
| [] => tt
| h :: t => (h, t)
end.

Compute uncons [] : unit.
Compute uncons [42] : nat * list nat.

End typeOf.

Module ULTIMATE_typeOf.

Definition typeOf_hd {A : Type} (l : list A) : Type :=
match l with
| [] => l = []
| h :: _ => {a : A | a = h}
end.

Definition hd {A : Type} (l : list A) : typeOf_hd l :=
match l with
| [] => eq_refl
| h :: _ => exist _ h eq_refl
end.

Compute hd [] : [] = [].
Compute hd [42] : {n : nat | n = 42}.

Definition typeOf_tail {A : Type} (l : list A) : Type :=
match l with
| [] => l = []
| _ :: t => {l : list A | l = t}
end.

Definition tail {A : Type} (l : list A) : typeOf_tail l :=
match l with
| [] => eq_refl
| _ :: t => exist _ t eq_refl
end.

Compute tail [] : [] = [].
Compute tail [42] : {l : list nat | l = []}.

Definition typeOf_uncons {A : Type} (l : list A) : Type :=
match l with
| [] => l = []
| h :: t => {p : A * list A | p = (h, t)}
end.

Definition uncons {A : Type} (l : list A) : typeOf_uncons l :=
match l with
| [] => eq_refl
| h :: t => exist _ (h, t) eq_refl
end.

Compute uncons [] : [] = [].
Compute uncons [42] : {p : nat * list nat | p = (42, [])}.

End ULTIMATE_typeOf.