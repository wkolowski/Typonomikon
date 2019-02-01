Require Import List.
Import ListNotations.

Set Universe Polymorphism.

Fixpoint opr (f : Type -> Type -> Type) (R : Type) (ts : list Type) : Type :=
match ts with
    | [] => R
    | t :: ts' => f t (opr f R ts')
end.

Definition arr (A B : Type) : Type := A -> B.

Fixpoint zipWithN_Type_aux (n : nat) (R : Type) (ts : list Type) : Type :=
match n with
    | 0 => opr arr R (rev ts) -> opr arr R (map list (rev ts))
    | S n' => forall A : Type, zipWithN_Type_aux n' R (A :: ts)
end.

Definition zipWithN_Type (n : nat) (R : Type) : Type :=
  zipWithN_Type_aux n R [].

Compute zipWithN_Type 2 nat.

Inductive hlist : Type :=
    | hsingl : forall A : Type, list A -> hlist
    | hcons : forall A : Type, list A -> hlist -> hlist.

Arguments hsingl {A} _.
Arguments hcons {A} _ _.

Inductive wut : Type :=
    | wnil : wut
    | wcons : forall A : Type, A -> wut -> wut.

Arguments wcons {A} _ _.

Fixpoint list_to_wut {A : Type} (l : list A) : wut :=
match l with
    | [] => wnil
    | h :: t => wcons h (list_to_wut t)
end.

Fixpoint zip (w : wut) (l : list wut) : list wut :=
match w, l with
    | wnil, _ => []
    | _, [] => []
    | wcons x w', h :: t => wcons x h :: zip w' t
end.

Fixpoint zip' {A : Type} (l : list A) (lw : list wut) : list wut :=
match l, lw with
    | [], _ => []
    | _, [] => []
    | h :: t, w :: ws => wcons h w :: zip' t ws
end.

Fixpoint typ (h : hlist) : list wut :=
match h with
    | hsingl l => [list_to_wut l]
    | hcons l h => zip' l (typ h)
end.

Compute typ (hsingl [true; true]).
Compute typ (hcons [1; 2; 3] (hsingl [true; true])).