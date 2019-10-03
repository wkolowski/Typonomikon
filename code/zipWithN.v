Require Import List.
Import ListNotations.

Inductive Code : Type :=
  | Singl : Type -> Code
  | Cons : Type -> Code -> Code.

Fixpoint cmap (F : Type -> Type) (c : Code) : Code :=
match c with
  | Singl A => Singl (F A)
  | Cons A c' => Cons (F A) (cmap F c')
end.

Fixpoint funType (c : Code) (R : Type) : Type :=
match c with
  | Singl A => A -> R
  | Cons A c' => A -> funType c' R
end.

Definition listType (c : Code) (R : Type) : Type :=
  funType (cmap list c) R.

Fixpoint prod (c : Code) : Type :=
match c with
  | Singl A => A
  | Cons A c' => A * prod c'
end.

Definition prodList (c : Code) : Type :=
  prod (cmap list c).

Definition listProd (c : Code) : Type :=
  list (prod c).

Definition uncurriedFunType (c : Code) (R : Type) : Type :=
  prod c -> R.

Definition uncurriedListType (c : Code) (R : Type) : Type :=
  prodList c -> R.

Fixpoint zip2 {A B : Type} (l : list A) (r : list B) : list (A * B) :=
match l, r with
  | [], _ => []
  | _, [] => []
  | hl :: tl, hr :: tr => (hl, hr) :: zip2 tl tr
end.

Fixpoint zip {c : Code} : prodList c -> listProd c :=
match c with
  | Singl A => id
  | Cons A c' =>
    fun '(l, p) => zip2 l (zip p)
end.

Compute
  @zip
    (Cons bool (Singl nat))
    ([true; false], [4; 5]).


Fixpoint uncurryFun
  {c : Code} {R : Type} {struct c} : funType c R -> uncurriedFunType c R.
Proof.
  destruct c; cbn in *; intro f; red; cbn.
    exact f.
    intros [t p]. exact (uncurryFun _ _ (f t) p).
Defined.

Fixpoint curryList
  {c : Code} {R : Type} {struct c} : uncurriedListType c R -> listType c R.
Proof.
  destruct c as [A | A c']; unfold uncurriedListType; cbn in *.
    intros f l. exact (f l).
    intros f l. apply curryList. red. intro. apply f. split; assumption.
Defined.


Definition zipWith
  {c : Code} {R : Type} (f : funType c R) : listType c (list R) :=
    curryList (fun p : prodList c => map (uncurryFun f) (zip p)).

Compute
  @zipWith
    (Cons nat (Cons nat (Singl nat))) _
    (fun a b c => a + b + c)
    [1; 2; 3] [4; 5; 6] [7; 8; 9].