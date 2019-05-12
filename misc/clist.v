Require Import X3.

(*
Definition clist'
  {A : Type} (P : (forall X : Type, X -> (A -> X -> X) -> X) -> Type)
  : Type :=
    forall X : Type,
      P (fun _ nil _ => nil) ->
      (forall (h : A) (t : forall X, X -> (A -> X -> X) -> X),
        P t -> P (fun X nil cons => cons h (t X nil cons))) ->
      forall l : forall X : Type, X -> (A -> X -> X) -> X, P l.
*)


Definition clist (A : Type) : Type :=
  forall X : Type, X -> (A -> X -> X) -> X.

Definition cnil {A : Type} : clist A :=
  fun X nil cons => nil.

Definition ccons {A : Type} : A -> clist A -> clist A :=
  fun h t => fun X nil cons => cons h (t X nil cons).

Notation "c[]" := cnil.
Notation "x :c: y" := (ccons x y) (at level 60, right associativity).
Notation "c[ x ; .. ; y ]" := (ccons x .. (ccons y cnil) ..).

Fixpoint fromList {A : Type} (l : list A) : clist A :=
match l with
    | [] => cnil
    | h :: t => ccons h (fromList t)
end.

Definition toList {A : Type} (l : clist A) : list A :=
  l (list A) [] (@cons A).

Lemma toList_fromList :
  forall (A : Type) (l : list A),
    toList (fromList l) = l.
Proof.
  induction l as [| h t]; compute in *; rewrite ?IHt; reflexivity.
Qed.

Lemma fromList_toList :
  forall (A : Type) (cl : clist A),
    fromList (toList cl) = cl.
Proof.
  intros. unfold clist in *. compute.
Abort.

Definition clen {A : Type} (l : clist A) : nat :=
  l nat 0 (fun _ => S).

Compute clen c[1; 2; 3].

Definition capp {A : Type} (l1 l2 : clist A) : clist A :=
  fun X nil cons => l1 X (l2 X nil cons) cons.

Compute capp c[1; 2; 3] c[4; 5; 6].

Lemma len_app :
  forall (A : Type) (l1 l2 : clist A),
    len (app l1 l2) = len l1 + len l2.
Proof.
  unfold clist, len, app. intros. unfold clist in *.