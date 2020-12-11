Inductive InfTree (B A : Type) : Type :=
    | E : InfTree B A
    | N : A -> (B -> InfTree B A) -> InfTree B A.

Arguments E {B A}.
Arguments N {B A} _ _.

Definition leaf {A : Type} (x : A) : InfTree False A :=
  N x (fun e : False => match e with end).

Definition isEmpty {B A : Type} (t : InfTree B A) : bool :=
match t with
    | E => true
    | _ => false
end.

Definition root {B A : Type} (t : InfTree B A) : option A :=
match t with
    | E => None
    | N x _ => Some x
end.

Definition unN {B A : Type} (t : InfTree B A)
  : option (A * {B : Type & B -> InfTree B A}) :=
match t with
    | E => None
    | N x f => Some (x, @existT Type _ B f)
end.

(** Zagadka, że o ja jebie: udowodnij, że funkcji [size] i [height] nie da
    się zaimplementować. *)

(*
Parameter size : forall A : Type, BTree A -> nat.
Parameter height : forall A : Type, BTree A -> nat.
*)

(*
Parameter leftmost : forall A : Type, BTree A -> option A.
Parameter rightmost : forall A : Type, BTree A -> option A.

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter bfs_aux :
  forall A : Type, list (BTree A) -> list A -> list A.

Parameter bfs : forall A : Type, BTree A -> list A.
*)

(*
Parameter mirror' : forall A : Type, BTree A -> BTree A.
*)

Fixpoint complete {B A : Type} (n : nat) (x : A) : InfTree B A :=
match n with
    | 0 => E
    | S n' => N x (fun _ => complete n' x)
end.

Fixpoint iterate
  {B A : Type} (f : A -> A) (n : nat) (x : A) : InfTree B A :=
match n with
    | 0 => E
    | S n' => N x (fun _ => iterate f n' (f x))
end.

Fixpoint take {B A : Type} (n : nat) (t : InfTree B A) : InfTree B A :=
match n, t with
    | 0, _ => E
    | _, E => E
    | S n', N x f => N x (fun b : B => take n' (f b))
end.

(*
Parameter index : forall A : Type, list bool -> BTree A -> option A.
Parameter nth : forall A : Type, nat -> BTree A -> option A.
*)

(*
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).
*)
Print InfTree.
Fixpoint intersperse {B A : Type} (v : A) (t : InfTree B A) : InfTree B A :=
match t with
    | E => E
    | N x f => N x (fun _ => N v (fun b => intersperse v (f b)))
end.

(*
Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.
*)

(*
Parameter any : forall A : Type, (A -> bool) -> BTree A -> bool.
Parameter all : forall A : Type, (A -> bool) -> BTree A -> bool.
*)

(*
Parameter find : forall A : Type, (A -> bool) -> BTree A -> option A.
Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).
*)

(*
Parameter count : forall A : Type, (A -> bool) -> BTree A -> nat.
*)


Fixpoint takeWhile
  {B A : Type} (p : A -> bool) (t : InfTree B A) : InfTree B A :=
match t with
    | E => E
    | N x f => if p x then N x (fun b : B => takeWhile p (f b)) else E
end.

(*
Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).
*)

Fixpoint map {A B C : Type} (f : B -> C) (t : InfTree A B) : InfTree A C :=
match t with
    | E => E
    | N x g => N (f x) (fun a : A => map f (g a))
end.

Fixpoint zipWith
  {A B C D : Type} (f : B -> C -> D)
  (t1 : InfTree A B) (t2 : InfTree A C) : InfTree A D :=
match t1, t2 with
    | E, _ => E
    | _, E => E
    | N x g, N y h => N (f x y) (fun a : A => zipWith f (g a) (h a))
end.

(*
Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.
*)

(** Predykaty *)

Inductive Elem {B A : Type} (x : A) : InfTree B A -> Prop :=
    | Elem_here :
        forall f : B -> InfTree B A, Elem x (N x f)
    | Elem_there :
        forall (f : B -> InfTree B A) (b : B),
          Elem x (f b) -> Elem x (N x f).

Inductive Exists {B A : Type} (P : A -> Prop) : InfTree B A -> Prop :=
    | Exists_here :
        forall (x : A) (f : B -> InfTree B A),
          P x -> Exists P (N x f)
    | Exists_there :
        forall (x : A) (f : B -> InfTree B A) (b : B),
          Exists P (f b) -> Exists P (N x f).

Inductive Forall {B A : Type} (P : A -> Prop) : InfTree B A -> Prop :=
    | Forall_E : Forall P E
    | Forall_N :
        forall (x : A) (f : B -> InfTree B A),
          (forall b : B, Forall P (f b)) -> Forall P (N x f).

(*
Parameter Dup : forall A : Type, BTree A -> Prop.

Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtMost : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
*)

Inductive SameShape
  {A B C : Type} : InfTree A B -> InfTree A C -> Prop :=
    | SS_E : SameShape E E
    | SS_N :
        forall
          (x : B) (y : C)
          (f : A -> InfTree A B) (g : A -> InfTree A C),
            (forall a : A, SameShape (f a) (g a)) ->
              SameShape (N x f) (N y g).

Inductive InfTreeDirectSubterm
  {B A : Type} : InfTree B A -> InfTree B A -> Prop :=
    | ITDS_E :
        forall (x : A) (f : B -> InfTree B A) (b : B),
          InfTreeDirectSubterm (f b) (N x f).

Inductive InfTreeSubterm
  {B A : Type} : InfTree B A -> InfTree B A -> Prop :=
    | ITS_refl :
        forall t : InfTree B A, InfTreeSubterm t t
    | ITS_step :
        forall t1 t2 t3 : InfTree B A,
          InfTreeDirectSubterm t1 t2 -> InfTreeSubterm t2 t3 ->
            InfTreeSubterm t1 t3.

Inductive InfTreeEq
  {B A : Type} : InfTree B A -> InfTree B A -> Prop :=
    | ITE_E : InfTreeEq E E
    | ITE_N :
        forall (v1 v2 : A) (f1 f2 : B -> InfTree B A),
          v1 = v2 -> (forall b : B, InfTreeEq (f1 b) (f2 b)) ->
            InfTreeEq (N v1 f1) (N v2 f2).

Require Import FunctionalExtensionality.

Lemma decode :
  forall {B A : Type} {t1 t2 : InfTree B A},
    InfTreeEq t1 t2 -> t1 = t2.
Proof.
  induction 1.
    reflexivity.
    f_equal.
      assumption.
      apply functional_extensionality. intro x. apply H1.
Restart.
  fix IH 5.
  destruct 1.
    reflexivity.
    f_equal.
      assumption.
      apply functional_extensionality. intro. apply IH, H0.
Defined.

Lemma encode :
  forall {B A : Type} {t1 t2 : InfTree B A},
    t1 = t2 -> InfTreeEq t1 t2.
Proof.
  destruct 1.
  induction t1; constructor.
    reflexivity.
    assumption.
Defined.

Lemma encode_decode :
  forall {B A : Type} {t1 t2 : InfTree B A} (p : t1 = t2),
    decode (encode p) = p.
Proof.
  destruct p.
  induction t1.
    reflexivity.
    {
      cbn. rewrite eq_trans_refl_l.
      generalize (functional_extensionality i i (fun x : B => decode
        (InfTree_ind B A (fun t1 : InfTree B A => InfTreeEq t1 t1) ITE_E
           (fun (a0 : A) (i0 : B -> InfTree B A) (H0 : forall b : B, InfTreeEq (i0 b) (i0 b)) =>
            ITE_N a0 a0 i0 i0 eq_refl H0) (i x)))).
      admit.
    }
Abort.

Scheme InfTreeEq_ind' := Induction for InfTreeEq Sort Prop.

Lemma decode_encode :
  forall {B A : Type} {t1 t2 : InfTree B A} (c : InfTreeEq t1 t2),
    encode (decode c) = c.
Proof.
  induction c using InfTreeEq_ind'; cbn.
    reflexivity.
    {
      destruct e.
      rewrite eq_trans_refl_l.
      generalize (functional_extensionality f1 f2 (fun x : B => decode (i x))).
      destruct e.
      cbn. f_equal.
      extensionality y.
Abort.