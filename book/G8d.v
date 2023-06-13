(** * G8d: Pierwszorzędowe kody [TODO] *)

From Typonomikon Require Import G8c.

(** Innym pomysłem na jednorodne reprezentowanie typów induktywnych,
    trochę podobnym do W-typów, jest stworzenie uniwersum nazw (czyli
    kodów), które następnie będziemy mogli zinterpretować jako typy
    induktywne. *)

Inductive I : Type :=
| u : I
| nonind : forall A : Type, (A -> I) -> I
| ind : I -> I.

Fixpoint Arg (i : I) (X : Type) : Type :=
match i with
| u => unit
| nonind A f => {a : A & Arg (f a) X}
| ind i => X * Arg i X
end.

Definition iprod (A B : Type) : I :=
  nonind A (fun _ => nonind B (fun _ => u)).

Compute Arg (iprod nat bool) False.

Definition isum (A B : Type) : I :=
  nonind bool (fun b => nonind (if b then A else B) (fun _ => u)).

Compute Arg (isum nat bool) False.

Definition inat : I :=
  nonind bool (fun b => if b then u else ind u).

Compute Arg inat False.

Definition inat_nat {X : Type} (a : Arg inat X) : unit + X.
Proof.
  cbn in a. destruct a as [[] []].
    left. exact tt.
    right. exact x.
Defined.

Definition ilist (A : Type) : I :=
  nonind bool (fun b => if b then u else nonind A (fun _ => ind u)).

Compute Arg (ilist nat) False.

Definition ifalse : I := ind u.

Compute Arg ifalse unit.

Unset Positivity Checking.
Inductive IType (i : I) : Type :=
| intro : Arg i (IType i) -> IType i.
Set Positivity Checking.

(*
Fixpoint IType_ind
  {i : I}
  {P : IType i -> Type}
  (intro' : forall a : Arg i (IType i), P (intro a) ->
*)

Definition iinat := IType inat.

Definition Z : iinat.
Proof.
  constructor. cbn. exists true. cbn. exact tt.
Defined.

Definition iS (n : iinat) : iinat.
Proof.
  constructor. cbn. exists false. cbn. split.
    exact n.
    constructor.
Defined.

Unset Guard Checking.
Fixpoint iinat_ind
  {P : iinat -> Type}
  (z : P Z)
  (s : forall n : iinat, P n -> P (iS n))
  (n : iinat) {struct n} : P n.
Proof.
  destruct n as [[[] []]].
    exact z.
    destruct a. apply s. apply iinat_ind; assumption.
Qed.
Set Guard Checking.

Fixpoint nat_to_iinat (n : nat) : iinat :=
match n with
| 0 => Z
| Datatypes.S n' => iS (nat_to_iinat n')
end.

Definition pred (n : iinat) : option iinat :=
match n with
| intro _ (existT _ true _) => None
| intro _ (existT _ false (n', _)) => Some n'
end.

(*
Fixpoint iinat_to_nat (n : iinat) : nat :=
match pred n with
| None => 0
| Some n' => S (iinat_to_nat n')
end.
*)

Unset Guard Checking.
Fixpoint iinat_to_nat (n : iinat) : nat :=
match n with
| intro _ (existT _ true _) => 0
| intro _ (existT _ false (n', _)) => Datatypes.S (iinat_to_nat n')
end.
Set Guard Checking.

Lemma one_way :
  forall n : nat, iinat_to_nat (nat_to_iinat n) = n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    f_equal. assumption.
Defined.

Compute one_way 0.

Lemma second_way' :
  forall n : iinat, nat_to_iinat (iinat_to_nat n) = n.
Proof.
  apply iinat_ind; cbn.
    reflexivity.
    intros n' IH. f_equal. assumption.
Qed.

Unset Guard Checking.
Fixpoint second_way
  (n : iinat) : nat_to_iinat (iinat_to_nat n) = n.
Proof.
  destruct n as [[[] []]]; cbn.
    reflexivity.
    unfold iS. repeat f_equal.
      apply second_way.
      destruct a. reflexivity.
Defined.
Set Guard Checking.

Compute second_way (iS Z).
Compute second_way (iS (iS Z)).

(** TODO: Kody dla typów induktywno-rekursywnych *)

Inductive IR (D : Type) : Type :=
| iota  : D -> IR D
| sigma : forall A : Type, (A -> IR D) -> IR D
| delta : forall A : Type, ((A -> D) -> IR D) -> IR D.