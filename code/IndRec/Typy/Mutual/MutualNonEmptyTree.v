Inductive BT (A : Type) : Type :=
    | Empty    : BT A
    | NonEmpty : NonEmptyBT A -> BT A

with NonEmptyBT (A : Type) : Type :=
    | Nnode    : A -> BT A -> BT A -> NonEmptyBT A.

Arguments Empty    {A}.
Arguments NonEmpty {A} _.
Arguments Nnode    {A} _ _ _.

(** Niczym się to nie różni od zwykłych drzew. *)

Require Import BT.

Fixpoint f {A : Type} (t : BT A) : BTree A :=
match t with
    | Empty       => E
    | NonEmpty t' => f' t'
end

with f' {A : Type} (t : NonEmptyBT A) : BTree A :=
match t with
    | Nnode x l r => N x (f l) (f r)
end.

Fixpoint g {A : Type} (t : BTree A) : BT A :=
match t with
    | E       => Empty
    | N x l r => NonEmpty (Nnode x (g l) (g r))
end.

Lemma fg :
  forall {A : Type} (t : BT A),
    g (f t) = t.
Proof.
  fix IH 2.
  destruct t as [| [x l r]]; cbn.
    reflexivity.
     rewrite !IH. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : BTree A),
    f (g t) = t.
Proof.
  induction t as [| x l IHl r IHr]; cbn.
    reflexivity.
    rewrite IHl, IHr. reflexivity.
Qed.