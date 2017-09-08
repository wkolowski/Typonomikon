Require Import Bool.Bool.

Inductive option (A : Type) : Type :=
    | Some : A -> option A
    | None : option A.

Arguments Some [A] _.
Arguments None [A].

Notation "A ?" := (option A) (at level 50).

Definition isSome {A : Type} (ma : A?) : bool :=
match ma with
    | Some _ => true
    | None => false
end.

Definition isNone {A : Type} (ma : A?) : bool :=
match ma with
    | Some _ => false
    | None => true
end.

Theorem isSome_or_isNone : forall (A : Type) (ma : A?),
    isSome ma || isNone ma = true.
Proof.
  destruct ma; simpl; trivial.
Qed.

(* In Haskell, this is called fromMaybe *)
Definition orElse {A : Type} (oa : A?) (a : A) : A :=
match oa with
    | Some x => x
    | None => a
end.

Definition fmap {A B : Set} (f : A -> B) (ma : A?) : B? :=
match ma with
    | Some a => Some (f a)
    | None => None
end.

Definition bind {A B : Set} (ma : A?) (f : A -> B?) : B? :=
match ma with
    | Some a => f a
    | None => None
end.

