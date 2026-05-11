Inductive PoorW (C : Type) (N : C -> Type) (R : C -> Type) : Type :=
| mk : forall c : C, N c -> (R c -> PoorW C N R) -> PoorW C N R.

Arguments mk {C N R} _ _ _.

Inductive ListC : Type :=
| Nil
| Cons.

Definition List' (A : Type) : Type :=
  PoorW ListC
    (fun c =>
      match c with
      | Nil => unit
      | Cons => A
      end)
    (fun c =>
      match c with
      | Nil => False
      | Cons => unit
      end).

Require Import List.
Import ListNotations.

Fixpoint f {A : Type} (l : list A) : List' A :=
match l with
| [] => mk Nil tt (fun e : False => match e with end)
| h :: t => mk Cons h (fun _ => f t)
end.

Fixpoint g {A : Type} (l : List' A) : list A :=
match l with
| mk Nil _ _ => []
| mk Cons h t => h :: g (t tt)
end.

Lemma gf :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  now induction l as [| h t]; cbn; [| rewrite IHt].
Qed.

Lemma fg :
  forall {A : Type} (l : List' A),
    f (g l) = l.
Proof.
  induction l as [[] h t]; cbn.
  - f_equal.
    + now destruct h.
    + admit.
  - f_equal.
    admit.
Admitted.
