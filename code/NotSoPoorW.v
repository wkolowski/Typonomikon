Inductive W (C : Type) (R : C -> Type) : Type :=
| sup : forall c : C, (R c -> W C R) -> W C R.

Arguments sup {C R} _ _.

Inductive ListC (A : Type) : Type :=
| Nil
| Cons (h : A).

Arguments Nil  {A}.
Arguments Cons {A} _.

Definition List' (A : Type) : Type :=
  W (ListC A)
    (fun c =>
      match c with
      | Nil    => False
      | Cons _ => unit
      end).

Require Import List.
Import ListNotations.

Fixpoint f {A : Type} (l : list A) : List' A :=
match l with
| [] => sup Nil (fun e : False => match e with end)
| h :: t => sup (Cons h) (fun _ => f t)
end.

Fixpoint g {A : Type} (l : List' A) : list A :=
match l with
| sup Nil  _ => []
| sup (Cons h) t => h :: g (t tt)
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
  induction l as [[] h t]; cbn; f_equal.
  - admit.
  - admit.
Admitted.
