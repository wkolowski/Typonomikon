Require Import List.
Import ListNotations.

Inductive AppList (A : Type) : Type :=
| Nil
| Cons (h : A) (t : AppList A)
| App  (l1 l2 : AppList A).

Arguments Nil  {A}.
Arguments Cons {A} _ _.
Arguments App  {A} _ _.

Definition nil {A : Type} : AppList A :=
  Nil.

Definition cons {A : Type} (h : A) (t : AppList A) : AppList A :=
  Cons h t.

Fixpoint app {A : Type} (l1 l2 : AppList A) : AppList A :=
match l1 with
| Nil         => l2
| Cons h t    => Cons h (app t l2)
| App l11 l12 => App l11 (app l12 l2)
end.

Inductive Smart {A : Type} : AppList A -> Prop :=
| Smart_Nil : Smart Nil
| Smart_Cons (h : A) (t : AppList A) : Smart t -> Smart (Cons h t)
| Smart_App  (l1 l2 : AppList A) : Smart l1 -> Smart l2 -> Smart (app l1 l2).

Lemma Smart_char :
  forall {A : Type} (l : AppList A),
    Smart l -> forall l1 l2 : AppList A, l <> App l1 l2.
Proof.
  induction 1; intros.
  - now congruence.
  - now congruence.
  - destruct l1; cbn.
    + now apply IHSmart2.
    + now congruence.
    + now contradiction IHSmart1 with l1_1 l1_2.
Qed.

Lemma Smart_inv :
  forall {A : Type} (h : A) (t : AppList A),
    Smart (Cons h t) -> Smart t.
Proof.
  intros A h t HS.
  remember (Cons h t) as l; revert h t Heql.
  induction HS; intros; [congruence.. |].
  destruct l1, l2; cbn in *; try easy.
  - now eapply IHHS2, Heql.
  - eapply IHHS1.
    rewrite <- Heql.
    admit.
  - eapply IHHS2.
  inversion HS1; subst; cbn in *.
Admitted.