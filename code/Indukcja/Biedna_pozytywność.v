Fail Inductive wut : Type :=
    | C : (wut -> bool) -> wut.

Axioms
  (wut : Type)
  (C : (wut -> bool) -> wut)
  (ind : forall
    (P : wut -> Type)
    (H : forall f : wut -> bool, P (C f)),
      {f : forall w : wut, P w |
       forall g : wut -> bool, f (C g) = H g}).

Goal forall w : wut, False.
Proof.
  Check ind (fun _ => False).
Abort.

Definition unC (w : wut) : wut -> bool.
Proof.
  exact (proj1_sig (ind (fun _ => wut -> bool) (fun f => f)) w).
Defined.

Lemma unC_eq :
  forall f : wut -> bool, unC (C f) = f.
Proof.
  intro. unfold unC. destruct (ind _). cbn. rewrite e. reflexivity.
Qed.

Lemma C_inj_aux :
  forall x y : wut, x = y -> unC x = unC y.
Proof.
  destruct 1. reflexivity.
Qed.

Lemma C_inj :
  forall f g : wut -> bool, C f = C g -> f = g.
Proof.
  intros. apply C_inj_aux in H. rewrite 2!unC_eq in H. assumption.
Qed.

Definition bad (f : wut -> bool) : wut -> bool :=
  fun w : wut => negb (f w).

Lemma oh_god_why : False.
Proof.
Abort.