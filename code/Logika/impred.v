(** * Impredykatywizm *)

Definition ior (P Q : Prop) : Prop :=
  forall X : Prop, (P -> X) -> (Q -> X) -> X.

Lemma ior_or :
  forall P Q : Prop,
    ior P Q <-> P \/ Q.
Proof.
  unfold ior. split.
    intros H. apply H.
      intro p. left. assumption.
      intro q. right. assumption.
    intros H X inl inr. destruct H as [p | q].
      apply inl. assumption.
      apply inr. assumption.
Qed.

Definition iand (P Q : Prop) : Prop :=
  forall G : Prop, (P -> Q -> G) -> G.

Lemma iand_and :
  forall P Q : Prop,
    iand P Q <-> P /\ Q.
Proof.
  unfold iand. split.
    intro H. apply H.
      intros p q. split; assumption.
    intros [p q] G conj. apply conj; assumption.
Qed.

Definition iTrue : Prop :=
  forall G : Prop, G -> G.

Lemma iTrue_True :
  iTrue <-> True.
Proof.
  unfold iTrue. split.
    intros _. trivial.
    intros _ G g. assumption.
Qed.

Definition iFalse : Prop :=
  forall G : Prop, G.

Lemma iFalse_False :
  iFalse <-> False.
Proof.
  unfold iFalse. split.
    intro H. apply H.
    contradiction.
Qed.

Definition iexists {A : Type} (P : A -> Prop) : Prop :=
  forall G : Prop, (forall x : A, P x -> G) -> G.

Lemma iexists_exists :
  forall {A : Type} (P : A -> Prop),
    iexists P <-> exists x : A, P x.
Proof.
  unfold iexists. split.
    intros H. apply H. intros x p. exists x. assumption.
    intros [x p] G H. apply (H x). assumption.
Qed.

Definition Leibniz {A : Type} (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Lemma Leibniz_eq :
  forall {A : Type} (x y : A),
    Leibniz x y <-> x = y.
Proof.
  unfold Leibniz. split.
    intro H. apply H. reflexivity.
    intros eq P H. rewrite <- eq. assumption.
Qed.