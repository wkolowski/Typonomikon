Require Import Bool Recdef StrictProp.

Inductive Z : Type :=
| z : Z
| s : Z -> Z
| p : Z -> Z.

Function isNormal (k : Z) : bool :=
match k with
| z    => true
| s k' =>
  match k' with
  | p _ => false
  | _   => isNormal k'
  end
| p k' =>
  match k' with
  | s _ => false
  | _   => isNormal k'
  end
end.

Record Z' : Type :=
{
    canonical : Z;
    isNormal_canonical : Squash (isNormal canonical = true);
}.

Function norm (k : Z) : Z :=
match k with
| z => z
| s k' =>
  match norm k' with
  | p k'' => k''
  | k'' => s k''
  end
| p k' =>
  match norm k' with
  | s k'' => k''
  | k'' => p k''
  end
end.

Ltac inv H := inversion H; subst; clear H; auto.

Inductive NF : Z -> Prop :=
| NF_z  : NF z
| NF_sz : NF (s z)
| NF_s  : forall k : Z, NF (s k) -> NF (s (s k))
| NF_pz : NF (p z)
| NF_p  : forall k : Z, NF (p k) -> NF (p (p k)).

#[global] Hint Constructors NF : core.

Lemma NF_norm :
  forall k : Z,
    NF (norm k).
Proof.
  intros k; functional induction norm k.
  - constructor.
  - rewrite e0 in IHz0; inv IHz0.
  - destruct (norm k'); intuition.
  - rewrite e0 in IHz0; inv IHz0.
  - destruct (norm k'); intuition.
Qed.

Lemma norm_NF :
  forall k : Z,
    NF k -> norm k = k.
Proof.
  induction 1.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - rewrite norm_equation, IHNF; reflexivity.
  - cbn; reflexivity.
  - rewrite norm_equation, IHNF; reflexivity.
Qed.

Lemma norm_idempotent :
  forall k : Z,
    norm (norm k) = norm k.
Proof.
  intros.
  apply norm_NF.
  apply NF_norm.
Qed.

Lemma NF_isNormal :
  forall k : Z, reflect (NF k) (isNormal k).
Proof.
  intros k; functional induction isNormal k
  ; repeat constructor.
  - intro H; inv H.
  - inv IHb; repeat constructor.
    + inv H0; contradiction.
    + intro H1; inv H1.
  - intro H; inv H.
  - inv IHb; repeat constructor.
    + inv H0; contradiction.
    + intro H1; inv H1.
Defined.

Lemma isNormal_norm :
  forall k : Z,
    isNormal (norm k) = true.
Proof.
  intros k; functional induction norm k; cbn.
  - reflexivity.
  - rewrite e0 in IHz0; cbn in *. destruct k''; congruence.
  - destruct (norm k'); cbn in *; auto.
  - rewrite e0 in IHz0; cbn in *. destruct k''; congruence.
  - destruct (norm k'); cbn in *; auto.
Qed.

Lemma norm_isNormal :
  forall k : Z,
    isNormal k = true -> norm k = k.
Proof.
  intros k; functional induction norm k; cbn; intro Heq.
  2-5: destruct k'; cbn in *; intuition congruence.
  reflexivity.
Qed.

Fixpoint abs (k : Z) : Z :=
match k with
| z => z
| s k' => s k'
| p k' => s (abs k')
end.

Lemma abs_abs :
  forall k : Z, abs (abs k) = abs k.
Proof.
  induction k; cbn; reflexivity.
Qed.

Fixpoint neg (k : Z) : Z :=
match k with
| z    => z
| s k' => p (neg k')
| p k' => s (neg k')
end.

Fixpoint add (k l : Z) : Z :=
match k with
| z => l
| s k' => s (add k' l)
| p k' => p (add k' l)
end.

Fixpoint sub (k l : Z) : Z :=
match l with
| z    => k
| s l' => p (sub k l')
| p l' => s (sub k l')
end.

Lemma sub_spec :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> sub k l = add (neg l) k.
Proof.
  induction l; cbn; intros.
  - reflexivity.
  - rewrite IHl.
    + reflexivity.
    + assumption.
    + destruct l; congruence.
  - rewrite IHl.
    + reflexivity.
    + assumption.
    + destruct l; congruence.
Qed.

Lemma abs_neg :
  forall k : Z,
    isNormal k = true -> abs (neg k) = abs k.
Proof.
  induction k; cbn; intros.
  - reflexivity.
  - destruct k; cbn in *.
    + reflexivity.
    + rewrite (IHk H); reflexivity.
    + congruence.
  - destruct k; cbn in *.
    + reflexivity.
    + congruence.
    + rewrite (IHk H); reflexivity.
Qed.

Lemma add_z_r :
  forall k : Z,
    add k z = k.
Proof.
  induction k; cbn; rewrite ?IHk; reflexivity.
Qed.

Lemma add_s_r :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> add k (s l) = s (add k l).
Proof.
Admitted.

Compute norm (add (s z) (p z)).
Compute norm (p (add (s z) z)).

Lemma add_p_r :
  forall k l : Z,
    norm (add k (p l)) = norm (p (add k l)).
Proof.
  induction k as [| k' | k']; cbn; intros.
Admitted.

Lemma add_comm :
  forall k l : Z,
    norm (add k l) = norm (add l k).
Proof.
  induction k; cbn; intros l.
  - rewrite add_z_r; reflexivity.
  - rewrite add_s_r, IHk; cbn; admit.
  - rewrite add_p_r, IHk; cbn; admit.
Admitted.