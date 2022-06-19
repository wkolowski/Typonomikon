Require Import Bool Recdef StrictProp.

Inductive Z : Type :=
| z' : Z
| s' : Z -> Z
| p' : Z -> Z.

Definition z : Z := z'.

Definition s (k : Z) : Z :=
match k with
| z'    => s' z'
| s' k' => s' (s' k')
| p' k' => k'
end.

Definition p (k : Z) : Z :=
match k with
| z'    => p' z'
| s' k' => k'
| p' k' => p' (p' k')
end.

Function isNormal (k : Z) : bool :=
match k with
| z'    => true
| s' k' =>
  match k' with
  | p' _ => false
  | _    => isNormal k'
  end
| p' k' =>
  match k' with
  | s' _ => false
  | _    => isNormal k'
  end
end.

Record Z' : Type :=
{
    canonical : Z;
    isNormal_canonical : Squash (isNormal canonical = true);
}.

Function norm (k : Z) : Z :=
match k with
| z' => z
| s' k' => s (norm k')
| p' k' => p (norm k')
end.

Ltac inv H := inversion H; subst; clear H; auto.

Lemma isNormal_norm :
  forall k : Z,
    isNormal (norm k) = true.
Proof.
  intros k; functional induction norm k; cbn.
  - reflexivity.
  - destruct (norm k'); cbn in *; try destruct z0; congruence.
  - destruct (norm k'); cbn in *; try destruct z0; congruence.
Qed.

Lemma norm_isNormal :
  forall k : Z,
    isNormal k = true -> norm k = k.
Proof.
  intros k; functional induction norm k; cbn; intro Heq.
  - reflexivity.
  - rewrite IHz0; destruct k'; cbn in *; try congruence.
  - rewrite IHz0; destruct k'; cbn in *; try congruence.
Qed.

Lemma norm_idempotent :
  forall k : Z,
    norm (norm k) = norm k.
Proof.
  intros k; rewrite norm_isNormal.
  - reflexivity.
  - apply isNormal_norm.
Qed.

Fixpoint abs (k : Z) : Z :=
match k with
| z'    => z
| s' k' => s k'
| p' k' => s (abs k')
end.

Lemma abs_abs :
  forall k : Z, abs (abs k) = abs k.
Proof.
  induction k; cbn.
  - reflexivity.
  - unfold s. destruct k; cbn in *; try reflexivity. unfold s in *.
Abort.

Fixpoint abs' (k : Z) : Z :=
match k with
| z'    => z'
| s' k' => s' k'
| p' k' => s' (abs' k')
end.

Lemma abs_abs :
  forall k : Z, abs' (abs' k) = abs' k.
Proof.
  induction k; cbn; reflexivity.
Qed.

Fixpoint neg (k : Z) : Z :=
match k with
| z'    => z
| s' k' => p (neg k')
| p' k' => s (neg k')
end.

Fixpoint add (k l : Z) : Z :=
match k with
| z' => l
| s' k' => s (add k' l)
| p' k' => p (add k' l)
end.

Fixpoint sub (k l : Z) : Z :=
match l with
| z'    => k
| s' l' => p (sub k l')
| p' l' => s (sub k l')
end.

Lemma sub_spec :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> sub k l = add (neg l) k.
Proof.
  induction l; cbn; intros.
    reflexivity.
    rewrite IHl.
Admitted.

Lemma abs_neg :
  forall k : Z,
    isNormal k = true -> abs (neg k) = abs k.
Proof.
  induction k; cbn; intros.
    reflexivity.
    destruct k; cbn in *.
      reflexivity.
Admitted.

Lemma add_z_r :
  forall k : Z,
    add k z = k.
Proof.
  induction k; cbn; rewrite ?IHk.
Admitted.

Lemma add_s'_r :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> add k (s' l) = s' (add k l).
Proof.
  induction k; cbn; intros.
    reflexivity.
    destruct k as [| k' | k']; cbn in *.
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
  induction k; cbn; intros.
  - rewrite add_z_r; reflexivity.
Admitted.