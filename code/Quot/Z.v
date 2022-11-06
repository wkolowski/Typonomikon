Require Import Recdef StrictProp Bool Lia.

Ltac inv H := inversion H; subst; clear H; auto.

Inductive Z : Type :=
| z : Z
| s : Z -> Z
| p : Z -> Z.

Inductive NF : Z -> Prop :=
| NF_z  : NF z
| NF_sz : NF (s z)
| NF_s  : forall k : Z, NF (s k) -> NF (s (s k))
| NF_pz : NF (p z)
| NF_p  : forall k : Z, NF (p k) -> NF (p (p k)).

#[global] Hint Constructors NF : core.

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

Function norm (k : Z) : Z :=
match k with
| z    => z
| s k' =>
  match norm k' with
  | p k'' => k''
  | k''   => s k''
  end
| p k' =>
  match norm k' with
  | s k'' => k''
  | k''   => p k''
  end
end.

Compute norm (s (s (s (p (p (p z)))))).
(* ===> = z : Z *)

Definition z' : Z := z.

Definition s' (k : Z) : Z :=
match k with
| z    => s z
| s k' => s (s k')
| p k' => k'
end.

Definition p' (k : Z) : Z :=
match k with
| z    => p z
| s k' => k'
| p k' => p (p k')
end.

Function norm' (k : Z) : Z :=
match k with
| z => z'
| s k' => s' (norm' k')
| p k' => p' (norm' k')
end.

Function abs (k : Z) : Z :=
match k with
| z => z
| s k' => s k'
| p k' => s (abs k')
end.

Function inv (k : Z) : Z :=
match k with
| z    => z
| s k' => p (inv k')
| p k' => s (inv k')
end.

Function add (k l : Z) : Z :=
match k with
| z => l
| s k' => s (add k' l)
| p k' => p (add k' l)
end.

Function sub (k l : Z) : Z :=
match l with
| z    => k
| s l' => p (sub k l')
| p l' => s (sub k l')
end.

Function mul (k l : Z) : Z :=
match k with
| z    => z
| s k' => add l (mul k' l)
| p k' => sub (mul k' l) l
end.

Function min (k1 k2 : Z) : Z :=
match k1, k2 with
| z    , p _   => k2
| z    , _     => z
| s k1', s k2' => s (min k1' k2')
| s k1', _     => k2
| p k1', p k2' => p (min k1' k2')
| p k1', _     => k1
end.

Definition max (k1 k2 : Z) : Z := min (inv k1) (inv k2).

Function fromNat (n : nat) : Z :=
match n with
| 0    => z
| S n' => s (fromNat n')
end.

Function succNegative (n : nat) : Z :=
match n with
| 0    => p z
| S n' => p (succNegative n')
end.

Compute abs (min (fromNat 5) (fromNat 6)).
Compute abs (min (succNegative 7) (fromNat 5)).

Lemma isNormal_spec :
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

Lemma isNormal_norm :
  forall k : Z,
    isNormal (norm k) = true.
Proof.
  intros k. destruct (isNormal_spec (norm k)).
  - reflexivity.
  - contradiction n. apply NF_norm.
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

Lemma norm_NF_conv :
  forall k : Z,
    norm k = k -> NF k.
Proof.
  intros k Heq.
  destruct (isNormal_spec k).
  - assumption.
  - rewrite <- Heq. apply NF_norm.
Qed.

Lemma norm_NF' :
  forall k : Z,
    NF k <-> norm k = k.
Proof.
  split.
  - apply norm_NF.
  - apply norm_NF_conv.
Qed.

Lemma norm_norm :
  forall k : Z,
    norm (norm k) = norm k.
Proof.
  intros k.
  apply norm_NF.
  apply NF_norm.
Qed.

Lemma norm_isNormal :
  forall k : Z,
    isNormal k = true -> norm k = k.
Proof.
  intros k; functional induction norm k; cbn; intro Heq.
  2-5: destruct k'; cbn in *; intuition congruence.
  reflexivity.
Qed.

Lemma norm'_norm :
  forall k : Z,
    norm' k = norm k.
Proof.
  reflexivity.
Qed.

Lemma abs_abs :
  forall k : Z, abs (abs k) = abs k.
Proof.
  induction k; cbn; reflexivity.
Qed.

Lemma add_z_l :
  forall k : Z,
    add z k = k.
Proof.
  reflexivity.
Qed.

Lemma add_z_r :
  forall k : Z,
    add k z = k.
Proof.
  induction k; cbn; rewrite ?IHk; reflexivity.
Qed.

Lemma add_s_r :
  forall k l : Z,
    norm (add k (s l)) = norm (s (add k l)).
Proof.
  induction k; cbn; intros l.
  - reflexivity.
  - rewrite IHk. cbn. reflexivity.
  - rewrite IHk. cbn. destruct (norm (add k l)).
    + reflexivity.
    + destruct z0; try reflexivity.
Admitted.

Lemma add_p_r :
  forall k l : Z,
    norm (add k (p l)) = norm (p (add k l)).
Proof.
  induction k; cbn; intros l.
  - reflexivity.
  - rewrite IHk. cbn. destruct (norm (add k l)).
Admitted.

Lemma add_s_r' :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> add k (s l) = s (add k l).
Proof.
  intros k l HN1 HN2.
Admitted.

Lemma add_p_r' :
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
  - rewrite add_z_r. reflexivity.
  - rewrite add_s_r, IHk; cbn; reflexivity.
  - rewrite add_p_r, IHk; cbn; reflexivity.
Qed.

Lemma sub_spec :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> sub k l = add (inv l) k.
Proof.
  induction l; cbn; intros.
  - reflexivity.
  - rewrite IHl; intuition. destruct l; congruence.
  - rewrite IHl; intuition. destruct l; congruence.
Qed.

Lemma norm_sub :
  forall k l : Z,
    norm (sub k l) = norm (add (inv l) k).
Proof.
  induction l; cbn; rewrite ?IHl; reflexivity.
Qed.

Lemma abs_inv :
  forall k : Z,
    isNormal k = true -> abs (inv k) = abs k.
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

Lemma abs_inv' :
  forall k : Z,
    NF k ->
      norm (abs (inv k)) = norm (abs k).
Proof.
  intros k HNF.
  rewrite abs_inv.
  - reflexivity.
  - destruct (isNormal_spec k); intuition.
Qed.

Lemma NF_min :
  forall k1 k2 : Z,
    NF k1 -> NF k2 -> NF (min k1 k2).
Proof.
  intros k1 k2.
  functional induction min k1 k2; cbn; intros H1 H2.
  - assumption.
  - assumption.
  - inversion H1; inversion H2; subst; clear H1 H2; cbn; constructor.
    apply IHz0; assumption.
  - assumption.
  - inversion H1; inversion H2; subst; clear H1 H2; cbn; constructor.
    1-2: assumption.
    apply IHz0; assumption.
  - assumption.
Qed.

Module Z_NF.

Record Z' : Type :=
{
  canonical : Z;
  NF_canonical : Squash (NF canonical);
}.

End Z_NF.

Module Z_norm.

Record Z' : Type :=
{
  canonical : Z;
  norm_canonical : Squash (norm canonical = canonical);
}.

End Z_norm.

Module Z_isNormal.

Record Z' : Type :=
{
  canonical : Z;
  isNormal_canonical : Squash (isNormal canonical = true);
}.

End Z_isNormal.

Module Z_SmartConstructors.

Record Z' : Type :=
{
  canonical : Z;
  isNormal_canonical : Squash (isNormal canonical = true);
}.

Function abs' (k : Z) : Z :=
match k with
| z    => z
| s k' => s k'
| p k' => s (abs' k')
end.

Function inv' (k : Z) : Z :=
match k with
| z    => z'
| s k' => p' (inv' k')
| p k' => s' (inv' k')
end.

Function add' (k l : Z) : Z :=
match k with
| z => l
| s k' => s' (add' k' l)
| p k' => p' (add' k' l)
end.

Function sub' (k l : Z) : Z :=
match l with
| z    => k
| s l' => p' (sub' k l')
| p l' => s' (sub' k l')
end.

Lemma abs'_abs' :
  forall k : Z, abs' (abs' k) = abs k.
Proof.
  induction k; cbn; reflexivity.
Qed.

Lemma abs'_inv :
  forall k : Z,
    isNormal k = true -> abs' (inv k) = abs' k.
Proof.
  induction k; cbn; intros.
    reflexivity.
    destruct k; cbn in *.
      reflexivity.
Admitted.

End Z_SmartConstructors.

Module Z_wut.

Definition succ (k : Z) : Z := norm (s k).
Definition pred (k : Z) : Z := norm (p k).

Definition inv' (k : Z) : Z := norm (inv k).

Definition add' (k1 k2 : Z) : Z := norm (add k1 k2).

Function abs (k : Z) : nat :=
match k with
| z    => 0
| s k' => S (abs k')
| p k' => S (abs k')
end.

Definition abs' (k : Z) : nat := abs (norm k).

Definition sub' (k1 k2 : Z) : Z := norm (sub k1 k2).

Definition mul' (k1 k2 : Z) : Z := norm (mul k1 k2).

Definition min' (k1 k2 : Z) : Z := min (norm k1) (norm k2).

Lemma norm_inv' :
  forall k : Z,
    norm (inv' k) = inv' k.
Proof.
  intros k.
  unfold inv'.
  rewrite norm_norm.
  reflexivity.
Qed.

Lemma norm_add' :
  forall k1 k2 : Z,
    norm (add' k1 k2) = add' k1 k2.
Proof.
  intros k1 k2.
  unfold add'.
  rewrite norm_norm.
  reflexivity.
Qed.

End Z_wut.