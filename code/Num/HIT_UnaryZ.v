Require Import Recdef Lia.

Inductive Z : Type :=
| z : Z
| s : Z -> Z
| p : Z -> Z.

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

Definition succ (k : Z) : Z := norm (s k).
Definition pred (k : Z) : Z := norm (p k).

Function inv' (k : Z) : Z :=
match k with
| z    => z
| s k' => p (inv' k')
| p k' => s (inv' k')
end.

Definition inv (k : Z) : Z := norm (inv' k).

Function add' (k1 k2 : Z) : Z :=
match k1 with
| z     => k2
| s k1' => s (add' k1' k2)
| p k1' => p (add' k1' k2)
end.

Definition add (k1 k2 : Z) : Z := norm (add' k1 k2).

Function abs' (k : Z) : nat :=
match k with
| z    => 0
| s k' => S (abs' k')
| p k' => S (abs' k')
end.

Definition abs (k : Z) : nat := abs' (norm k).

Function sub' (k1 k2 : Z) : Z :=
match k2 with
| z     => k1
| s k2' => p (sub' k1 k2')
| p k2' => s (sub' k1 k2')
end.

Definition sub (k1 k2 : Z) : Z := norm (sub' k1 k2).

Function mul' (k1 k2 : Z) : Z :=
match k1 with
| z     => z
| s k1' => add' k2 (mul' k1' k2)
| p k1' => sub' (mul' k1' k2) k2
end.

Definition mul (k1 k2 : Z) : Z := norm (mul' k1 k2).

Function min' (k1 k2 : Z) : Z :=
match k1, k2 with
| z    , p _   => k2
| z    , _     => z
| s k1', s k2' => s (min' k1' k2')
| s k1', _     => k2
| p k1', p k2' => p (min' k1' k2')
| p k1', _     => k1
end.

Definition min (k1 k2 : Z) : Z := min' (norm k1) (norm k2).

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

Definition max (k1 k2 : Z) : Z := min (inv k1) (inv k2).

Inductive NF : Z -> Prop :=
| NF_z  : NF z
| NF_sz : NF (s z)
| NF_pz : NF (p z)
| NF_s  : forall k : Z, NF (s k) -> NF (s (s k))
| NF_p  : forall k : Z, NF (p k) -> NF (p (p k)).

Lemma NF_norm :
  forall k : Z,
    NF (norm k).
Proof.
  intros k.
  functional induction norm k.
  - constructor.
  - rewrite e0 in IHz0. inversion IHz0; subst.
    + constructor.
    + assumption.
  - destruct (norm k').
    + constructor.
    + constructor; assumption.
    + contradiction.
  - rewrite e0 in IHz0. inversion IHz0; subst.
    + constructor.
    + assumption.
  - destruct (norm k').
    + constructor.
    + contradiction.
    + constructor; assumption.
Qed.

Lemma norm_NF :
  forall k : Z,
    NF k -> norm k = k.
Proof.
  induction 1; cbn in *.
  1-3: reflexivity.
  - destruct (norm k); inversion IHNF; subst; reflexivity.
  - destruct (norm k); inversion IHNF; subst; reflexivity.
Qed.

Lemma norm_norm :
  forall k : Z,
    norm (norm k) = norm k.
Proof.
  intros k.
  rewrite norm_NF.
  - reflexivity.
  - apply NF_norm.
Qed.

Lemma norm_inv :
  forall k : Z,
    norm (inv k) = inv k.
Proof.
  intros k.
  unfold inv.
  rewrite norm_norm.
  reflexivity.
Qed.

Lemma norm_add :
  forall k1 k2 : Z,
    norm (add k1 k2) = add k1 k2.
Proof.
  intros k1 k2.
  unfold add.
  rewrite norm_norm.
  reflexivity.
Qed.

Lemma NF_min :
  forall k1 k2 : Z,
    NF k1 -> NF k2 -> NF (min' k1 k2).
Proof.
  intros k1 k2.
  functional induction min' k1 k2; cbn; intros H1 H2.
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