Require Import Recdef StrictProp Lia.

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

Record Z' : Type :=
{
    canonical : Z;
    norm_canonical : Squash (norm canonical = canonical);
}.

Compute norm (s (s (s (p (p (p z)))))).
(* ===> = z : Z *)

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
  intros k.
  functional induction norm k.
  - constructor.
  - rewrite e0 in IHz0. inv IHz0.
  - destruct (norm k'); intuition.
  - rewrite e0 in IHz0. inv IHz0.
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
  intros k.
  apply norm_NF.
  apply NF_norm.
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
    norm (sub k l) = norm (add (neg l) k).
Proof.
  induction l; cbn; rewrite ?IHl; reflexivity.
Qed.

Lemma abs_neg :
  forall k : Z,
    NF k ->
      norm (abs (neg k)) = norm (abs k).
Proof.
  induction k; cbn; intros.
  - reflexivity.
  - destruct k; cbn in *.
    + reflexivity.
    + rewrite IHk.
      * reflexivity.
      * inv H.
    + inv H.
  - destruct k; cbn in *.
    + reflexivity.
    + inv H.
    + rewrite IHk.
      * reflexivity.
      * inv H.
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
Admitted.

Lemma add_p_r :
  forall k l : Z,
    norm (add k (p l)) = norm (p (add k l)).
Proof.
  induction k; cbn; intros l.
  - reflexivity.
  - rewrite IHk. cbn. destruct (norm (add k l)).
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