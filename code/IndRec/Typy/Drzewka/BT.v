(** Pamiętać, że w RCC jest jakotaka implementacja BTree, którą można tu
    po prostu skopiować. *)

Inductive BTree (A : Type) : Type :=
    | E : BTree A
    | N : A -> BTree A -> BTree A -> BTree A.

Arguments E {A}.
Arguments N {A} _ _ _.

Inductive SameShape {A : Type} : BTree A -> BTree A -> Prop :=
    | SameShape_E : SameShape E E
    | SameShape_N :
        forall (x y : A) (t1 t1' t2 t2' : BTree A),
          SameShape t1 t1' -> SameShape t2 t2' ->
            SameShape (N x t1 t2) (N y t1' t2').

Inductive DifferentShape {A : Type} : BTree A -> BTree A -> Prop :=
    | DifferentShape_EN :
        forall (x : A) (t1 t2 : BTree A),
          DifferentShape E (N x t1 t2)
    | DifferentShape_NE :
        forall (x : A) (t1 t2 : BTree A),
          DifferentShape E (N x t1 t2)
    | DifferentShape_N_rec_l :
        forall (x y : A) (t1 t1' t2 t2' : BTree A),
          DifferentShape t1 t1' ->
            DifferentShape (N x t1 t2) (N y t1' t2')
    | DifferentShape_N_rec_r :
        forall (x y : A) (t1 t1' t2 t2' : BTree A),
          DifferentShape t2 t2' ->
            DifferentShape (N x t1 t2) (N y t1' t2').

Inductive BTreeEq {A : Type} : BTree A -> BTree A -> Type :=
    | BTreeEq_E : BTreeEq E E
    | BTreeEq_N :
        forall (x y : A) (t1 t1' t2 t2' : BTree A),
          x = y -> BTreeEq t1 t1' -> BTreeEq t2 t2' ->
            BTreeEq (N x t1 t2) (N y t1' t2').

Inductive BTreeNeq {A : Type} : BTree A -> BTree A -> Type :=
    | BTreeNeq_EN :
        forall (v : A) (l r : BTree A), BTreeNeq E (N v l r)
    | BTreeNeq_NE :
        forall (v : A) (l r : BTree A), BTreeNeq (N v l r) E
    | BTreeNeq_N_v :
        forall (x y : A) (l1 r1 l2 r2 : BTree A),
          x <> y -> BTreeNeq (N x l1 r1) (N y l2 r2)
    | BTreeNeq_N_l :
        forall (x y : A) (l1 r1 l2 r2 : BTree A),
          BTreeNeq l1 l2 -> BTreeNeq (N x l1 r1) (N y l2 r2)
    | BTreeNeq_N_r :
        forall (x y : A) (l1 r1 l2 r2 : BTree A),
          BTreeNeq r1 r2 -> BTreeNeq (N x l1 r1) (N y l2 r2).

Ltac inv H := inversion H; subst; clear H.

Lemma BTreeNeq_neq :
  forall {A : Type} {t1 t2 : BTree A},
    BTreeNeq t1 t2 -> t1 <> t2.
Proof.
  induction 1; intro Heq; inv Heq; contradiction.
Qed.

Inductive Exists {A : Type} (P : A -> Prop) : BTree A -> Prop :=
    | Exists_N :
        forall (x : A) (l r : BTree A),
          P x -> Exists P (N x l r)
    | Exists_NL :
        forall (x : A) (l r : BTree A),
          Exists P l -> Exists P (N x l r)
    | Exists_NR :
        forall (x : A) (l r : BTree A),
          Exists P r -> Exists P (N x l r).

Inductive Forall {A : Type} (P : A -> Prop) : BTree A -> Prop :=
    | Forall_E : Forall P E
    | Forall_N :
        forall (x : A) (l r : BTree A),
          P x -> Forall P l -> Forall P r -> Forall P (N x l r).

Inductive DirectSubterm {A : Type} : BTree A -> BTree A -> Prop :=
    | DS_L :
        forall (x : A) (l r : BTree A), DirectSubterm l (N x l r)
    | DS_R :
        forall (x : A) (l r : BTree A), DirectSubterm r (N x l r).

Inductive Subterm {A : Type} : BTree A -> BTree A -> Prop :=
    | Subterm_DirectSubterm :
        forall t1 t2 : BTree A, DirectSubterm t1 t2 -> Subterm t1 t2
    | Subterm_step :
        forall t1 t2 t3 : BTree A,
          Subterm t1 t2 -> DirectSubterm t2 t3 -> Subterm t1 t3.

Lemma Subterm_E :
  forall {A : Type} {t1 t2 : BTree A},
    Subterm t1 t2 -> t2 <> E.
Proof.
  induction 1.
    destruct H; inversion 1.
    destruct H0; inversion 1.
Qed.

Lemma wf_Subterm :
  forall {A : Type},
    well_founded (@Subterm A).
Proof.
  red. constructor. induction a as [| x l IHl r IHr]; intros.
    apply Subterm_E in H. contradiction.
    inv H.
      inv H0.
        constructor. assumption.
        constructor. assumption.
      inv H1.
        apply IHl. assumption.
        apply IHr. assumption.
Defined.

Inductive Dup {A : Type} : BTree A -> Type :=
    | Dup_N_xl :
        forall (x : A) (l r : BTree A),
          Exists (fun y => x = y) l -> Dup (N x l r)
    | Dup_N_xr :
        forall (x : A) (l r : BTree A),
          Exists (fun y => x = y) r -> Dup (N x l r)
    | Dup_N_rec_l :
        forall (x : A) (l r : BTree A),
          Dup l -> Dup (N x l r)
    | Dup_N_rec_r :
        forall (x : A) (l r : BTree A),
          Dup r -> Dup (N x l r).

Inductive Exactly {A : Type} (P : A -> Prop) : nat -> BTree A -> Type :=
    | Exactly_E : Exactly P 0 E
    | Exactly_N_yes :
        forall (x : A) (l r : BTree A) (n m : nat),
          Exactly P n l -> Exactly P m r -> P x ->
            Exactly P (1 + n + m) (N x l r)
    | Exactly_N_no :
        forall (x : A) (l r : BTree A) (n m : nat),
          Exactly P n l -> Exactly P m r -> ~ P x ->
            Exactly P (n + m) (N x l r).

Require Import Equality.

Lemma Exactly_det :
  forall {A : Type} {P : A -> Prop} {n m : nat} {t : BTree A},
    Exactly P n t -> Exactly P m t -> n = m.
Proof.
  intros until 1. revert m.
  induction X; intros nm H; inv H.
    reflexivity.
    rewrite (IHX1 _ X), (IHX2 _ X0). reflexivity.
    contradiction.
    contradiction.
    rewrite (IHX1 _ X), (IHX2 _ X0). reflexivity.
Qed.

Require Import ProofIrrelevance.

Lemma isProp_Exactly :
  forall
    {A : Type} {P : A -> Prop} {n : nat} {t : BTree A}
    (p1 p2 : Exactly P n t),
      p1 = p2.
Proof.
  induction p1.
    dependent destruction p2. reflexivity.
    dependent destruction p2.
      {
        assert (n = n0) by (eapply Exactly_det; eassumption).
        assert (m = m0) by (eapply Exactly_det; eassumption).
        subst.
        dependent destruction x.
        f_equal.
          apply IHp1_1.
          apply IHp1_2.
          apply proof_irrelevance.
      }
      contradiction.
    dependent destruction p2.
      contradiction.
      {
        assert (n = n1) by (eapply Exactly_det; eassumption).
        assert (m = m0) by (eapply Exactly_det; eassumption).
        subst.
        dependent destruction x.
        f_equal.
          apply IHp1_1.
          apply IHp1_2.
          apply proof_irrelevance.
      }
Qed.

(** TODO: AtLeast, AtMost *)

Fixpoint size {A : Type} (t : BTree A) : nat :=
match t with
    | E => 0
    | N _ l r => 1 + size l + size r
end.

Definition Elem {A : Type} (x : A) (t : BTree A) : Type :=
  Exists (fun y => x = y) t.

Inductive Index : Type :=
    | here : Index
    | left : Index -> Index
    | right : Index -> Index.

Fixpoint index {A : Type} (i : Index) (t : BTree A) : option A :=
match i, t with
    | here    , N x _ _ => Some x
    | left i' , N _ l _ => index i' l
    | right i', N _ _ r => index i' r
    | _       , _      => None
end.

Lemma Elem_index :
  forall {A : Type} (t : BTree A) (x : A),
    Elem x t -> exists i : Index, index i t = Some x.
Proof.
  induction 1; subst.
    exists here. cbn. reflexivity.
    destruct IHX as [i IH]. exists (left i). cbn. assumption.
    destruct IHX as [i IH]. exists (right i). cbn. assumption.
Qed.

Fixpoint count {A : Type} (p : A -> bool) (t : BTree A) : nat :=
match t with
    | E       => 0
    | N x l r => (if p x then 1 else 0) + count p l + count p r
end.

Definition Perm {A : Type} (t1 t2 : BTree A) : Prop :=
  forall p : A -> bool, count p t1 = count p t2.

Definition Subset {A : Type} (t1 t2 : BTree A) : Type :=
  forall x : A, Elem x t1 -> Elem x t2.

Definition SetEquiv {A : Type} (t1 t2 : BTree A) : Type :=
  Subset t1 t2 * Subset t2 t1.