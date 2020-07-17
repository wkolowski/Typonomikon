(**
TODO: github.com/mioalter/talks/blob/master/Haskell_Meetup_Jan_13_2016/
      Two_Tricks_Haskell_Meetup_1_13_2016.pdf
*)

Inductive RBT (A : Type) : Type :=
    | L : A -> RBT A
    | N : RBT A -> RBT A -> RBT A.

Arguments L {A} _.
Arguments N {A} _ _.

Inductive SameShape {A : Type} : RBT A -> RBT A -> Prop :=
    | SameShape_L :
        forall x y : A, SameShape (L x) (L y)
    | SameShape_N :
        forall t1 t1' t2 t2' : RBT A,
          SameShape t1 t1' -> SameShape t2 t2' ->
            SameShape (N t1 t2) (N t1' t2').

Inductive DifferentShape {A : Type} : RBT A -> RBT A -> Prop :=
    | DifferentShape_LN :
        forall (x : A) (t1 t2 : RBT A),
          DifferentShape (L x) (N t1 t2)
    | DifferentShape_NL :
        forall (x : A) (t1 t2 : RBT A),
          DifferentShape (N t1 t2) (L x)
    | DifferentShape_N_rec_l :
        forall t1 t1' t2 t2' : RBT A,
          DifferentShape t1 t1' -> DifferentShape (N t1 t2) (N t1' t2')
    | DifferentShape_N_rec_r :
        forall t1 t1' t2 t2' : RBT A,
          DifferentShape t2 t2' -> DifferentShape (N t1 t2) (N t1' t2').

Inductive RBTEq {A : Type} : RBT A -> RBT A -> Type :=
    | RBTEq_L :
        forall x y : A, x = y -> RBTEq (L x) (L y)
    | RBTEq_N :
        forall t1 t1' t2 t2' : RBT A,
          RBTEq t1 t1' -> RBTEq t2 t2' -> RBTEq (N t1 t2) (N t1' t2').

Inductive RBTNeq {A : Type} : RBT A -> RBT A -> Type :=
    | RBTNeq_L :
        forall x y : A, x <> y -> RBTNeq (L x) (L y)
    | RBTNeq_N_l :
        forall t1 t1' t2 t2' : RBT A,
          RBTNeq t1 t1' -> RBTNeq (N t1 t2) (N t1' t2')
    | RBTNeq_N_r :
        forall t1 t1' t2 t2' : RBT A,
          RBTNeq t2 t2' -> RBTNeq (N t1 t2) (N t1' t2').

Ltac inv H := inversion H; subst; clear H.

Lemma RBTNeq_neq :
  forall {A : Type} {t1 t2 : RBT A},
    RBTNeq t1 t2 -> t1 <> t2.
Proof.
  induction 1; intro Heq; inv Heq; contradiction.
Qed.

Inductive Exists {A : Type} (P : A -> Prop) : RBT A -> Type :=
    | Exists_L :
        forall x : A, P x -> Exists P (L x)
    | Exists_NL :
        forall t1 t2 : RBT A, Exists P t1 -> Exists P (N t1 t2)
    | Exists_NR :
        forall t1 t2 : RBT A, Exists P t2 -> Exists P (N t1 t2). 

Inductive Forall {A : Type} (P : A -> Prop) : RBT A -> Prop :=
    | Forall_ L :
        forall x : A, P x -> Forall P (L x)
    | Forall_N :
        forall t1 t2 : RBT A,
          Forall P t1 -> Forall P t2 -> Forall P (N t1 t2).

Inductive DirectSubterm {A : Type} : RBT A -> RBT A -> Prop :=
    | DS_L :
        forall t1 t2 : RBT A, DirectSubterm t1 (N t1 t2)
    | DS_R :
        forall t1 t2 : RBT A, DirectSubterm t2 (N t1 t2).

Inductive Subterm {A : Type} : RBT A -> RBT A -> Prop :=
    | Subterm_DirectSubterm :
        forall t1 t2 : RBT A, DirectSubterm t1 t2 -> Subterm t1 t2
    | Subterm_step :
        forall t1 t2 t3 : RBT A,
          Subterm t1 t2 -> DirectSubterm t2 t3 -> Subterm t1 t3.

Lemma Subterm_L :
  forall {A : Type} {t1 t2 : RBT A},
    Subterm t1 t2 -> forall x : A, t2 <> L x.
Proof.
  induction 1.
    destruct H; inversion 1.
    destruct H0; inversion 1.
Qed.

Lemma wf_Subterm :
  forall {A : Type},
    well_founded (@Subterm A).
Proof.
  red. constructor. induction a as [| t1 IH1 t2 IH2].
    intros. apply Subterm_L with a in H. contradiction.
    inversion 1; subst.
      inversion H0; subst.
        constructor. destruct 1.
          apply IH1. constructor. assumption.
          apply IH1. econstructor 2; eassumption.
        constructor. destruct 1.
          apply IH2. constructor. assumption.
          apply IH2. econstructor 2; eassumption.
      inversion H1; subst.
        apply IH1. assumption.
        apply IH2. assumption.
Defined.

Inductive Dup {A : Type} : RBT A -> Type :=
    | Dup_both :
        forall (x : A) (t1 t2 : RBT A),
          Exists (fun y => x = y) t1 ->
          Exists (fun y => x = y) t2 ->
            Dup (N t1 t2)
    | Dup_l :
        forall t1 t2 : RBT A,
          Dup t1 -> Dup (N t1 t2)
    | Dup_r :
        forall t1 t2 : RBT A,
          Dup t2 -> Dup (N t1 t2).

Inductive Exactly {A : Type} (P : A -> Prop) : nat -> RBT A -> Type :=
    | Exactly_L_yes :
        forall x : A, P x -> Exactly P 1 (L x)
    | Exactly_L_no :
        forall x : A, ~ P x -> Exactly P 0 (L x)
    | Exactly_N :
        forall (t1 t2 : RBT A) (n1 n2 : nat),
          Exactly P n1 t1 -> Exactly P n2 t2 ->
            Exactly P (n1 + n2) (N t1 t2).

Require Import Equality.

Lemma Exactly_det :
  forall {A : Type} {P : A -> Prop} {n m : nat} {t : RBT A},
    Exactly P n t -> Exactly P m t -> n = m.
Proof.
  intros until 1. revert m.
  induction X; inversion 1; subst.
    reflexivity.
    contradiction.
    contradiction.
    reflexivity.
    rewrite (IHX1 n0), (IHX2 n3).
      reflexivity.
      assumption.
      assumption.
Qed.

Require Import ProofIrrelevance.

Lemma isProp_Exactly :
  forall
    {A : Type} {P : A -> Prop} {n : nat} {t : RBT A}
    (p1 p2 : Exactly P n t),
      p1 = p2.
Proof.
  induction p1.
    dependent destruction p2. f_equal. apply proof_irrelevance.
    dependent destruction p2. f_equal. apply proof_irrelevance.
    {
      dependent destruction p2.
      assert (n1 = n0) by (eapply Exactly_det; eassumption).
      assert (n2 = n3) by (eapply Exactly_det; eassumption).
      subst.
      dependent destruction x.
      f_equal.
        apply IHp1_1.
        apply IHp1_2.
    }
Qed.

Inductive AtLeast {A : Type} (P : A -> Prop) : nat -> RBT A -> Type :=
    | AtLeast_0 :
        forall t : RBT A, AtLeast P 0 t
    | AtLeast_L :
        forall x : A, P x -> AtLeast P 1 (L x)
    | AtLeast_N :
        forall (t1 t2 : RBT A) (n1 n2 : nat),
          AtLeast P n1 t1 -> AtLeast P n2 t2 ->
            AtLeast P (n1 + n2) (N t1 t2).

Lemma Exactly_AtLeast :
  forall {A : Type} {P : A -> Prop} {n : nat} {t : RBT A},
    Exactly P n t -> AtLeast P n t.
Proof.
  induction 1.
    constructor. assumption.
    constructor.
    constructor; assumption.
Qed.

Inductive AtMost {A : Type} (P : A -> Prop) : nat -> RBT A -> Type :=
    | AtMost_L :
        forall x : A, AtMost P 1 (L x)
    | AtMost_L_not :
        forall x : A, ~ P x -> AtMost P 0 (L x)
    | AtMost_N :
        forall (t1 t2 : RBT A) (n1 n2 : nat),
          AtMost P n1 t1 -> AtMost P n2 t2 ->
            AtMost P (n1 + n2) (N t1 t2).

Fixpoint bind {A B : Type} (t : RBT A) (f : A -> RBT B) : RBT B :=
match t with
    | L x => f x
    | N t1 t2 => N (bind t1 f) (bind t2 f)
end.

Fixpoint size {A : Type} (t : RBT A) : nat :=
match t with
    | L _ => 1
    | N t1 t2 => size t1 + size t2
end.

(*
Lemma size_bind :
  forall {A B : Type} (t : RBT A) (f : A -> RBT B),
    size (bind t f) = size t * 
*)

Lemma AtMost_size :
  forall {A : Type} {P : A -> Prop} {t : RBT A},
    AtMost P (size t) t.
Proof.
  induction t; cbn.
    constructor.
    constructor; assumption.
Qed.

Definition Elem {A : Type} (x : A) (t : RBT A) : Type :=
  Exists (fun y => x = y) t.

Inductive Index : Type :=
    | here : Index
    | left : Index -> Index
    | right : Index -> Index.

Fixpoint index {A : Type} (i : Index) (t : RBT A) : option A :=
match i, t with
    | here    , L x    => Some x
    | left i' , N t' _ => index i' t'
    | right i', N _ t' => index i' t'
    | _       , _      => None
end.

Lemma Elem_index :
  forall {A : Type} (t : RBT A) (x : A),
    Elem x t -> exists i : Index, index i t = Some x.
Proof.
  induction 1; subst.
    exists here. cbn. reflexivity.
    destruct IHX as [i Heq]. exists (left i). cbn. assumption.
    destruct IHX as [i Heq]. exists (right i). cbn. assumption.
Qed.

Fixpoint count {A : Type} (p : A -> bool) (t : RBT A) : nat :=
match t with
    | L x => if p x then 1 else 0
    | N t1 t2 => count p t1 + count p t2
end.

Definition Perm {A : Type} (t1 t2 : RBT A) : Prop :=
  forall p : A -> bool, count p t1 = count p t2.

Definition Subset {A : Type} (t1 t2 : RBT A) : Type :=
  forall x : A, Elem x t1 -> Elem x t2.

Definition SetEquiv {A : Type} (t1 t2 : RBT A) : Type :=
  Subset t1 t2 * Subset t2 t1.