Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Inductive prefix {A : Type} : list A -> list A -> Prop :=
    | prefix_nil : forall l : list A, prefix [] l
    | prefix_cons :
        forall (x : A) (l1 l2 : list A),
          prefix l1 l2 -> prefix (x :: l1) (x :: l2).

Lemma prefix_spec :
  forall (A : Type) (l1 l2 : list A),
    prefix l1 l2 <-> exists l3 : list A, l2 = l1 ++ l3.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists l. reflexivity.
      destruct IHprefix as (l3 & IH). subst. exists l3. reflexivity.
    destruct 1 as (l3 & H). subst.
      induction l1 as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Inductive suffix {A : Type} : list A -> list A -> Prop :=
    | suffix_nil :
        forall l : list A, suffix [] l
    | suffix_cons :
        forall (x : A) (l1 l2 : list A),
          suffix l1 l2 -> suffix (snoc x l1) (snoc x l2).

Inductive suffix' {A : Type} : list A -> list A -> Prop :=
    | suffix'_nil :
        forall l : list A, suffix' l l
    | suffix'_cons :
        forall (x : A) (l1 l2 : list A),
          suffix' l1 l2 -> suffix' l1 (x :: l2).

Lemma suffix'_spec :
  forall (A : Type) (l1 l2 : list A),
    suffix' l1 l2 <-> exists l3 : list A, l2 = l3 ++ l1.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists []. cbn. reflexivity.
      destruct IHsuffix' as (l3 & IH); subst.
        exists (x :: l3). reflexivity.
    destruct 1 as (l3 & H). subst.
      induction l3 as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma prefix_suffix :
  forall (A : Type) (l1 l2 : list A),
    prefix l1 l2 <-> suffix (rev l2) (rev l1).
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      constructor.
      rewrite <- ?snoc_app_singl. constructor. assumption.
    assert (forall l1 l2 : list A, suffix l1 l2 -> prefix (rev l2) (rev l1)).
      induction 1; cbn.
        constructor.
        rewrite ?rev_snoc. constructor. assumption.
      intro. specialize (H _ _ H0). rewrite ?rev_inv in H. assumption.
Qed.
(* end hide *)

