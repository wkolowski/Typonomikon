Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Inductive Prefix {A : Type} : list A -> list A -> Prop :=
    | Prefix_nil : forall l : list A, Prefix [] l
    | Prefix_cons :
        forall (x : A) (l1 l2 : list A),
          Prefix l1 l2 -> Prefix (x :: l1) (x :: l2).

Lemma Prefix_spec :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 <-> exists l3 : list A, l2 = l1 ++ l3.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists l. reflexivity.
      destruct IHPrefix as (l3 & IH). subst. exists l3. reflexivity.
    destruct 1 as (l3 & H). subst.
      induction l1 as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_app :
  forall (A : Type) (l1 l2 l3 : list A),
    Prefix l1 l2 -> Prefix l1 (l2 ++ l3).
(* begin hide *)
Proof.
  intros. rewrite Prefix_spec in *. destruct H as (l3' & H); subst.
  exists (l3' ++ l3). rewrite app_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Prefix_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Inductive Suffix {A : Type} : list A -> list A -> Prop :=
    | Suffix_nil :
        forall l : list A, Suffix [] l
    | Suffix_cons :
        forall (x : A) (l1 l2 : list A),
          Suffix l1 l2 -> Suffix (snoc x l1) (snoc x l2).

Inductive Suffix' {A : Type} : list A -> list A -> Prop :=
    | Suffix'_nil :
        forall l : list A, Suffix' l l
    | Suffix'_cons :
        forall (x : A) (l1 l2 : list A),
          Suffix' l1 l2 -> Suffix' l1 (x :: l2).

(* TODO *) Lemma Suffix_Suffix' :
  forall (A : Type) (l1 l2 : list A),
    Suffix l1 l2 <-> Suffix' l1 l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      induction l as [| h t]; cbn; constructor. assumption.
Abort.
(* end hide *)

Lemma Suffix'_spec :
  forall (A : Type) (l1 l2 : list A),
    Suffix' l1 l2 <-> exists l3 : list A, l2 = l3 ++ l1.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists []. cbn. reflexivity.
      destruct IHSuffix' as (l3 & IH); subst.
        exists (x :: l3). reflexivity.
    destruct 1 as (l3 & H). subst.
      induction l3 as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_Suffix :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 <-> Suffix (rev l1) (rev l2).
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      constructor.
      rewrite <- ?snoc_app_singl. constructor. assumption.
    assert (forall l1 l2 : list A, Suffix l1 l2 -> Prefix (rev l1) (rev l2)).
      induction 1; cbn.
        constructor.
        rewrite ?rev_snoc. constructor. assumption.
      intro. specialize (H _ _ H0). rewrite ?rev_inv in H. assumption.
Qed.
(* end hide *)