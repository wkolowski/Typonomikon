Require Import List.
Import ListNotations.

Require Import Permutation.

Module AdjacentTranspositions.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
    | Perm_refl : forall l : list A, Perm l l
    | Perm_steptrans :
      forall (x y : A) (l1 l2 l3 : list A),
        Perm (l1 ++ y :: x :: l2) l3 -> Perm (l1 ++ x :: y :: l2) l3.

Lemma Perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  induction 1.
    apply Permutation_refl.
    rewrite <- IHPerm. apply Permutation_app.
      reflexivity.
      constructor.
Qed.

Lemma Perm_cons :
  forall {A : Type} (x : A) {l1 l2 : list A},
    Perm l1 l2 -> Perm (x :: l1) (x :: l2).
Proof.
  induction 1.
    constructor.
    apply (Perm_steptrans x0 y (x :: l1) l2). cbn. assumption.
Qed.

Lemma Perm_trans :
  forall {A : Type} {l1 l2 l3 : list A},
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
Proof.
  induction 1; intro H23.
    assumption.
    apply (Perm_steptrans x y l1 l2), IHPerm, H23.
Qed.

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_steptrans y x [] l). cbn. constructor.
    eapply Perm_trans; eassumption.
Qed.

End AdjacentTranspositions.

Module Transpositions.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
    | Perm_refl : forall l : list A, Perm l l
    | Perm_transp :
        forall (x y : A) (l1 l2 l3 l4 : list A),
          Perm (l1 ++ x :: l2 ++ y :: l3) l4 ->
            Perm (l1 ++ y :: l2 ++ x :: l3) l4.

Lemma Perm_cons :
  forall {A : Type} (h : A) (t1 t2 : list A),
    Perm t1 t2 -> Perm (h :: t1) (h :: t2).
Proof.
  induction 1.
    constructor.
    apply (Perm_transp x y (h :: l1)). cbn. assumption.
Qed.

Lemma Perm_trans :
  forall {A : Type} {l1 l2 l3 : list A},
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
Proof.
  induction 1; intro.
    assumption.
    constructor. apply IHPerm. assumption.
Qed.

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_transp x y [] []). cbn. constructor.
    eapply Perm_trans; eassumption.
Qed.

Lemma Permutation_transpose :
  forall {A : Type} {x y : A} {l1 l2 l3 : list A},
    Permutation (l1 ++ x :: l2 ++ y :: l3) (l1 ++ y :: l2 ++ x :: l3).
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    {
      change (x :: l2 ++ y :: l3) with ((x :: l2) ++ y :: l3).
      change (y :: l2 ++ x :: l3) with ((y :: l2) ++ x :: l3).
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite (Permutation_app_comm l3).
      rewrite (Permutation_app_comm l2).
      cbn. constructor.
      apply Permutation_app_comm.
    }
    constructor. apply IHt1.
Qed.

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  induction 1.
    reflexivity.
    rewrite Permutation_transpose. assumption.
Qed.

End Transpositions.

Module Exactly.

Require Import D5.

Ltac inv H := inversion H; subst; clear H.

Definition Perm {A : Type} (l1 l2 : list A) : Prop :=
  forall (P : A -> Prop) (n : nat),
    Exactly P n l1 <-> Exactly P n l2.

Lemma Permutation_Exactly :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat),
        Exactly P n l1 -> Exactly P n l2.
Proof.
  induction 1; intros.
    assumption.
    inv H0.
      constructor.
        assumption.
        apply IHPermutation. assumption.
      constructor 3.
        assumption.
        apply IHPermutation. assumption.
    inv H.
      inv H4; repeat constructor; assumption.
      inv H4; repeat constructor; assumption.
    apply IHPermutation2, IHPermutation1. assumption.
Qed.

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  split.
    apply Permutation_Exactly. assumption.
    apply Permutation_Exactly. symmetry. assumption.
Qed.

Lemma Perm_front_ex :
  forall {A : Type} {h : A} {t l : list A},
    Perm (h :: t) l ->
      exists l1 l2 : list A,
        l = l1 ++ h :: l2 /\ Perm t (l1 ++ l2).
Proof.
  intros until 1.
  revert h t H.
  induction l as [| h' t']; intros.
    admit.
    unfold Perm in H.
Admitted.

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  induction l1 as [| h1 t1]; intros.
    destruct l2 as [| h2 t2].
      constructor.
      {
        unfold Perm in H. destruct (H (fun x => x = h2) 0).
        rewrite Exactly_0_cons in *.
        destruct (H0 ltac:(constructor)).
        contradiction.
      }
    {
      apply Perm_front_ex in H.
      destruct H as (l1 & l3 & H1 & H2). subst.
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite Permutation_app_comm.
      apply IHt1.
      assumption.
    }
Qed.

End Exactly.

Module AtLeast.

Require Import D5.

Ltac inv H := inversion H; subst; clear H.

Definition Perm {A : Type} (l1 l2 : list A) : Prop :=
  forall (P : A -> Prop) (n : nat),
    (AtLeast P n l1 <-> AtLeast P n l2).

Hint Constructors AtLeast.

Lemma Permutation_AtLeast :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat),
        AtLeast P n l1 -> AtLeast P n l2.
Proof.
  induction 1; intros.
    assumption.
    inv H0; auto.
    inv H.
      auto.
      inv H4; auto.
      inv H2; auto.
    apply IHPermutation2, IHPermutation1. assumption.
Qed.

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  split.
    apply Permutation_AtLeast. assumption.
    apply Permutation_AtLeast. symmetry. assumption.
Qed.

Lemma AtLeast_1 :
  forall {A : Type} {P : A -> Prop} {l : list A},
    AtLeast P 1 l ->
      exists (x : A) (l1 l2 : list A),
        P x /\ l = l1 ++ x :: l2.
Proof.
  induction l as [| h t]; intros.
    inv H.
    inv H.
      exists h, [], t. auto.
      destruct (IHt H2) as (x & l1 & l2 & IH1 & IH2).
        subst. exists x, (h :: l1), l2. auto.
Qed.

Lemma AtLeast_app_comm' :
  forall {A : Type} {P : A -> Prop} {n : nat} {l1 l2 : list A},
    AtLeast P n (l1 ++ l2) <-> AtLeast P n (l2 ++ l1).
Proof.
  split; intro; apply AtLeast_app_comm; assumption.
Qed.

Lemma AtLeast_cons_app :
  forall
    {A : Type} {P : A -> Prop} {n : nat}
    (x : A) (l1 l2 : list A),
      AtLeast P n (l1 ++ x :: l2) <->
      AtLeast P n (x :: l1 ++ l2).
Proof.
  intros.
  change (x :: l1 ++ l2) with ((x :: l1) ++ l2).
  rewrite AtLeast_app_comm'. cbn.
  rewrite !AtLeast_cons.
  rewrite !(@AtLeast_app_comm' _ _ _ l1 l2).
  reflexivity.
Qed.

Lemma Perm_front_ex :
  forall {A : Type} {h : A} {t l : list A},
    Perm (h :: t) l ->
      exists l1 l2 : list A,
        l = l1 ++ h :: l2 /\ Perm t (l1 ++ l2).
Proof.
  intros.
  unfold Perm in H.
  assert (AtLeast (fun x => x = h) 1 l).
    apply H. auto.
  apply AtLeast_1 in H0.
  destruct H0 as (x & l1 & l2 & H1 & H2); subst.
  exists l1, l2.
  split.
    reflexivity.
    {
      red. intros.
      destruct (H P n).
      destruct (H P (S n)).
      firstorder.
        specialize (H0 ltac:(auto)).
        specialize (H1 H0).
        inv H1.
          auto.
          apply AtLeast_cons' with h.
            apply AtLeast_cons_app. apply H2. auto.
          assert (AtLeast P n (h :: l1 ++ l2)).
            apply AtLeast_cons_app. auto.
            inv H1.
              auto.
              apply AtLeast_cons' with h.
                apply AtLeast_cons_app. apply H2. auto.
              assumption.
          assert (AtLeast P n (h :: t)).
            apply H1. apply AtLeast_cons_app. constructor. assumption.
            inv H5.
              auto.
              apply AtLeast_cons' with h. apply H3.
                apply AtLeast_app_comm. cbn. constructor.
                  assumption.
                  apply AtLeast_app_comm. assumption.
              assumption.
    }
Qed.

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  induction l1 as [| h1 t1]; intros.
    destruct l2 as [| h2 t2].
      constructor.
      {
        unfold Perm in H. destruct (H (fun x => x = h2) 1).
        specialize (H1 ltac:(auto)). inv H1.
      }
    { unfold Perm in H.
      apply Perm_front_ex in H.
      destruct H as (l1 & l3 & H1 & H2). subst.
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite Permutation_app_comm.
      apply IHt1.
      assumption.
    }
Qed.

Hint Constructors Exactly.

(* TODO *) Lemma AtLeast_Exactly :
  forall {A : Type} (l1 l2 : list A),
    (forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 <-> AtLeast P n l2)
    <->
    (forall (P : A -> Prop) (n : nat),
      Exactly P n l1 <-> Exactly P n l2).
Proof.
  split.
    split; intros.
      induction H0.
        destruct l2.
          auto.
          destruct (H (fun x => x = a) 1).
            specialize (H1 ltac:(auto)). inv H1.
Abort.

End AtLeast.