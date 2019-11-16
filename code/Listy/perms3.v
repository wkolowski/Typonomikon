Require Import D5.


Definition exchange {A : Type} (l1 l2 : list A) : Prop :=
  exists (x y : A) (r1 r2 : list A),
    l1 = r1 ++ x :: y :: r2 /\
    l2 = r1 ++ y :: x :: r2.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
    | Perm_refl : forall l : list A, Perm l l
    | Perm_step_trans :
        forall l1 l2 l3 : list A,
          exchange l1 l2 -> Perm l2 l3 -> Perm l1 l3.

Lemma Perm_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Perm l1 l2 -> Perm (x :: l1) (x :: l2).
Proof.
  induction 1.
    constructor.
    destruct H as (y & z & r1 & r2 & eq1 & eq2); subst.
      apply (Perm_step_trans) with (x :: r1 ++ z :: y :: r2).
        red. exists y, z, (x :: r1), r2. split; reflexivity.
        assumption.
Qed.

Lemma Perm_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
Proof.
  intros until 1. revert l3.
  induction H; intros.
    assumption.
    econstructor.
      exact H.
      apply IHPerm. assumption.
Qed.

Lemma Permutation_Perm :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_step_trans _ (x :: y :: l)).
      red. exists y, x, [], l. cbn. split; trivial.
      apply Perm_refl.
    apply Perm_trans with l'; assumption.
Qed.

Lemma Perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  induction 1.
    reflexivity.
    rewrite <- IHPerm.
      destruct H as (x & y & r1 & r2 & eq1 & eq2). subst.
      apply Permutation_app_l. constructor.
Qed.

Lemma Perm_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Perm l1 l2 -> count p l1 = count p l2.
Proof.
  induction 1.
    reflexivity.
    destruct H as (x & y & r1 & r2 & eq1 & eq2). subst.
      rewrite <- IHPerm, !count_app. f_equal. cbn.
      destruct (p x), (p y); reflexivity.
Qed.

Definition perm {A : Type} (l1 l2 : list A) : Prop :=
  forall p : A -> bool, count p l1 = count p l2.

Lemma count_ex :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p l = 0 \/
    exists (x : A) (l1 l2 : list A),
      p x = true /\ l = l1 ++ x :: l2.
Proof.
  induction l as [| h t]; cbn.
    left. reflexivity.
    destruct IHt.
      destruct (p h) eqn: Hph.
        right. exists h, [], t. split; trivial.
        left. assumption.
      destruct H as (x & l1 & l2 & eq1 & eq2); subst.
        destruct (p h) eqn: Hph.
          right. exists h, [], (l1 ++ x :: l2). split; trivial.
          right. exists x, (h :: l1), l2. cbn. split; trivial.
Qed.

Lemma perm_front_ex' :
  forall (A : Type) (h : A) (t l : list A),
    perm (h :: t) l ->
      exists l1 l2 : list A,
        l = l1 ++ h :: l2 /\ perm (l1 ++ l2) t.
Proof.
  unfold perm. intros.
  revert t h H.
  induction l as [| h' t']; cbn; intros.
    specialize (H (fun _ => true)). cbn in H. inversion H.
Abort.

Lemma count_Perm :
  forall (A : Type) (l1 l2 : list A),
    (forall p : A -> bool, count p l1 = count p l2) ->
      Perm l1 l2.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    specialize (H (fun _ => true)). destruct l2; cbn in H.
      apply Perm_refl.
      inversion H.
    induction l2 as [| h2 t2]; cbn.
      specialize (H (fun _ => true)). cbn in H. inversion H.
Abort.

(*
Lemma exchange_ins :
  forall (A : Type) (x : A) (l1 l2 : list A),
    exchange l1 l2 -> exchange (ins x l1) (ins x l2).
Proof.
  destruct 1 as (y & z & r1 & r2 & eq1 & eq2). subst.
  revert r2. induction r1 as [| h t]; cbn; intro.
    red. do 2 eexists. exists []. eexists. split.
      cbn. reflexivity.
*)