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

Lemma Permutation_Perm :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    constructor.
    admit.
    apply (Perm_step_trans _ (x :: y :: l)).
      red. exists y, x, [], l. cbn. split; trivial.
      apply Perm_refl.
    admit.
Admitted.

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