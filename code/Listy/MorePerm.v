Require Import List.
Import ListNotations.

Require Import Permutation.

Require Import JMeq.
Require Import Program.Equality.

Scheme wut := Induction for Permutation Sort Prop.

Lemma isProp_Permutation_not :
  forall (A : Type),
    exists p1 p2 : @Permutation A [] [], p1 <> p2.
Proof.
  intro.
  exists (@perm_nil A), (perm_trans (@perm_nil A) (@perm_nil A)).
  intro.
Abort.

(*
Lemma isProp_Permutation :
  forall {A : Type} (l1 l2 : list A) (p1 p2 : Permutation l1 l2),
    p1 = p2.
Proof.
  intros A l1 l2.
  eapply (@wut A (fun l1 l2 p1 => forall p2 : Permutation l1 l2, p1 = p2) _ _ _ _ l1 l2).
  Unshelve.
  all: cbn; intros. Print Permutation.
    inversion p2.
  
 Permutation_ind A. (fun l1 l2 => _).


  dependent induction p1.
  induction p1.
*)

Print Permutation.

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
    admit.
    rewrite <- IHPerm. admit.
Admitted.

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