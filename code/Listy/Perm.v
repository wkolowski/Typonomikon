Require Import D5.

(** ** Permutacje jako ciągi transpozycji elementów sąsiednich *)

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

Lemma Perm_spec :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 <-> Permutation l1 l2.
Proof.
  split.
    apply Perm_Permutation.
    apply Permutation_Perm.
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

(** ** Permutacje jako listy, które mają tyle samo elementów o każdej
       rozstrzygalnej właściwości *)

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

Lemma Perm_perm :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> perm l1 l2.
Proof.
  induction 1; cbn.
    red. reflexivity.
    destruct H as (x & y & r1 & r2 & eq1 & eq2); subst.
      unfold perm in *. intro. specialize (IHPerm p).
      rewrite <- IHPerm. rewrite 2!count_app. cbn.
      destruct (p x), (p y); reflexivity.
Qed.

Lemma perm_Perm :
  forall (A : Type) (l1 l2 : list A),
    perm l1 l2 -> Perm l1 l2.
Proof.
  intros. apply Permutation_Perm.
  apply Permutation_count_conv. exact H.
Qed.

(** ** Liczenie wszystkich permutacji przez selekcję *)

Module perms1.

Fixpoint select {A : Type} (l : list A) : list (list A * list A) :=
match l with
    | [] => [([], [])]
    | h :: t => [([], l)] ++ map (fun '(a, b) => (h :: a, b)) (select t)
end.

Compute select [1; 2; 3].

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | h :: t =>
        bind (fun ll =>
          map (fun '(l, r) => l ++ h :: r) (select ll)) (perms t)
end.

Compute perms [1; 2; 3].

Lemma Permutation_perms :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (perms l1) (perms l2).
Proof.
  induction 1; cbn.
    do 2 constructor.
    rewrite 2!bind_spec. apply Permutation_join, Permutation_map.
      assumption.
    rewrite !bind_spec. apply Permutation_join. admit.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Admitted.

Lemma elem_perms :
  forall (A : Type) (l : list A),
    elem l (perms l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    rewrite bind_spec, elem_join.
      exists (map (fun '(l, r) => l ++ h :: r) (select t)). split.
        destruct t; constructor.
        apply elem_map_conv. exists t. split.
          reflexivity.
          assumption.
Qed.

Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
Proof.
  intros. apply Permutation_perms in H.
  Search Permutation elem.
  rewrite <- (Permutation_elem _ (perms l1) (perms l2)).
    apply elem_perms.
    assumption.
Qed.

End perms1.

(** ** Liczenie wszystkich permutacji przez wstawianie *)

Module perms2.

Fixpoint ins {A : Type} (x : A) (l : list A) : list (list A) :=
match l with
    | [] => [[x]]
    | h :: t => [x :: h :: t] ++ map (cons h) (ins x t)
end.

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | h :: t => bind (ins h) (perms t)
end.

Lemma len_ins :
  forall (A : Type) (x : A) (l : list A),
    length (ins x l) = S (length l).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_map, IHt. reflexivity.
Qed.

Fixpoint nsum (l : list nat) : nat :=
match l with
    | [] => 0
    | h :: t => h + nsum t
end.

Lemma len_join :
  forall (A : Type) (ll : list (list A)),
    length (join ll) = nsum (map length ll).
Proof.
  induction ll as [| h t]; cbn.
    reflexivity.
    rewrite length_app, IHt. reflexivity.
Qed.

Lemma len_perms :
  forall (A : Type) (l : list A),
    length (perms l) = fact (length l).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite bind_spec, len_join, map_map.
Abort.

Lemma map_ins :
  forall (A B : Type) (f : A -> B) (x : A) (l : list A),
    map (map f) (ins x l) = ins (f x) (map f l).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    f_equal. rewrite <- IHt, !map_map. cbn. reflexivity.
Qed.

Lemma ins_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    l1 = [] \/
    l2 = [] \/
      ins x (l1 ++ l2) =
      map (fun l => app l l2) (ins x l1) ++
      map (app l1) (ins x l2).
Proof.
  induction l1 as [| h1 t1]; cbn.
    left. reflexivity.
    induction l2 as [| h2 t2]; cbn.
      right. left. reflexivity.
      do 2 right. decompose [or] IHt2; subst; clear IHt2.
        inversion H.
Abort.

Lemma ins_snoc :
  forall (A : Type) (x y : A) (l : list A),
    ins x (snoc y l) =
    snoc (snoc x (snoc y l)) (map (snoc y) (ins x l)).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    f_equal. rewrite IHt. rewrite map_snoc, !map_map.
      cbn. reflexivity.
Qed.

Lemma ins_rev :
  forall (A : Type) (x : A) (l : list A),
    ins x (rev l) = rev (map rev (ins x l)).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite <- !snoc_app_singl. rewrite ins_snoc, IHt.
      rewrite map_rev, map_map, <- map_rev. f_equal.
      rewrite map_rev, map_map. cbn. f_equal.
      f_equal.
Admitted.

Lemma elem_ins :
  forall (A : Type) (x : A) (l : list A),
    elem (x :: l) (ins x l).
Proof.
  destruct l; constructor.
Qed.

Lemma elem_perms :
  forall (A : Type) (l : list A),
    elem l (perms l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    rewrite bind_spec, elem_join. exists (ins h t). split.
      apply elem_ins.
      apply elem_map. assumption.
Qed.

Lemma Permutation_elem_ins :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem l2 (ins x l1) -> Permutation (x :: l1) l2.
Proof.
  induction l1 as [| h t]; cbn.
    inversion 1; subst.
      reflexivity.
      inversion H2.
    inversion 1; subst.
      reflexivity.
      rewrite elem_map_conv in H2. destruct H2 as (r & Heq & Hel).
        subst. rewrite perm_swap. constructor. apply IHt. assumption.
Qed.

Lemma Permutation_bind :
  forall (A B : Type) (f g : A -> list B) (l1 l2 : list A),
    (forall x : A, Permutation (f x) (g x)) ->
      Permutation l1 l2 ->
        Permutation (bind f l1) (bind g l2).
Proof.
  induction 2; cbn.
    constructor.
    apply Permutation_app.
      apply H.
      assumption.
    induction l as [| h t]; cbn.
      rewrite 2!app_nil_r. rewrite Permutation_app_comm.
        apply Permutation_app; apply H.
      rewrite (Permutation_app_comm _ (f h)),
              (Permutation_app_comm _ (g h)).
        rewrite !app_assoc. apply Permutation_app.
          rewrite <- !app_assoc. assumption.
          apply H.
    assert (Permutation (bind f l) (bind f l')).
      rewrite !bind_spec. apply Permutation_join, Permutation_map.
        assumption.
      rewrite H0, IHPermutation2. reflexivity.
Qed.

Lemma bind_comm :
  forall (A B C : Type) (f g: A -> list A) (l : list A),
    bind f (bind g l) =
    bind g (bind f l).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite !bind_spec, !map_app in *.
Abort.

Lemma count_join :
  forall (A : Type) (p : A -> bool) (l : list (list A)),
    count p (join l) = nsum (map (count p) l).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite count_app, IHt. reflexivity.
Qed.

Lemma nsum_app :
  forall l1 l2 : list nat,
    nsum (l1 ++ l2) = nsum l1 + nsum l2.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite IHt1, plus_assoc. reflexivity.
Qed.

Fixpoint deepcount
  {A : Type} (p : A -> bool) (l : list (list A)) : nat :=
match l with
    | [] => 0
    | h :: t => count p h + deepcount p t
end.

Lemma bind_assoc :
  forall (A B C : Type) (f : A -> list B) (g : B -> list C) (la : list A),
    bind g (bind f la) = bind (fun x => bind g (f x)) la.
Proof.
  induction la as [| ha ta]; cbn.
    reflexivity.
    intros. rewrite !bind_spec, !map_app, join_app in *.
      rewrite IHta. reflexivity.
Qed.

Lemma Permutation_bind_ins :
  forall (A : Type) (x y : A) (l : list A),
    Permutation
      (bind (ins x) (ins y l))
      (bind (ins y) (ins x l)).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    rewrite perm_swap. do 2 constructor. apply Permutation_app.
      apply Permutation_count_conv. intro.
        rewrite !count_map.
Admitted.

Lemma Permutation_perms :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (perms l1) (perms l2).
Proof.
  induction 1; cbn.
    do 2 constructor.
    rewrite 2!bind_spec. apply Permutation_join, Permutation_map.
      assumption.
    rewrite !bind_assoc. apply Permutation_bind.
      2: reflexivity.
      apply Permutation_bind_ins.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Lemma Permutation_elem_perms :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
Proof.
  intros. rewrite <- (Permutation_elem _ (perms l1)).
    apply elem_perms.
    apply Permutation_perms. assumption.
Qed.

End perms2.