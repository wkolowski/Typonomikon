Require Import D5.

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

Lemma Permutation_map_wut :
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
Admitted.

Fixpoint deepcount
  {A : Type} (p : A -> bool) (l : list (list A)) : nat :=
match l with
    | [] => 0
    | h :: t => count p h + deepcount p t
end.

Lemma Permutation_perms :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (perms l1) (perms l2).
Proof.
  induction 1; cbn.
    do 2 constructor.
    rewrite 2!bind_spec. apply Permutation_join, Permutation_map.
      assumption.
    apply Permutation_count_conv. intro.
    generalize (perms l) as l'.
      induction l' as [| h t]; cbn.
        reflexivity.
        rewrite !bind_spec, !count_join, !map_app in *.
          rewrite !nsum_app, !IHt. rewrite map_map.
Restart.
  intros. apply Permutation_count_conv. intro.
  induction H; cbn.
    reflexivity.
    Search Permutation count.
    apply Permutation_count. rewrite !bind_spec.
      apply Permutation_join, Permutation_map. admit.
    rewrite !bind_spec. rewrite !map_join, !count_join.
      rewrite !map_map. f_equal. rewrite !map_join. f_equal.
      rewrite !map_map. f_equal.
      Require Import FunctionalExtensionality.
      extensionality r.
    Focus 2. rewrite IHPermutation1, IHPermutation2.
Print Permutation. Search Permutation app.
      rewrite !map_map.
    apply Permutation_count_conv'. rewrite !bind_spec, !count_join, !map_map.
Admitted.

Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
Proof.
  induction 1; cbn.
    constructor.
    rewrite bind_spec, elem_join. eexists. split.
      apply elem_ins.
      apply elem_map. assumption.
    rewrite !bind_spec, elem_join. exists (ins x (y :: l)). split.
      cbn. right. apply elem_map. apply elem_ins.
      apply elem_map, elem_join. exists (ins y l). split.
        apply elem_ins.
        apply elem_map. apply elem_perms.
    rewrite <- (Permutation_elem _ (perms l') (perms l'')).
      assumption.
      apply Permutation_perms. assumption.
Qed.
