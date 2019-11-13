Require Import D5.

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
        admit.
        apply elem_map_conv. exists t. split.
          reflexivity.
          assumption.
Admitted.

Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
Proof.
  induction 1.
    constructor.
    cbn. rewrite bind_spec, elem_join.
      exists (map (cons x) (perms l')). split.
        apply elem_map. assumption.
        rewrite elem_map_conv. exists l. split.
          admit.
          assumption.
    cbn. rewrite bind_spec, elem_join.
      exists (map (app [y; x]) (perms l)). split.
        change (y :: x :: l) with (app [y; x] l).
          apply elem_map. admit.
        apply elem_map_conv. exists (y :: l). admit.
Abort.

Fixpoint ins {A : Type} (x : A) (l : list A) : list (list A) :=
match l with
    | [] => [[x]]
    | h :: t => [x :: h :: t] ++ map (cons h) (ins x t)
end.

Compute ins 5 [1; 2; 3].

Fixpoint perms' {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | h :: t => bind (ins h) (perms' t)
end.

Lemma elem_ins :
  forall (A : Type) (x : A) (l : list A),
    elem (x :: l) (ins x l).
Proof.
  destruct l; constructor.
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

Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (perms' l1) (perms' l2).
Proof.
  induction 1; cbn.
    do 2 constructor.
    rewrite 2!bind_spec. apply Permutation_join, Permutation_map.
      assumption.
(*    induction l as [| h t]; cbn.*)
(*      constructor.*)
      rewrite !bind_spec, !map_join.
        repeat apply Permutation_join.
        rewrite !map_map.
        apply Permutation_map_wut.
    Focus 2. rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

 Permutation_map.
Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms' l2).
Proof.
  induction 1; cbn.
    constructor.
    rewrite bind_spec, elem_join. eexists. split.
      apply elem_ins.
      apply elem_map. assumption.
    Focus 2.
    rewrite bind_spec, elem_join. eexists. split.
      apply elem_ins. cbn.
      apply elem_map.