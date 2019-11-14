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
  intros. apply Permutation_perms in H.
  Search Permutation elem.
  rewrite <- (Permutation_elem _ (perms l1) (perms l2)).
    apply elem_perms.
    assumption.
Qed.