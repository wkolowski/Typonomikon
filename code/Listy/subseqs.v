Require Import D5.

Fixpoint subseqs {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | h :: t => map (cons h) (subseqs t) ++ subseqs t
end.

Compute subseqs [1; 2; 3; 4; 5].

Check Subseq.

Lemma Subseq_subseqs :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> elem l1 (subseqs l2).
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn.
      constructor.
      apply elem_app_r. assumption.
    apply elem_app_l, elem_map. assumption.
    apply elem_app_r. assumption.
Qed.

Lemma subseqs_Subseq :
  forall (A : Type) (l1 l2 : list A),
    elem l1 (subseqs l2) -> Subseq l1 l2.
Proof.
  intros A l1 l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inversion H; subst.
      constructor.
      inversion H2.
    apply elem_app in H. destruct H.
      rewrite elem_map_conv in H. destruct H as (x & Heq & Hel).
        subst. constructor. apply IHt2. assumption.
      constructor. apply IHt2, H.
Qed.