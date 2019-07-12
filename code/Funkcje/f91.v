(*
  Another approach to McCarthy's f91 function without using
  induction-recursion.

  It is based on this paper:
  https://members.loria.fr/DLarchey/files/papers/TYPES_2018_paper_19.pdf

  The technique goes like this:
  1. Define the graph relation for the function.
  2. Define the domain predicate for the function using the graph relation.
  3. Prove useful stuff, like functionality ofD the graph.
  4. Define the function together with its specification using induction
     on the domain predicate.
  5. Extract the function and the specification using projections.
*)

Require Import Omega.

Inductive graph : nat -> nat -> Prop :=
    | graph_gt100 :
        forall n : nat, 100 < n -> graph n (n - 10)
    | graph_le100 :
        forall n r1 r2 : nat, n <= 100 ->
          graph (n + 11) r1 -> graph r1 r2 -> graph n r2.

Inductive dom : nat -> Type :=
    | dom_gt100 :
        forall n : nat, 100 < n -> dom n
    | dom_le100 :
        forall n r : nat, n <= 100 ->
          graph (n + 11) r -> dom (n + 11) -> dom r -> dom n.

Lemma graph_functional :
  forall n r1 r2 : nat,
    graph n r1 -> graph n r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; intros.
    inversion H0; subst.
      reflexivity.
      omega.
    inversion H2; subst.
      omega.
      assert (r1 = r3) by apply (IHgraph1 _ H4); subst.
        apply (IHgraph2 _ H5).
Qed.

Fixpoint fD' (n : nat) (d : dom n) : {r : nat | graph n r}.
Proof.
  destruct d.
    exists (n - 10). constructor. assumption.
    destruct (fD' _ d1) as [r1 g1].
      destruct (fD' _ d2) as [r2 g2]. exists r2. eapply graph_le100.
        assumption.
        exact g1.
        assert (r1 = r) by (eapply graph_functional; eauto).
          rewrite H. assumption.
Defined.

Definition fD (n : nat) (d : dom n) : nat :=
match fD' n d with
    | exist _ r _ => r
end.

Lemma fD_correct :
  forall (n : nat) (d : dom n), graph n (fD n d).
Proof.
  intros. unfold fD. destruct (fD' n d). assumption.
Qed.

Lemma fD_complete :
  forall (n r : nat) (d : dom n),
    graph n r -> fD n d = r.
Proof.
  intros. unfold fD. destruct (fD' n d).
  eapply graph_functional; eauto.
Qed.

Lemma fD_spec :
  forall (n r : nat) (d : dom n),
    fD n d = r <-> graph n r.
Proof.
  split; intro.
    rewrite <- H. apply fD_correct.
    apply fD_complete. assumption.
Qed.

(* It remains to prove that ... *)
Lemma dom_total :
  forall n : nat, dom n.
Proof.
  do 101 try (destruct n).
    Focus 100. eright. omega. apply fD_correct. constructor. omega.
      cbn.
Admitted.

Definition f (n : nat) : nat := fD n (dom_total n).

Lemma f_correct :
  forall n : nat, graph n (f n).
Proof.
  intros. apply fD_correct.
Qed.

Lemma f_complete :
  forall n r : nat,
    graph n r -> f n = r.
Proof.
  intros. apply fD_complete. assumption.
Qed.

Lemma f_spec :
  forall n r : nat,
    f n = r <-> graph n r.
Proof.
  intros. apply fD_spec.
Qed.

Lemma f_eq :
  forall n : nat,
    f n =
    if leb n 100 then f (f (n + 11)) else n - 10.
Proof.
  intros. unfold f. rewrite fD_spec.
  destruct (Nat.leb_spec0 n 100) as [H | H].
    eapply graph_le100.
      assumption.
      1-2: apply fD_correct.
    constructor. omega.
Qed.

Lemma fD_91 :
  forall (n : nat) (d : dom n),
    n <= 100 -> fD n d = 91.
Proof.
  intros. rewrite fD_spec. revert H.
  induction d; intro.
    omega.
    clear l. inversion d1; subst.
      inversion d2; subst.
        clear IHd2. inversion g; subst.
          eapply graph_le100; eauto. assert (n = 100) by omega.
            subst. cbn. constructor. omega.
          omega.
        eapply graph_le100; eauto.
      specialize (IHd1 H0). assert (r = 91).
        eapply graph_functional; eauto.
        subst. eapply graph_le100; eauto. apply IHd2. omega.
Qed.

Lemma f_ind :
  forall
    (P : nat -> nat -> Prop)
    (H_gt100 : forall n : nat, 100 < n -> P n (n - 10))
    (H_le100 :
      forall n : nat, n <= 100 ->
        P (n + 11) (f (n + 11)) -> P (f (n + 11)) (f (f (n + 11))) ->
          P n (f (f (n + 11)))),
    forall n : nat, P n (f n).
Proof.
  intros. unfold f, fD. destruct (fD' n _) as (r & H).
  induction H.
    apply H_gt100. assumption.
    rewrite <- f_spec in *. subst. apply H_le100; assumption.
Defined.

Lemma f_91 :
  forall (n : nat),
    n <= 100 -> f n = 91.
Proof.
  apply (f_ind (fun n r => n <= 100 -> r = 91)).
    intros. omega.
    intros. destruct (Nat.leb_spec0 (n + 11) 100).
      apply H1. rewrite H0.
        omega.
        assumption.
      destruct (Nat.leb_spec0 (f (n + 11)) 100).
        apply H1. assumption.
        rewrite f_eq in n1. destruct (Nat.leb_spec0 (n + 11) 100).
          omega.
          assert (n = 100) by omega. subst. cbn. rewrite 2!f_eq.
            cbn. reflexivity.
Qed.