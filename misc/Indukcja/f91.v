(*

  Another approach to McCarthy's f91 function without using
  induction-recursion.

  It is based on this paper:
  https://members.loria.fr/DLarchey/files/papers/TYPES_2018_paper_19.pdf

  The technique goes like this:
  1. Define the graph relation for the function.
  2. Define the domain predicate for the function using the graph relation.
  3. Prove useful stuff, like functionality of the graph.
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

Fixpoint f' (n : nat) (d : dom n) : {r : nat | graph n r}.
Proof.
  destruct d.
    exists (n - 10). constructor. assumption.
    destruct (f' _ d1) as [r1 g1].
      destruct (f' _ d2) as [r2 g2]. exists r2. eapply graph_le100.
        assumption.
        exact g1.
        assert (r1 = r) by (eapply graph_functional; eauto).
          rewrite H. assumption.
Defined.

Definition f (n : nat) (d : dom n) : nat :=
match f' n d with
    | exist _ r _ => r
end.

Lemma f_correct :
  forall (n : nat) (d : dom n), graph n (f n d).
Proof.
  intros. unfold f. destruct (f' n d). assumption.
Qed.

Lemma f_complete :
  forall (n r : nat) (d : dom n),
    graph n r -> f n d = r.
Proof.
  intros. unfold f. destruct (f' n d).
  eapply graph_functional; eauto.
Qed.

Lemma f_spec :
  forall (n r : nat) (d : dom n),
    f n d = r <-> graph n r.
Proof.
  split; intro.
    rewrite <- H. apply f_correct.
    apply f_complete. assumption.
Qed.

(*
Lemma f_eq :
  forall (n : nat) (d : dom n),
    f n d =
    match d with
        | dom_gt100 _ _ => n - 10
        | dom_le100 n _ H g d1 d2 => f (f _ d1) d2
    end.
*)

Lemma f91 :
  forall (n : nat) (d : dom n),
    n <= 100 -> f n d = 91.
Proof.
  intros. rewrite f_spec. revert H.
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