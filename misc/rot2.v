

Fixpoint rot2 {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [x] => [x]
    | x :: y :: t => y :: x :: rot2 t
end.

Lemma rot2_involution :
  forall (A : Type) (l : list A),
    rot2 (rot2 l) = l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct t; cbn.
      reflexivity.
      cbn in *.
Abort.

Fixpoint list_ind_2
  {A : Type} (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (Hcons2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
  (l : list A) : P l :=
match l with
    | [] => Hnil
    | [x] => Hsingl x
    | x :: y :: l' => Hcons2 x y l' (list_ind_2 P Hnil Hsingl Hcons2 l')
end.

Lemma rot2_involution :
  forall (A : Type) (l : list A),
    rot2 (rot2 l) = l.
Proof.
  intro. apply list_ind_2; cbn; intros.
    1-2: reflexivity.
    rewrite H. reflexivity.
Qed.

Inductive Rot2 {A : Type} : list A -> list A -> Prop :=
    | Rot2_nil : Rot2 [] []
    | Rot2_singl : forall x : A, Rot2 [x] [x]
    | Rot2_cons2 :
        forall (x y : A) (l l' : list A),
          Rot2 l l' -> Rot2 (x :: y :: l) (y :: x :: l').

Lemma Rot2_correct :
  forall (A : Type) (l : list A),
    Rot2 l (rot2 l).
Proof.
  intro. apply list_ind_2; cbn; constructor. assumption.
Qed.

Lemma Rot2_complete :
  forall (A : Type) (l l' : list A),
    Rot2 l l' -> rot2 l = l'.
Proof.
  induction 1; cbn.
    1-2: reflexivity.
    rewrite IHRot2. reflexivity.
Qed.



Definition split' :
  forall (n : nat) {A : Type} (l : list A),
    (length l < S n) +
    {l1 : list A & {l2 : list A |
      l = l1 ++ l2 /\ lengthOrder l2 l}}.
Proof.
  refine
  (fix split' (n : nat) {A : Type} (l : list A) :=
    match n, l with
      | 0, [] => inl _
      | 0, _ => inr _
      | S _, [] => inl _
      | S n', h :: t =>
          match @split' n' A t with
              | inl _ => inl _
              | inr _ => inr _
          end
    end).
  apply le_n.
  exists [y], l0. split.
    cbn. reflexivity.
    apply le_n.
  cbn. apply le_n_S, le_0_n.
  cbn. apply lt_n_S. assumption.
  destruct s as (l1 & l2 & H1 & H2).
    exists (h :: l1), l2. split.
      cbn. f_equal. apply H1.
      apply lt_trans with (length t).
        assumption.
        apply le_n.
Defined.

Definition rotn' {A : Type} (n : nat) (l : list A) : list A.
Proof.
  revert l n.
  apply (@well_founded_induction_type _ _ (@wf_lengthOrder A)
    (fun l => nat -> list A)).
  intros l IH n.
  destruct (split' n l) as [| (l1 & l2 & H1 & H2)].
    exact l.
    exact (rev l1 ++ IH l2 H2 n).
Defined.


(*
Inductive Rotn {A : Type} : nat -> list A -> list A -> Prop :=
    | Rotn_nil : forall n : nat, Rotn n [] []
    | Rotn_short :
        forall (n : nat) (l : list A),
          length l < S n -> Rotn n l l
    | Rotn_long :
        forall (n : nat) (l1 l2 r : list A),
          length l1 = n -> Rotn n l2 r -> Rotn n (l1 ++ l2) (rev l1 ++ r).
*)

Require Import Coq.Program.Equality.

Lemma rotn'_eq :
  forall (A : Type) (n : nat) (l : list A),
    rotn' n l =
    match split' n l with
        | inl _ => l
        | inr (existT _ l1 (exist _ l2 _)) => rev l1 ++ rotn' n l2
    end.
Proof.
  intros. revert l n.
  apply (@well_founded_induction _ _ (@wf_lengthOrder A)
    (fun l => forall n : nat, _)).
  intros l IH n.
  cbn. destruct (split' n l) as [| (l1 & l2 & H1 & H2)].
    reflexivity.
    f_equal. specialize (IH _ H2 n). case_eq (split' n l2).
      intros H3 H4. unfold rotn' in *. cbn in IH. rewrite H4 in *.
    destruct (split' n l2).
      cbn.
    rewrite IH.
    Focus 2. intro. cbn. destruct l; cbn.
      reflexivity.
      cbn in H.
      inversion H. rewrite H1. rewrite H.
    intros [l1 l2] H. specialize (IH l2). rewrite  cbn. dependent rewrite H.
  cbn. dependent destruction (.
Admitted.