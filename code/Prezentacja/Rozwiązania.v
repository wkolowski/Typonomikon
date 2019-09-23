(** **** Zadanie 6 *)

(*
Module Zad6.

Require Import List.
Import ListNotations.

Require Import Omega.

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Lemma wf_lengthOrder :
  forall A : Type, well_founded (@lengthOrder A).
Proof.
  intros. apply (wf_inverse_image _ _ (@length A)). apply lt_wf.
Defined.

Fixpoint split
  (n : nat) {A : Type} (l : list A) : option (list A * list A) :=
match n, l with
    | 0, _ => Some ([], l)
    | S _, [] => None
    | S n', h :: t =>
        match split n' t with
            | None => None
            | Some (l1, l2) => Some (h :: l1, l2)
        end
end.

Lemma lengthOrder_split_aux :
  forall (n : nat) (A : Type) (l : list A) (l1 l2 : list A),
    split n l = Some (l1, l2) ->
      n = 0  \/ lengthOrder l2 l.
Proof.
  induction n as [| n']; cbn; intros.
    left. reflexivity.
    right. destruct l as [| h t]; cbn in *.
      inversion H.
      case_eq (split n' t).
        intros [l1' l2'] H'. rewrite H' in H. inversion H; subst.
          destruct (IHn' A t l1' l2 H').
            rewrite H0 in *. cbn in *. inversion H'; subst.
              apply le_n.
            apply lt_trans with (length t).
              assumption.
              apply le_n.
        intro. rewrite H0 in H. inversion H.
Qed.

Lemma lengthOrder_split :
  forall (n : nat) (A : Type) (l : list A) (l1 l2 : list A),
    split (S n) l = Some (l1, l2) -> lengthOrder l2 l.
Proof.
  intros. destruct (lengthOrder_split_aux _ _ _ _ _ H).
    inversion H0.
    assumption.
Qed.

Definition rotn {A : Type} (n : nat) (l : list A) : list A.
Proof.
  revert l n.
  apply (@well_founded_induction_type _ _ (@wf_lengthOrder A)
    (fun l => nat -> list A)).
  intros l IH n.
  case_eq (split (S n) l).
    intros [l1 l2] H. refine (rev l1 ++ IH l2 _ n).
      eapply lengthOrder_split. exact H.
    intro. exact l.
Defined.

Compute rotn 1 [1; 2; 3; 4; 5; 6; 7].

Lemma rotn_eq :
  forall (A : Type) (n : nat) (l : list A),
    rotn n l =
    match split (S n) l with
        | None => l
        | Some (l1, l2) => rev l1 ++ rotn n l2
    end.
Proof.
  intros. revert l n.
  apply (@well_founded_induction _ _ (@wf_lengthOrder A)
    (fun l => forall n : nat, _)).
  intros l IH n.
  case_eq (split (S n) l).
    intros [l1 l2] H.
Admitted.

Inductive Rotn {A : Type} : nat -> list A -> list A -> Prop :=
    | Rotn_None :
        forall (n : nat) (l : list A),
          split (S n) l = None -> Rotn n l l
    | Rotn_Some :
        forall (n : nat) (l l1 l2 r : list A),
          split (S n) l = Some (l1, l2) ->
            Rotn n l2 r -> Rotn n l (rev l1 ++ r).

Lemma Rotn_complete :
  forall (A : Type) (n : nat) (l r : list A),
    Rotn n l r -> rotn n l = r.
Proof.
  induction 1.
    rewrite rotn_eq, H. reflexivity.
    rewrite rotn_eq, H, IHRotn. reflexivity.
Qed.

Lemma Rotn_correct :
  forall (A : Type) (n : nat) (l : list A),
    Rotn n l (rotn n l).
Proof.
  intros A n l. revert l n.
  apply (@well_founded_induction _ _ (@wf_lengthOrder A)
    (fun l => forall n : nat, Rotn n l (rotn n l))).
  intros l IH n.
  rewrite rotn_eq. case_eq (split (S n) l).
    intros [l1 l2] H. econstructor.
      eassumption.
      apply IH. apply (lengthOrder_split n _ l l1). assumption.
    intros. constructor. assumption.
Qed.

Lemma rotn_ind :
  forall (A : Type) (P : nat -> list A -> list A -> Prop),
    (forall (n : nat) (l : list A),
      split (S n) l = None -> P n l l) ->
    (forall (n : nat) (l l1 l2 : list A),
      split (S n) l = Some (l1, l2) ->
        P n l2 (rotn n l2) -> P n l (rev l1 ++ rotn n l2)) ->
    forall (n : nat) (l : list A), P n l (rotn n l).
Proof.
  intros A P H1 H2 n l.
  refine (Rotn_ind A P H1 _ n l (rotn n l) _).
    intros. apply Rotn_complete in H0. rewrite <- H0. apply H2.
      assumption.
      rewrite H0. assumption.
    apply Rotn_correct.
Qed.

Lemma split_None :
  forall (A : Type) (n : nat) (l : list A),
    split n l = None -> length l < n.
Proof.
  induction n as [| n']; cbn; intros.
    inversion H.
    destruct l as [| h t]; cbn in H.
      apply le_n_S, le_0_n.
      case_eq (split n' t).
        intros [l1 l2] Heq. rewrite Heq in H. inversion H.
        intro. cbn. apply lt_n_S. apply IHn'. assumption.
Qed.

Lemma split_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 = n -> split n (l1 ++ l2) = Some (l1, l2).
Proof.
  induction n as [| n']; cbn; intros.
    destruct l1; cbn.
      reflexivity.
      inversion H.
    destruct l1 as [| h t]; cbn.
      inversion H.
      rewrite IHn'.
        reflexivity.
        cbn in H. inversion H. reflexivity.
Qed.

Lemma split_length :
  forall {A : Type} {n : nat} {l1 l2 : list A},
    split n (l1 ++ l2) = Some (l1, l2) -> length l1 = n.
Proof.
  induction n as [| n']; cbn; intros.
    inversion H. reflexivity.
    destruct l1 as [| h t]; cbn in *.
      destruct l2; cbn in H.
        inversion H.
        destruct (split n' l2).
          destruct p. 1-2: inversion H.
      case_eq (split n' (t ++ l2)).
        intros [l1' l2'] Heq. eapply f_equal, IHn'.
          rewrite Heq in H. inversion H; subst. eassumption.
        intro. rewrite H0 in H. inversion H.
Qed.

Lemma split_spec :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) -> l = l1 ++ l2.
Proof.
  induction n as [| n']; cbn; intros.
    inversion H. cbn. reflexivity.
    destruct l as [| h t]; cbn.
      inversion H.
      case_eq (split n' t).
        intros [l1' l2'] H'. rewrite H' in H. inversion H.
          cbn. f_equal. apply IHn'. inversion H; subst. assumption.
        intro. rewrite H0 in H. inversion H.
Qed.

Lemma rotn_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 = S n ->
      rotn n (l1 ++ l2) = rev l1 ++ rotn n l2.
Proof.
  intros A n l1 l2 h.
  rewrite rotn_eq, split_app; auto.
Qed.

Lemma rotn_involution :
  forall (A : Type) (n : nat) (l : list A),
    rotn n (rotn n l) = l.
Proof.
  intro. apply (rotn_ind A (fun n l r => rotn n r = l)); intros.
    rewrite rotn_eq, H. reflexivity.
    rewrite rotn_app, H0, rev_involutive.
      apply split_spec in H. rewrite H. reflexivity.
      rewrite rev_length. eapply split_length. rewrite <- H.
        f_equal. apply split_spec in H. rewrite H. reflexivity.
Qed.

End Zad6.
*)