Module attempt1.

(** Jeden konstruktor negatywny - działa. *)

Fail Inductive wut : Type :=
    | C : (wut -> bool) -> wut.

Axioms
  (wut : Type)
  (C : (wut -> bool) -> wut)
  (ind : forall
    (P : wut -> Type)
    (H : forall f : wut -> bool, P (C f)),
      {f : forall w : wut, P w |
       forall g : wut -> bool, f (C g) = H g}).

Definition bad : wut -> (wut -> bool).
Proof.
  apply (ind (fun _ => wut -> bool)).
  intro f. exact f.
Defined.

Lemma bad_sur :
  forall f : wut -> bool, exists w : wut, bad w = f.
Proof.
  intro. unfold bad. destruct (ind _).
  exists (C f). apply e.
Defined.

Lemma have_mercy_plx : False.
Proof.
  pose (diagonal := fun w => negb (bad w w)).
  destruct (bad_sur diagonal).
  unfold diagonal, bad in H. destruct (ind _).
  apply (f_equal (fun f => f x)) in H.
  destruct (x0 x x); inversion H.
Qed.

End attempt1.

Module attempt2.

(** Dwa konstruktory negatywne - działa. *)

Fail Inductive wut : Type :=
    | C0 : (wut -> bool) -> wut
    | C1 : (wut -> nat) -> wut.

Axioms
  (wut : Type)
  (C0 : (wut -> bool) -> wut)
  (C1 : (wut -> nat) -> wut)
  (ind : forall
    (P : wut -> Type)
    (PC0 : forall f : wut -> bool, P (C0 f))
    (PC1 : forall f : wut -> nat, P (C1 f)),
      {f : forall w : wut, P w |
        (forall g : wut -> bool, f (C0 g) = PC0 g) /\
        (forall g : wut -> nat, f (C1 g) = PC1 g)
      }
  ).

Definition bad :
  wut -> (wut -> bool).
Proof.
  apply (ind (fun _ => wut -> bool)).
    intro f. exact f.
    intros _ _. exact true.
Defined.

Lemma bad_sur :
  forall (f : wut -> bool), exists w : wut, bad w = f.
Proof.
  intro. unfold bad. destruct (ind _) as (g & H1 & H2).
  exists (C0 f). apply H1.
Defined.

Lemma Cantor_ty_dziwko : False.
Proof.
  destruct (bad_sur (fun w : wut => negb (bad w w))).
  unfold bad in H. destruct (ind _).
  apply (f_equal (fun f => f x)) in H.
  destruct (x0 x x); inversion H.
Qed.

End attempt2.

Module attempt3.

(** Jeden konstruktor negatywny z argumentem indukcyjnym w
    przeciwdziedzinie i drugi konstruktor normalny. *)

Fail Inductive wut : Type :=
    | C0 : (wut -> wut) -> wut
    | C1 : nat -> wut.

Axioms
  (wut : Type)
  (C0 : (wut -> wut) -> wut)
  (C1 : nat -> wut)
  (ind : forall
    (P : wut -> Type)
    (PC0 : forall f : wut -> wut, P (C0 f))
    (PC1 : forall n : nat, P (C1 n)),
      {f : forall w : wut, P w |
        (forall g : wut -> wut, f (C0 g) = PC0 g) /\
        (forall n : nat, f (C1 n) = PC1 n)
      }
  ).

Definition bad :
  wut -> (wut -> wut).
Proof.
  apply (ind (fun _ => wut -> wut)).
    intro f. exact f.
    intros _ w. exact w.
Defined.

Lemma bad_sur :
  forall (f : wut -> wut), exists w : wut, bad w = f.
Proof.
  intro. unfold bad. destruct (ind _) as (g & H1 & H2).
  exists (C0 f). apply H1.
Defined.

Definition change (w : wut) : wut.
Proof.
  revert w.
  apply (ind (fun _ => wut)).
    intro. exact (C1 0).
    intro. apply (C1 (S n)).
Defined.

Lemma change_neq :
  forall w : wut, change w <> w.
Proof.
  apply ind.
    intros f H. unfold change in H. destruct (ind _) as (g & H1 & H2).
      rewrite H1 in H. admit.
    intros n H. unfold change in H. destruct (ind _) as (g & H1 & H2).
      rewrite H2 in H. admit.
Admitted.

Lemma behemot_atakuje : False.
Proof.
  destruct (bad_sur (fun w : wut => change (bad w w))).
  unfold bad in H. destruct (ind _).
  apply (f_equal (fun f => f x)) in H.
  apply (change_neq (x0 x x)).
  symmetry. assumption.
Qed.

End attempt3.

Module attempt4.

(** Pewnie najgorsze bydle. *)

Fail Inductive wut : Type :=
    | C : (wut -> wut) -> wut.

Axioms
  (wut : Type)
  (C : (wut -> wut) -> wut)
  (ind : forall
    (P : wut -> Type)
    (PC : forall f : wut -> wut, P (C f)),
      {f : forall w : wut, P w |
        forall g : wut -> wut, f (C g) = PC g}).

Definition bad :
  wut -> (wut -> wut).
Proof.
  apply (ind (fun _ => wut -> wut)).
    intro f. exact f.
Defined.

Lemma bad_sur :
  forall (f : wut -> wut), exists w : wut, bad w = f.
Proof.
  intro. unfold bad. destruct (ind _) as (g & H).
  exists (C f). apply H.
Defined.

Definition change : wut -> wut.
Proof.
  apply (ind (fun _ => wut)).
  intro f. apply f. exact (C (fun w => C (fun v => f v))).
Defined.

Lemma change_neq :
  forall w : wut, change w <> w.
Proof.
  apply ind. intros f H.
  unfold change in H. destruct (ind _) as (g & eq).
  rewrite eq in H.
Admitted.

Lemma behemot_atakuje : False.
Proof.
Abort.

End attempt4.

(** **** Ćwiczenie *)