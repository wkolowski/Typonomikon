(** *** Przemienność *)

Lemma and_comm :
  forall P Q : Prop, P /\ Q -> Q /\ P.
(* begin hide *)
Proof.
  destruct 1; split; assumption.
Qed.
(* end hide *)

Lemma or_comm :
  forall P Q : Prop, P \/ Q -> Q \/ P.
(* begin hide *)
Proof.
  destruct 1; [right | left]; assumption.
Qed.
(* end hide *)

(** *** Łączność *)

Lemma and_assoc :
  forall P Q R : Prop, P /\ (Q /\ R) <-> (P /\ Q) /\ R.
(* begin hide *)
Proof.
  split; intros.
    destruct H as [p [q r]]. repeat split; assumption.
    destruct H as [[p q] r]. repeat split; assumption.
Restart.
  split; intros; repeat
  match goal with
      | H : _ /\ _ |- _ => destruct H
  end; repeat split; assumption.
Qed.
(* end hide *)

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
(* begin hide *)
Proof.
  split; intros.
    destruct H as [p | [q | r]].
      left. left. assumption.
      left. right. assumption.
      right. assumption.
    destruct H as [[p | q] | r].
      left. assumption.
      right. left. assumption.
      right. right. assumption.
Qed.
(* end hide *)

(** *** Rozdzielność *)

Lemma and_dist_or :
  forall P Q R : Prop, P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
(* begin hide *)
Proof.
  split; intros.
    destruct H as [p [q | r]].
      left. split; assumption.
      right. split; assumption.
    destruct H as [[p q] | [p r]].
      split. assumption. left. assumption.
      split. assumption. right. assumption.
Qed.
(* end hide *)

Lemma or_dist_and :
  forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
(* begin hide *)
Proof.
  split; intros.
    destruct H as [p | [q r]].
      split; left; assumption.
      split; right; assumption.
    destruct H as [[p1 | q] [p2 | r]].
      left. assumption.
      left. assumption.
      left. assumption.
      right. split; assumption.
Restart.
  split; intros.
    destruct H as [p | [q r]];
      split; ((left; assumption) || (right; assumption)).
    destruct H as [[p1 | q] [p2 | r]];
      ((left; assumption) || (right; split; assumption)).
Qed.
(* end hide *)

Lemma imp_dist_imp :
  forall P Q R : Prop, (P -> Q -> R) <-> ((P -> Q) -> (P -> R)).
(* begin hide *)
Proof.
  split; intros.
    apply H.
      assumption.
      apply H0. assumption.
    apply H.
      intro. assumption.
      assumption.
Restart.
  split; intros; apply H; intros; try apply H0; assumption.
Qed.
(* end hide *)

(** *** Kuryfikacja i dekuryfikacja *)

Lemma curry :
  forall P Q R : Prop, (P /\ Q -> R) -> (P -> Q -> R).
(* begin hide *)
Proof.
  intros; apply H; split; assumption.
Qed.
(* end hide *)

Lemma uncurry :
  forall P Q R : Prop, (P -> Q -> R) -> (P /\ Q -> R).
(* begin hide *)
Proof.
  intros * pqr pq.
  destruct pq as [p q].
  apply pqr.
    assumption.
    assumption.
Qed.
(* end hide *)

(** *** Prawa de Morgana *)

Lemma deMorgan_1 :
  forall P Q : Prop, ~ (P \/ Q) <-> ~ P /\ ~ Q.
(* begin hide *)
Proof.
  split.
    intro npq. split.
      intro p. apply npq. left. assumption.
      intro q. apply npq. right. assumption.
    intros npnq npq. destruct npnq as [np nq]. destruct npq.
      apply np. assumption.
      apply nq. assumption.
Qed.
(* end hide *)

Lemma deMorgan_2 :
  forall P Q : Prop, ~ P \/ ~ Q -> ~ (P /\ Q).
(* begin hide *)
Proof.
  intros * npnq pq.
  destruct pq as [p q].
  destruct npnq as [np | nq].
    apply np. assumption.
    apply nq. assumption.
Qed.
(* end hide *)

(** *** Niesprzeczność i zasada wyłączonego środka *)

Lemma noncontradiction' :
  forall P : Prop, ~ (P /\ ~ P).
(* begin hide *)
Proof.
  unfold not; intros. destruct H. apply H0. assumption.
Qed.
(* end hide *)

Lemma noncontradiction_v2 :
  forall P : Prop, ~ (P <-> ~ P).
(* begin hide *)
Proof.
  intros * H.
  destruct H as [lr rl].
  apply lr.
    apply rl. intro p. apply lr.
      assumption.
      assumption.
    apply rl. intro p. apply lr.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma em_irrefutable :
  forall P : Prop, ~ ~ (P \/ ~ P).
(* begin hide *)
Proof.
  intros * H.
  apply H.
  right. intro p.
  apply H.
  left. assumption.
Qed.
(* end hide *)

(** *** Elementy neutralne i anihilujące *)

Lemma and_false_annihilation :
  forall P : Prop, P /\ False <-> False.
(* begin hide *)
Proof.
  split; intro H.
    destruct H. contradiction.
    contradiction.
Qed.
(* end hide *)

Lemma or_false_neutral :
  forall P : Prop, P \/ False <-> P.
(* begin hide *)
Proof.
  split.
    intro H. destruct H.
      assumption.
      contradiction.
    intro p. left. assumption.
Qed.
(* end hide *)

Lemma and_true_neutral :
  forall P : Prop, P /\ True <-> P.
(* begin hide *)
Proof.
  split.
    intro H. destruct H as [p t]. assumption.
    intro p. split.
      assumption.
      trivial.
Qed.
(* end hide *)

Lemma or_true_annihilation :
  forall P : Prop, P \/ True <-> True.
(* begin hide *)
Proof.
  split.
    intros _. trivial.
    intros _. right. trivial.
Qed.
(* end hide *)

(** *** Inne *)

Lemma or_imp_and :
  forall P Q R : Prop, (P \/ Q -> R) <-> (P -> R) /\ (Q -> R).
(* begin hide *)
Proof.
  split.
    intro H. split.
      intro p. apply H. left. assumption.
      intro q. apply H. right. assumption.
    intros H1 H2. destruct H1 as [pr qr]. destruct H2 as [p | q].
      apply pr. assumption.
      apply qr. assumption.
Qed.
(* end hide *)

Lemma and_not_imp :
  forall P Q : Prop, P /\ ~ Q -> ~ (P -> Q).
(* begin hide *)
Proof.
  intros * H pq. destruct H as [p nq].
  apply nq. apply pq. assumption.
Qed.
(* end hide *)

Lemma or_not_imp :
  forall P Q : Prop, ~ P \/ Q -> (P -> Q).
(* begin hide *)
Proof.
  intros * H p. destruct H as [np | q].
    contradiction.
    assumption.
Qed.
(* end hide *)

Lemma contraposition :
  forall P Q : Prop, (P -> Q) -> (~ Q -> ~ P).
(* begin hide *)
Proof.
  intros * pq nq p. apply nq, pq, p.
Qed.
(* end hide *)

Lemma absurd :
  forall P Q : Prop, ~ P -> P -> Q.
(* begin hide *)
Proof.
  intros np p. contradiction.
Qed.
(* end hide *)

Lemma impl_and :
  forall P Q R : Prop, (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
(* begin hide *)
Proof.
  split; intro H'; destruct (H H'); assumption.
Qed.
(* end hide *)

(** *** Projekcje *)

Lemma forall_and_proj1 :
  forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x /\ Q x) -> (forall x : A, P x).
(* begin hide *)
Proof.
  intros. destruct (H x). assumption.
Qed.
(* end hide *)

Lemma forall_and_proj2 :
  forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x /\ Q x) -> (forall x : A, Q x).
(* begin hide *)
Proof.
  intros. destruct (H x). assumption.
Qed.
(* end hide *)

(** *** Rozdzielność *)

Lemma forall_dist_and :
  forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x /\ Q x) <->
    (forall x : A, P x) /\ (forall x : A, Q x).
(* begin hide *)
Proof.
  split.
    intros. split.
      intros. destruct (H x). assumption.
      intros. destruct (H x). assumption.
    intros. split.
      destruct H. apply H.
      destruct H. apply H0.
Restart.
  split; intros; split; intros; try destruct H; try (destruct (H x));
  try assumption; try apply H; try apply H0.
Qed.
(* end hide *)

Lemma exists_dist_or :
  forall (A : Type) (P Q : A -> Prop),
    (exists x : A, P x \/ Q x) <->
    (exists x : A, P x) \/ (exists x : A, Q x).
(* begin hide *)
Proof.
  split; intros.
    destruct H as [x [HP | HQ]].
      left. exists x. assumption.
      right. exists x. assumption.
    destruct H as [[x HP] | [x HQ]].
      exists x. left. assumption.
      exists x. right. assumption.
Restart.
  split; intros.
    destruct H as [x [HP | HQ]];
      [left | right]; exists x; assumption.
    destruct H as [[x HP] | [x HQ]];
      exists x; [left | right]; assumption.
Qed.
(* end hide *)

Lemma ex_dist_and :
  forall (A : Type) (P Q : A -> Prop),
    (exists x : A, P x /\ Q x) ->
      (exists y : A, P y) /\ (exists z : A, Q z).
(* begin hide *)
Proof.
  intros. destruct H as [x H]. destruct H.
  split; exists x; assumption.
Qed.
(* end hide *)

(** *** Inne *)

Lemma forall_or_imp :
  forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x) \/ (forall x : A, Q x) ->
      forall x : A, P x \/ Q x.
(* begin hide *)
Proof.
  destruct 1; intros.
    left. apply H.
    right. apply H.
Restart.
  destruct 1; intros; [left | right]; apply H.
Qed.
(* end hide *)

Lemma forall_imp_imp :
  forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x -> Q x) ->
      (forall x : A, P x) -> (forall x : A, Q x).
(* begin hide *)
Proof.
  intros. apply H. apply H0.
Qed.
(* end hide *)

Lemma forall_inhabited_nondep :
  forall (A : Type) (R : Prop),
    A -> ((forall x : A, R) <-> R).
(* begin hide *)
Proof.
  split; intros.
    apply H. assumption.
    assumption.
Restart.
  split; intros; try apply H; assumption.
Qed.
(* end hide *)

Lemma forall_or_nondep :
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x : A, P x) \/ Q -> (forall x : A, P x \/ Q).
(* begin hide *)
Proof.
  destruct 1; intros.
    left. apply H.
    right. assumption.
Qed.
(* end hide *)

Lemma forall_nondep_impl :
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x : A, Q -> P x) <-> (Q -> forall x : A, P x).
(* begin hide *)
Proof.
  split; intros.
    apply H. assumption.
    apply H. assumption.
Restart.
  split; intros; apply H; assumption.
Qed.
(* end hide *)

(** * Inne *)

Lemma constructive_dilemma :
  forall P Q R S : Prop,
    (P -> R) -> (Q -> S) -> P \/ Q -> R \/ S.
(* begin hide *)
Proof.
  intros P Q R S PR QS H.
  destruct H as [p | q].
    left. apply PR. assumption.
    right. apply QS. assumption.
Qed.
(* end hide *)

Lemma destructive_dilemma :
  forall P Q R S : Prop,
    (P -> R) -> (Q -> S) -> ~ R \/ ~ S -> ~ P \/ ~ Q.
(* begin hide *)
Proof.
  intros P Q R S PR QS H.
  destruct H as [nr | ns].
    left. intro p. apply nr, PR. assumption.
    right. intro q. apply ns, QS. assumption.
Qed.
(* end hide *)

Lemma idempotency_of_entailment :
  forall P Q : Prop,
    (P -> Q) <-> (P -> P -> Q).
(* begin hide *)
Proof.
  split.
    intros pq p1 p2. apply pq. assumption.
    intros ppq p. apply ppq.
      assumption.
      assumption.
Qed.
(* end hide *)

(** ** Klasyczny rachunek zdań (i kwantyfikatorów) *)

Require Import Classical.

Lemma imp_and_or :
  forall P Q R : Prop,
    (P -> Q \/ R) -> ((P -> Q) \/ (P -> R)).
(* begin hide *)
Proof.
  intros. destruct (classic P) as [HP | HnotP].
    destruct (H HP); [left | right]; intro; assumption.
    left. intro. cut False.
      inversion 1.
      apply HnotP. apply H0.
Qed.
(* end hide *)

Lemma deMorgan_2_conv :
  forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
(* begin hide *)
Proof.
  intros P Q npq.
  destruct (classic P) as [p | np].
    destruct (classic Q) as [q | nq].
      contradiction npq. split; assumption.
      right. assumption.
    left. assumption.
Qed.
(* end hide *)

Lemma not_impl :
  forall P Q : Prop,
    ~ (P -> Q) -> P /\ ~ Q.
(* begin hide *)
Proof.
  intros * npq. split.
    destruct (classic P).
      assumption.
      exfalso. apply npq. intro p. contradiction.
    intro q. apply npq. intros _. assumption.
Qed.
(* end hide *)

Lemma impl_not_or :
  forall P Q : Prop,
    (P -> Q) -> (~ P \/ Q).
(* begin hide *)
Proof.
  intros P Q pq.
  destruct (classic P).
    right. apply pq. assumption.
    left. assumption.
Qed.
(* end hide *)

Lemma material_implication :
  forall P Q : Prop, (P -> Q) <-> (~P \/ Q).
(* begin hide *)
Proof.
  split; intros.
    destruct (classic P).
      right. apply H. assumption.
      left. intro. contradiction.
    destruct H.
      contradiction.
      assumption.
Qed.
(* end hide *)

Lemma contraposition_conv :
  forall P Q : Prop,
    (~ Q -> ~ P) -> (P -> Q).
(* begin hide *)
Proof.
  intros * qp p.
  destruct (classic Q).
    assumption.
    exfalso. apply qp; assumption.
Qed.
(* end hide *)

Lemma excluded_middle :
  forall P : Prop, P \/ ~P.
(* begin hide *)
Proof.
  apply classic.
Qed.
(* end hide *)

Lemma peirce :
  forall P Q : Prop, ((P -> Q) -> P) -> P.
(* begin hide *)
Proof.
  intros * pqp.
  destruct (classic P).
    assumption.
    apply pqp. intro p. contradiction.
Qed.
(* end hide *)