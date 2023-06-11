(** * B1z: Inne spójniki? [TODO] *)

From Typonomikon Require Export B1.

(** * Różnica między "lub" i "albo" *)

Definition xor (A B : Prop) : Prop :=
  (A /\ ~ B) \/ (~ A /\ B).

Lemma xor_irrefl :
  forall P : Prop, ~ xor P P.
(* begin hide *)
Proof.
  unfold xor. intros A H.
  destruct H as [[p np] | [np p]].
    apply np. assumption.
    apply np. assumption.
Qed.
(* end hide *)

Lemma xor_comm :
  forall P Q : Prop, xor P Q -> xor Q P.
(* begin hide *)
Proof.
  unfold xor. intros P Q H.
  destruct H as [[p nq] | [q np]].
    right. split; assumption.
    left. split; assumption.
Qed.
(* end hide *)

Lemma xor_comm' :
  forall P Q : Prop, xor P Q <-> xor Q P.
(* begin hide *)
Proof.
  split; apply xor_comm.
Qed.
(* end hide *)

Lemma xor_cotrans :
  (forall P : Prop, P \/ ~ P) ->
    (forall P Q R : Prop, xor P Q -> xor P R \/ xor Q R).
(* begin hide *)
Proof.
  unfold xor. intros LEM P Q R H.
  destruct H as [[p nq] | [q np]].
    destruct (LEM R) as [r | nr].
      right. right. split; assumption.
      left. left. split; assumption.
    destruct (LEM R) as [r | nr].
      left. right. split; assumption.
      right. left. split; assumption.
Qed.
(* end hide *)

Lemma Irrefutable_xor_cotrans :
  forall P Q R : Prop, ~ ~ (xor P Q -> xor P R \/ xor Q R).
(* begin hide *)
Proof. unfold xor; firstorder. Qed.
(* end hide *)

Lemma not_iff_xor :
  forall P Q : Prop, xor P Q -> ~ (P <-> Q).
(* begin hide *)
Proof.
  unfold xor, iff.
  intros P Q H1 H2.
  destruct H2 as [pq qp], H1 as [[p nq] | [np q]].
    apply nq, pq. assumption.
    apply np, qp. assumption.
Qed.
(* end hide *)

Lemma Irrefutable_xor_not_iff :
  forall P Q : Prop, ~ ~ (~ (P <-> Q) -> xor P Q).
(* begin hide *)
Proof. unfold xor; firstorder. Qed.
(* end hide *)

Lemma xor_spec :
  forall P Q : Prop, xor P Q <-> (P \/ Q) /\ (~ P \/ ~ Q).
(* begin hide *)
Proof.
  unfold xor, iff. split.
    intros [[p nq] | [np q]].
      split.
        left. assumption.
        right. assumption.
      split.
        right. assumption.
        left. assumption.
    intros [[p | q] [np | nq]].
      contradiction.
      left. split; assumption.
      right. split; assumption.
      contradiction.
Qed.
(* end hide *)

Lemma xor_False_r :
  forall P : Prop, xor P False <-> P.
(* begin hide *)
Proof.
  unfold xor, iff. split.
    intro H. destruct H as [[p _] | [_ f]].
      assumption.
      contradiction.
    intro p. left. split.
      assumption.
      intro f. contradiction.
Qed.
(* end hide *)

Lemma xor_False_l :
  forall P : Prop, xor False P <-> P.
(* begin hide *)
Proof.
  split.
    intro x. apply xor_comm in x. apply xor_False_r. assumption.
    intro p. unfold xor. right. split.
      intro f. contradiction.
      assumption.
Qed.
(* end hide *)

Lemma xor_True_l :
  forall P : Prop, xor True P <-> ~ P.
(* begin hide *)
Proof.
  unfold xor, iff. split.
    intros [[_ np] | [f _]].
      assumption.
      contradiction.
    intro np. left. split.
      trivial.
      assumption.
Qed.
(* end hide *)

Lemma xor_True_r :
  forall P : Prop, xor P True <-> ~ P.
(* begin hide *)
Proof.
  split.
    destruct 1 as [[p nt] | [np t]].
      contradiction.
      assumption.
    intro. right. split.
      assumption.
      trivial.
Qed.
(* end hide *)

(** ** Nowy podrozdział [xor] *)

Module xor_new.

Infix "`xor`" := xor (at level 85, right associativity).

Parameters P Q R : Prop.

Lemma xor_True_l :
  True `xor` P <-> ~ P.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_True_r :
  P `xor` True <-> ~ P.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_False_l :
  False `xor` P <-> P.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_False_r :
  P `xor` False <-> P.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_True_l' :
  P -> P `xor` Q <-> ~ Q.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_True_r' :
  Q -> P `xor` Q <-> ~ P.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_False_l' :
  ~ P -> P `xor` Q <-> Q.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_False_r' :
  ~ Q -> P `xor` Q <-> P.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_irrefl :
  P `xor` P <-> False.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_comm :
  P `xor` Q <-> Q `xor` P.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma Irrefutable_xor_assoc :
  ~ ~ (P `xor` (Q `xor` R) <-> (P `xor` Q) `xor` R).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma or_xor :
  P `xor` Q -> P \/ Q.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma and_xor_l :
  (P `xor` Q) /\ R <-> (P /\ R) `xor` (Q /\ R).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma and_xor_r :
  P /\ (Q `xor` R) <-> (P /\ Q) `xor` (P /\ R).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma Irrefutable_not_xor_l :
  ~ ~ (~ (P `xor` Q) <-> ~ P `xor` Q).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma Irrefutable_not_xor_r :
  ~ ~ (~ (P `xor` Q) <-> P `xor` ~ Q).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma Irrefutable_xor_not :
  ~ ~ ((~ P) `xor` ~ Q -> P `xor` Q).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_not_conv :
  P `xor` Q -> ~ P `xor` ~ Q.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_isolation :
  (P /\ ~ Q) `xor` (P /\ Q) -> P.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma Irrefutable_xor_isolation_conv :
  ~ ~ (P -> (P /\ ~ Q) `xor` (P /\ Q)).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma Irrefutable_dd_and_xor :
  ~ ~ (P /\ (~ P `xor` Q) -> P /\ Q).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma dd_and_xor_conv :
  P /\ Q -> P /\ (~ P `xor` Q).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma dd_or_xor_r :
  P \/ (P `xor` Q) -> P \/ Q.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma Irrefutable_dd_or_xor_r_conv :
  ~ ~ (P \/ Q -> P \/ (P `xor` Q)).
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma dd_impl_xor_r :
  P -> (~ P `xor` Q) <-> P -> Q.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma dd_impl_xor_l :
  (P `xor` Q) -> Q <-> P -> Q.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

End xor_new.

(** * Zdecyduj się pan, czyli spójnik "i/lub"  *)

Definition andor (P Q : Prop) : Prop := P \/ Q \/ (P /\ Q).

Lemma and_or_l :
  forall P Q : Prop, P /\ Q -> P \/ Q.
(* begin hide *)
Proof.
  destruct 1 as [p q]. left. assumption.
Qed.
(* end hide *)

Lemma and_or_r :
  forall P Q : Prop, P /\ Q -> P \/ Q.
(* begin hide *)
Proof.
  destruct 1 as [p q]. right. assumption.
Qed.
(* end hide *)

Lemma andor_or :
  forall P Q : Prop, andor P Q <-> P \/ Q.
(* begin hide *)
Proof.
  unfold andor. intros P Q. split.
  - intros [p | [q | [p q]]].
    + left. assumption.
    + right. assumption.
    + left. assumption.
  - intros [p | q].
    + left. assumption.
    + right. left. assumption.
Qed.
(* end hide *)

(** ** i/lub po raz drugi *)

Definition andxor (P Q : Prop) : Prop := xor P (xor Q (P /\ Q)).

Lemma andxor_or :
  (forall P : Prop, P \/ ~ P) ->
    forall P Q : Prop, andxor P Q <-> P \/ Q.
(* begin hide *)
Proof.
  unfold andxor. intros lem P Q. split.
  - intros [[p _] | [_ [[q _] | H]]].
    + left. assumption.
    + right. assumption.
    + destruct H as (nq & _ & q). contradiction.
  - intros [p | q].
    + left. split.
      * assumption.
      * unfold xor. intros [[q npq] | (nq & _ & q)].
        -- apply npq. split; assumption.
        -- contradiction.
    + destruct (lem P) as [p | np].
      * left. split; [assumption |]. unfold xor. tauto.
      * right. split; [assumption |]. unfold xor. tauto.
Qed.
(* end hide *)

Lemma Irrefutable_andxor_or :
  forall P Q : Prop, ~ ~ (andxor P Q <-> P \/ Q).
(* begin hide *)
Proof. unfold andxor; firstorder. Qed.
(* end hide *)

(** * Ani [P] ani [Q], czyli negacja dysjunkcji *)

Definition nor (P Q : Prop) : Prop := ~ (P \/ Q).

Lemma nor_comm :
  forall P Q : Prop,
    nor P Q <-> nor Q P.
(* begin hide *)
Proof.
  unfold nor. intros P Q. split.
  - intros f [q | p]; apply f; [right | left]; assumption.
  - intros f [p | q]; apply f; [right | left]; assumption.
Qed.
(* end hide *)

Lemma not_nor_assoc :
  exists P Q R : Prop,
    nor (nor P Q) R /\ ~ nor P (nor Q R).
(* begin hide *)
Proof.
  unfold nor. exists True, True, False. tauto.
Qed.
(* end hide *)

Lemma nor_True_l :
  forall P : Prop,
    nor True P <-> False.
(* begin hide *)
Proof.
  unfold nor.
  intros P. split.
  - intros f. apply f. left. trivial.
  - contradiction.
Qed.
(* end hide *)

Lemma nor_True_r :
  forall P : Prop,
    nor P True <-> False.
(* begin hide *)
Proof.
  unfold nor. intros P; split.
  - intros f. apply f. right. trivial.
  - contradiction.
Qed.
(* end hide *)

Lemma nor_False_l :
  forall P : Prop,
    nor False P <-> ~ P.
(* begin hide *)
Proof.
  unfold nor.
  split.
  - intros f p. apply f. right. assumption.
  - intros np [f | p]; contradiction.
Qed.
(* end hide *)

Lemma nor_False_r :
  forall P : Prop,
    nor P False <-> ~ P.
(* begin hide *)
Proof.
  unfold nor. intros P; split.
  - intros f p. apply f. left. assumption.
  - intros np [p | f]; contradiction.
Qed.
(* end hide *)

Lemma nor_antiidempotent :
  forall P : Prop,
    nor P P <-> ~ P.
(* begin hide *)
Proof.
  unfold nor. split.
  - intros f p. apply f. left. assumption.
  - intros f [p | p]; contradiction.
Qed.
(* end hide *)

(** W nieco innej wersji. *)

Definition nor' (P Q : Prop) : Prop := ~ P /\ ~ Q.

Lemma nor'_comm :
  forall P Q : Prop,
    nor' P Q <-> nor' Q P.
(* begin hide *)
Proof.
  unfold nor'.
  intros P Q. split.
  - intros [np nq]. split; assumption.
  - intros [nq np]. split; assumption.
Qed.
(* end hide *)

Lemma not_nor'_assoc :
  exists P Q R : Prop,
    nor' (nor' P Q) R /\ ~ nor' P (nor' Q R).
(* begin hide *)
Proof.
  unfold nor'. exists True, True, False. tauto.
Qed.
(* end hide *)

Lemma nor'_True_l :
  forall P : Prop,
    nor' True P <-> False.
(* begin hide *)
Proof.
  unfold nor'.
  intros P. split.
  - intros [? _]. contradiction.
  - contradiction.
Qed.
(* end hide *)

Lemma nor'_True_r :
  forall P : Prop,
    nor' P True <-> False.
(* begin hide *)
Proof.
  unfold nor'. intros P; split.
  - intros [_ ?]. contradiction.
  - contradiction.
Qed.
(* end hide *)

Lemma nor'_False_l :
  forall P : Prop,
    nor' False P <-> ~ P.
(* begin hide *)
Proof.
  unfold nor'. intros P. split.
  - intros [_ np]. assumption.
  - intros np. split.
    + intros e. contradiction.
    + assumption.
Qed.
(* end hide *)

Lemma nor'_False_r :
  forall P : Prop,
    nor' P False <-> ~ P.
(* begin hide *)
Proof.
  unfold nor'. intros P; split.
  - intros [np _]. assumption.
  - intros np. split.
    + assumption.
    + intros e. contradiction.
Qed.
(* end hide *)

Lemma nor'_antiidempotent :
  forall P : Prop,
    nor' P P <-> ~ P.
(* begin hide *)
Proof.
  unfold nor'. split.
  - intros [np _]. assumption.
  - intros np. split; assumption.
Qed.
(* end hide *)

(** Równoważność *)

Lemma nor_nor' :
  forall P Q : Prop, nor P Q <-> nor' P Q.
(* begin hide *)
Proof.
  unfold nor, nor'; split.
  - intros f. split.
    + intros p. apply f. left. assumption.
    + intros q. apply f. right. assumption.
  - intros [np nq] [p | q]; contradiction.
Qed.
(* end hide *)

(** * [nand], czyli negacja koniunkcji *)

Definition nand (P Q : Prop) : Prop := ~ (P /\ Q).

Lemma nand_comm :
  forall P Q : Prop,
    nand P Q <-> nand Q P.
(* begin hide *)
Proof.
  unfold nand.
  intros P. split.
  - intros f [q p]. apply f; split; assumption.
  - intros f [p q]. apply f; split; assumption.
Qed.
(* end hide *)

Lemma not_nand_assoc :
  exists P Q R : Prop,
    nand (nand P Q) R /\ ~ nand P (nand Q R).
(* begin hide *)
Proof.
  unfold nand. exists True, True, False. tauto.
Qed.
(* end hide *)

Lemma nand_True_l :
  forall P : Prop,
    nand True P <-> ~ P.
(* begin hide *)
Proof.
  unfold nand.
  intros P. split.
  - intros f p. apply f. split; trivial.
  - intros np [_ p]. contradiction.
Qed.
(* end hide *)

Lemma nand_True_r :
  forall P : Prop,
    nand P True <-> ~ P.
(* begin hide *)
Proof.
  unfold nand; intros P; split.
  - intros f p. apply f. split; trivial.
  - intros np [p _]. contradiction.
Qed.
(* end hide *)

Lemma nand_False_l' :
  forall P : Prop,
    nand False P.
(* begin hide *)
Proof.
  unfold nand. intros P [[] _].
Qed.
(* end hide *)

Lemma nand_False_l :
  forall P : Prop,
    nand False P <-> True.
(* begin hide *)
Proof.
  split; intros.
  - trivial.
  - apply nand_False_l'.
Qed.
(* end hide *)

Lemma nand_False_r :
  forall P : Prop,
    nand P False <-> True.
(* begin hide *)
Proof.
  unfold nand; intros P; split.
  - intros _. trivial.
  - intros _ [p f]. contradiction.
Qed.
(* end hide *)

Lemma nand_antiidempotent :
  forall P : Prop,
    nand P P <-> ~ P.
(* begin hide *)
Proof.
  unfold nand. split.
  - intros f p. apply f. split; assumption.
  - intros np [p _]. contradiction.
Qed.
(* end hide *)

(** * Antyimplikacja, czyli negacja implikacji *)

Definition nimpl (P Q : Prop) : Prop := ~ (P -> Q).

Lemma nimpl_False_l :
  forall P : Prop,
    ~ nimpl False P.
(* begin hide *)
Proof.
  unfold nimpl.
  intros P f. apply f. intros c. contradiction.
Qed.
(* end hide *)

Lemma nimpl_False_r:
  forall P : Prop,
    nimpl P False <-> ~ ~ P.
(* begin hide *)
Proof.
  unfold nimpl.
  intros P; split; intros; assumption.
Qed.
(* end hide *)

Lemma nimpl_True_l :
  forall P : Prop,
    nimpl True P <-> ~ P.
(* begin hide *)
Proof.
  unfold nimpl.
  intros P; split.
  - intros f p. apply f. intros _. assumption.
  - intros f p. apply f, p. trivial.
Qed.
(* end hide *)

Lemma nimpl_True_r :
  forall P : Prop,
    ~ nimpl P True.
(* begin hide *)
Proof.
  unfold nimpl.
  intros P f. apply f. intros _. trivial.
Qed.
(* end hide *)

Lemma nimpl_conv :
  forall P Q : Prop,
    nimpl (~ P) (~ Q) -> nimpl P Q.
(* begin hide *)
Proof.
  unfold nimpl.
  intros P Q f g.
  apply f. intros np q.
Abort.
(* end hide *)

Lemma nimpl_conv :
  forall P Q : Prop,
    nimpl P Q -> nimpl (~ Q) (~ P).
(* begin hide *)
Proof.
  unfold nimpl.
  intros P Q f g.
  apply f. intros p.
Abort.
(* end hide *)

(** **** Ćwiczenie (conditioned disjunction) *)

(** #<a class='link' href='https://en.wikipedia.org/wiki/Conditioned_disjunction'>
    Wikipedia</a># podaje poniższą definicję pewnego dziwnego spójnika: *)

Definition conditioned_disjunction (P Q R : Prop) : Prop :=
  (Q -> P) /\ (~ Q -> R).

(** Wyraź za jego pomocą wszystkie podstawowe spójniki, tj. implikację, dysjunkcję,
    koniunkcje i negację.

    Udowodnij też garść twierdzeń mówiących, co się stanie, gdy za [P], [Q] lub [R]
    wstawić [True] lub [False]. *)

(* begin hide *)
(* TODO: tu rozwiązania zadań o [conditioned_disjunction] *)
(* end hide *)