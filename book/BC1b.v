(** * BC1b: Inne spójniki? [TODO] *)

From Typonomikon Require Export BC1a.

(** * Różnica między "lub" i "albo" (TODO) *)

Definition xor (A B : Prop) : Prop :=
  (A /\ ~ B) \/ (~ A /\ B).

Infix "`xor`" := xor (at level 85, right associativity).

Section xor_lemmas.

Context (P Q R : Prop).

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

Lemma xor_spec :
  xor P Q <-> (P \/ Q) /\ (~ P \/ ~ Q).
(* begin hide *)
Proof.
  unfold xor, iff.
  split.
  - intros [[p nq] | [np q]].
    + split.
      * left; assumption.
      * right; assumption.
    + split.
      * right; assumption.
      * left; assumption.
  - intros [[p | q] [np | nq]].
    + contradiction.
    + left; split; assumption.
    + right; split; assumption.
    + contradiction.
Qed.
(* end hide *)

Lemma xor_irrefl :
  P `xor` P <-> False.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_irrefl_true :
  P -> Q -> P `xor` Q <-> False.
(* begin hide *)
Proof. unfold xor; tauto. Qed.
(* end hide *)

Lemma xor_irrefl_false :
  ~ P -> ~ Q -> P `xor` Q <-> False.
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

Lemma not_iff_xor :
  xor P Q -> ~ (P <-> Q).
(* begin hide *)
Proof.
  unfold xor, iff.
  intros H1 H2.
  destruct H2 as [pq qp], H1 as [[p nq] | [np q]].
  - apply nq, pq.
    assumption.
  - apply np, qp.
    assumption.
Qed.
(* end hide *)

Lemma Irrefutable_xor_not_iff :
  ~ ~ (~ (P <-> Q) -> xor P Q).
(* begin hide *)
Proof. unfold xor; firstorder. Qed.
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

Lemma Irrefutable_xor_cotrans :
  ~ ~ (xor P Q -> xor P R \/ xor Q R).
(* begin hide *)
Proof. unfold xor; firstorder. Qed.
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

End xor_lemmas.

(** * Zdecyduj się pan, czyli spójnik "i/lub"  (TODO) *)

Definition andor (P Q : Prop) : Prop :=
  P \/ Q \/ (P /\ Q).

Infix "`andor`" := andor (at level 85, right associativity).

Section andor_lemmas.

Context (P Q R : Prop).

Lemma or_and :
  P /\ Q -> P \/ Q.
(* begin hide *)
Proof.
  destruct 1 as [p q]. left. assumption.
Qed.
(* end hide *)

Lemma andor_or :
  P `andor` Q <-> P \/ Q.
(* begin hide *)
Proof.
  unfold andor.
  split.
  - intros [p | [q | [p q]]].
    + left. assumption.
    + right. assumption.
    + left. assumption.
  - intros [p | q].
    + left. assumption.
    + right. left. assumption.
Qed.
(* end hide *)

End andor_lemmas.

(** * Zdecyduj się pan po raz drugi, czyli spójnik "i/albo" (TODO) *)

Definition andxor (P Q : Prop) : Prop :=
  P `xor` Q `xor` (P /\ Q).

Infix "`andxor`" := andxor (at level 85, right associativity).

Section andxor_lemmas.

Context (P Q R : Prop).

Lemma andxor_or :
  (forall P : Prop, P \/ ~ P) ->
    P `andxor` Q <-> P \/ Q.
(* begin hide *)
Proof.
  unfold andxor.
  intros lem.
  split.
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
  ~ ~ (P `andxor` Q <-> P \/ Q).
(* begin hide *)
Proof.
  unfold andxor.
  intros H; apply H.
  split.
  - intros [[p n] | [np [[q npq] | [nq [p q]]]]].
    + now left.
    + now right.
    + now left.
  - intros [p | q].
    + left.
      split; [assumption |].
      intros [[q npq] | [nq [p' q]]].
      * now apply npq.
      * contradiction.
    + right.
      split.
      * intros p.
        apply H.
Restart.
  firstorder.
Qed.
(* end hide *)

End andxor_lemmas.

(** * Ani w tę ani we wtę, czyli negacja dysjunkcji (TODO) *)

Definition nor (P Q : Prop) : Prop :=
  ~ (P \/ Q).

Infix "`nor`" := nor (at level 85, right associativity).

Section nor_lemmas.

Context (P Q R : Prop).

Lemma nor_comm :
  nor P Q <-> nor Q P.
(* begin hide *)
Proof.
  unfold nor.
  split.
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
  nor True P <-> False.
(* begin hide *)
Proof.
  unfold nor.
  split.
  - intros f. apply f. left. trivial.
  - contradiction.
Qed.
(* end hide *)

Lemma nor_True_r :
  nor P True <-> False.
(* begin hide *)
Proof.
  unfold nor.
  split.
  - intros f. apply f. right. trivial.
  - contradiction.
Qed.
(* end hide *)

Lemma nor_False_l :
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
  nor P False <-> ~ P.
(* begin hide *)
Proof.
  unfold nor.
  split.
  - intros f p. apply f. left. assumption.
  - intros np [p | f]; contradiction.
Qed.
(* end hide *)

Lemma nor_antiidempotent :
  nor P P <-> ~ P.
(* begin hide *)
Proof.
  unfold nor. split.
  - intros f p. apply f. left. assumption.
  - intros f [p | p]; contradiction.
Qed.
(* end hide *)

End nor_lemmas.

(** ** W nieco innej wersji (TODO) *)

Definition nor' (P Q : Prop) : Prop :=
  ~ P /\ ~ Q.

Notation "'neither' P 'nor' Q" := (nor' P Q) (at level 85, right associativity).

Section nor'_lemmas.

Context (P Q R : Prop).

Lemma nor'_comm :
  nor' P Q <-> nor' Q P.
(* begin hide *)
Proof.
  unfold nor'.
  split.
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
  nor' True P <-> False.
(* begin hide *)
Proof.
  unfold nor'.
  split.
  - intros [? _]. contradiction.
  - contradiction.
Qed.
(* end hide *)

Lemma nor'_True_r :
  nor' P True <-> False.
(* begin hide *)
Proof.
  unfold nor'.
  split.
  - intros [_ ?]. contradiction.
  - contradiction.
Qed.
(* end hide *)

Lemma nor'_False_l :
  nor' False P <-> ~ P.
(* begin hide *)
Proof.
  unfold nor'.
  split.
  - intros [_ np]. assumption.
  - intros np. split.
    + intros e. contradiction.
    + assumption.
Qed.
(* end hide *)

Lemma nor'_False_r :
  nor' P False <-> ~ P.
(* begin hide *)
Proof.
  unfold nor'.
  split.
  - intros [np _]. assumption.
  - intros np. split.
    + assumption.
    + intros e. contradiction.
Qed.
(* end hide *)

Lemma nor'_antiidempotent :
  nor' P P <-> ~ P.
(* begin hide *)
Proof.
  unfold nor'.
  split.
  - intros [np _]. assumption.
  - intros np. split; assumption.
Qed.
(* end hide *)

(** Równoważność *)

Lemma nor_nor' :
  P `nor` Q <-> neither P nor Q.
(* begin hide *)
Proof.
  unfold nor'; split.
  - intros f. split.
    + intros p. apply f. left. assumption.
    + intros q. apply f. right. assumption.
  - intros [np nq] [p | q]; contradiction.
Qed.
(* end hide *)

End nor'_lemmas.

(** * [nand], czyli negacja koniunkcji *)

Definition nand (P Q : Prop) : Prop :=
  ~ (P /\ Q).

Infix "`nand`" := nand (at level 85, right associativity).

Section nand_lemmas.

Context (P Q R : Prop).

Lemma nand_comm :
  nand P Q <-> nand Q P.
(* begin hide *)
Proof.
  unfold nand.
  split.
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
  nand True P <-> ~ P.
(* begin hide *)
Proof.
  unfold nand.
  split.
  - intros f p. apply f. split; trivial.
  - intros np [_ p]. contradiction.
Qed.
(* end hide *)

Lemma nand_True_r :
  nand P True <-> ~ P.
(* begin hide *)
Proof.
  unfold nand.
  split.
  - intros f p. apply f. split; trivial.
  - intros np [p _]. contradiction.
Qed.
(* end hide *)

Lemma nand_False_l' :
  nand False P.
(* begin hide *)
Proof.
  unfold nand. intros [[] _].
Qed.
(* end hide *)

Lemma nand_False_l :
  nand False P <-> True.
(* begin hide *)
Proof.
  split; intros.
  - trivial.
  - apply nand_False_l'.
Qed.
(* end hide *)

Lemma nand_False_r :
  nand P False <-> True.
(* begin hide *)
Proof.
  unfold nand.
  split.
  - intros _. trivial.
  - intros _ [p f]. contradiction.
Qed.
(* end hide *)

Lemma nand_antiidempotent :
  nand P P <-> ~ P.
(* begin hide *)
Proof.
  unfold nand.
  split.
  - intros f p. apply f. split; assumption.
  - intros np [p _]. contradiction.
Qed.
(* end hide *)

End nand_lemmas.

(** * Antyimplikacja, czyli negacja implikacji *)

Definition nimpl (P Q : Prop) : Prop :=
  ~ (P -> Q).

Infix "`nimpl`" := nimpl (at level 85, right associativity).

Section nimpl_lemmas.

Context (P Q R : Prop).

Lemma nimpl_False_l :
  ~ nimpl False P.
(* begin hide *)
Proof.
  unfold nimpl.
  intros f.
  apply f.
  intros c.
  contradiction.
Qed.
(* end hide *)

Lemma nimpl_False_r :
  nimpl P False <-> ~ ~ P.
(* begin hide *)
Proof.
  unfold nimpl.
  split; intros; assumption.
Qed.
(* end hide *)

Lemma nimpl_True_l :
  nimpl True P <-> ~ P.
(* begin hide *)
Proof.
  unfold nimpl.
  split.
  - intros f p. apply f. intros _. assumption.
  - intros f p. apply f, p. trivial.
Qed.
(* end hide *)

Lemma nimpl_True_r :
  ~ nimpl P True.
(* begin hide *)
Proof.
  unfold nimpl.
  intros f. apply f. intros _. trivial.
Qed.
(* end hide *)

Lemma nimpl_conv :
  nimpl (~ Q) (~ P) -> nimpl P Q.
(* begin hide *)
Proof.
  unfold nimpl.
  intros f g.
  apply f.
  intros nq p.
  apply nq, g, p.
Qed.
(* end hide *)

Lemma nimpl_conv' :
  nimpl P Q -> nimpl (~ Q) (~ P).
(* begin hide *)
Proof.
  unfold nimpl.
  intros f g.
  apply f.
  intros p.
  exfalso.
  apply g; [| assumption].
  intros q.
  apply f.
  intros _.
  assumption.
Qed.
(* end hide *)

End nimpl_lemmas.

(** * Zadania (TODO) *)

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