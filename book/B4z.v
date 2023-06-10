(** * B4z: Logika klasyczna jako logika silnych i słabych spójników [TODO] *)

From Typonomikon Require Export B4.

(** * Silna implikacja *)

Definition simpl (P Q : Prop) : Prop := ~ P \/ Q.

Lemma impl_simpl :
  forall P Q : Prop,
    simpl P Q -> (P -> Q).
(* begin hide *)
Proof.
  unfold simpl. intros P Q [np | q] p.
  - contradiction.
  - assumption.
Qed.
(* end hide *)

Lemma simpl_simpl_impl :
  LEM ->
    forall P Q : Prop,
      simpl (simpl P Q) (P -> Q).
(* begin hide *)
Proof.
  unfold LEM, simpl.
  intros lem P Q.
  destruct (lem P) as [p | np], (lem Q) as [q | nq].
  - right. intros _. assumption.
  - left. intros [np | q]; contradiction.
  - right. intros _. assumption.
  - right. intros p. contradiction.
Qed.
(* end hide *)

Lemma simpl_impl_classically :
  LEM ->
    forall P Q : Prop,
      (P -> Q) -> simpl P Q.
(* begin hide *)
Proof.
  unfold LEM, simpl.
  intros lem P Q f.
  destruct (lem P) as [p | np].
  - right. apply f. assumption.
  - left. assumption.
Qed.
(* end hide *)

Lemma simpl_impl_tabu :
  (forall P Q : Prop, (P -> Q) -> simpl P Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, simpl.
  intros simpl_impl P.
  apply or_comm. apply simpl_impl. intros p. trivial.
Qed.
(* end hide *)

(** * Słaba implikacja *)

Definition wimpl (P Q : Prop) : Prop := ~ Q -> ~ P.

Lemma wimpl_alternative :
  forall P Q : Prop, wimpl P Q <-> ~ (P /\ ~ Q).
(* begin hide *)
Proof. unfold wimpl; tauto. Qed.
(* end hide *)

Lemma wimpl_impl :
  forall P Q : Prop,
    (P -> Q) -> wimpl P Q.
(* begin hide *)
Proof.
  unfold wimpl. intros P Q f nq p.
  apply nq, f, p.
Qed.
(* end hide *)

Lemma impl_wimpl_irrefutable :
  forall P Q : Prop,
    ~ ~ (wimpl P Q -> (P -> Q)).
(* begin hide *)
Proof.
  unfold wimpl.
  intros P Q H. apply H.
  intros f p. exfalso. apply f; [| assumption].
  intros q. apply H. intros _ _. assumption.
Qed.
(* end hide *)

Lemma wimpl_impl_classically :
  LEM ->
    forall P Q : Prop,
      wimpl P Q -> (P -> Q).
(* begin hide *)
Proof.
  unfold LEM, wimpl.
  intros lem P Q f p.
  destruct (lem Q) as [q | nq].
  - assumption.
  - contradict p. apply f. assumption.
Qed.
(* end hide *)

Lemma impl_wimpl_wimpl :
  forall P Q : Prop,
    wimpl (P -> Q) (wimpl P Q).
(* begin hide *)
Proof.
  unfold LEM, wimpl.
  intros P Q f g. apply f.
  intros nq p. apply nq, g. assumption.
Qed.
(* end hide *)

Lemma impl_wimpl_tabu :
  (forall P Q : Prop, wimpl P Q -> (P -> Q)) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, wimpl.
  intros impl_wimpl P.
  specialize (impl_wimpl (~ ~ (P \/ ~ P)) (P \/ ~ P)).
  apply impl_wimpl.
  - tauto.
  - apply Irrefutable_LEM.
Qed.
(* end hide *)

(** * Słaba dysjunkcja *)

Definition wor (P Q : Prop) : Prop := ~ P -> Q.

Lemma wor_or :
  forall P Q : Prop,
    P \/ Q -> wor P Q.
(* begin hide *)
Proof.
  unfold wor. intros P Q [p | q] np.
  - contradiction.
  - assumption.
Qed.
(* end hide *)

Lemma wor_introl :
  forall P Q : Prop,
    P -> wor P Q.
(* begin hide *)
Proof.
  unfold wor. intros P Q p np. contradiction.
Qed.
(* end hide *)

Lemma wor_intror :
  forall P Q : Prop,
    Q -> wor P Q.
(* begin hide *)
Proof.
  unfold wor. intros P Q q _. assumption.
Qed.
(* end hide *)

Lemma wor_False_l :
  forall P : Prop,
    wor False P <-> P.
(* begin hide *)
Proof.
  unfold wor. intros P; split.
  - intros p. apply p. intros f. contradiction.
  - intros p _. assumption.
Qed.
(* end hide *)

Lemma wor_False_r :
  LEM ->
    forall P : Prop,
      wor P False <-> P.
(* begin hide *)
Proof.
  unfold LEM, wor.
  intros lem P; split.
  - intros nnp. destruct (lem P) as [p | np].
    + assumption.
    + contradiction.
  - intros p np. contradiction.
Qed.
(* end hide *)

Lemma wor_True_l :
  forall P : Prop,
    wor True P <-> True.
(* begin hide *)
Proof.
  unfold wor. intros P; split.
  - intros _. trivial.
  - intros _ nt. contradiction.
Qed.
(* end hide *)

Lemma wor_True_r :
  forall P : Prop,
    wor P True <-> True.
(* begin hide *)
Proof.
  unfold wor. intros P; split; intros _; trivial.
Qed.
(* end hide *)

Lemma wor_assoc :
  forall P Q R : Prop,
    wor (wor P Q) R <-> wor P (wor Q R).
(* begin hide *)
Proof.
  unfold wor. intros P Q R; split.
  - intros f np nq. apply f. intros g. apply nq, g. assumption.
  - intros f ng. apply f.
    + intros p. apply ng. intros np. contradiction.
    + intros q. apply ng. intros _. assumption.
Qed.
(* end hide *)

Lemma wor_comm :
  LEM ->
    forall P Q : Prop,
      wor P Q <-> wor Q P.
(* begin hide *)
Proof.
  unfold LEM, wor.
  intros lem P Q; split.
  - intros f nq. destruct (lem P) as [p | np].
    + assumption.
    + contradict nq. apply f. assumption.
  - intros f np. destruct (lem Q) as [q | nq].
    + assumption.
    + contradict np. apply f. assumption.
Qed.
(* end hide *)

Lemma or_wor_classically :
  LEM ->
    forall P Q : Prop,
      wor P Q -> P \/ Q.
(* begin hide *)
Proof.
  unfold LEM, wor.
  intros lem P Q f.
  destruct (lem P) as [p | np].
  - left. assumption.
  - destruct (lem Q) as [q | nq].
    + right. assumption.
    + right. apply f. intros p. contradiction.
Qed.
(* end hide *)

Lemma or_wor_tabu :
  (forall P Q : Prop, wor P Q -> P \/ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, wor.
  intros or_wor P.
  apply or_wor. intros np. assumption.
Qed.
(* end hide *)

(** * Słaba dysjunkcja przemienna *)

Definition wor2 (P Q : Prop) : Prop := (~ P -> Q) \/ (~ Q -> P).

Lemma wor2_or :
  forall P Q : Prop,
    P \/ Q -> wor2 P Q.
(* begin hide *)
Proof.
  unfold wor2. intros P Q [p | q].
  - right. intros _. assumption.
  - left. intros _. assumption.
Qed.
(* end hide *)

Lemma wor_wor2 :
  LEM ->
    forall P Q : Prop,
      wor2 P Q -> wor P Q.
(* begin hide *)
Proof.
  unfold LEM, wor2, wor.
  intros lem P Q [f | f] np.
  - apply f. assumption.
  - destruct (lem Q) as [q | nq].
    + assumption.
    + contradict np. apply f. assumption.
Qed.
(* end hide *)

Lemma wor2_wor :
  forall P Q : Prop,
    wor P Q -> wor2 P Q.
(* begin hide *)
Proof.
  unfold wor2, wor.
  intros P Q f. left. assumption.
Qed.
(* end hide *)

Lemma wor2_introl :
  forall P Q : Prop,
    P -> wor2 P Q.
(* begin hide *)
Proof.
  unfold wor2. intros P Q p. right. intros _. assumption.
Qed.
(* end hide *)

Lemma wor2_intror :
  forall P Q : Prop,
    Q -> wor2 P Q.
(* begin hide *)
Proof.
  unfold wor2. intros P Q q. left. intros _. assumption.
Qed.
(* end hide *)

Lemma wor2_False_l :
  LEM ->
    forall P : Prop,
      wor2 False P <-> P.
(* begin hide *)
Proof.
  unfold LEM, wor2.
  intros lem P; split.
  - intros [p | f].
    + apply p. intros f. contradiction.
    + destruct (lem P) as [p | np].
      * assumption.
      * contradiction.
  - intros p. left. intros _. assumption.
Qed.
(* end hide *)

Lemma wor2_False_r :
  LEM ->
    forall P : Prop,
      wor2 P False <-> P.
(* begin hide *)
Proof.
  unfold LEM, wor2.
  intros lem P; split.
  - intros [nnp | p].
    + destruct (lem P) as [p | np].
      * assumption.
      * contradiction.
    + apply p. intros f. assumption.
  - intros p. right. intros _. assumption.
Qed.
(* end hide *)

Lemma wor2_True_l :
  forall P : Prop,
    wor2 True P <-> True.
(* begin hide *)
Proof.
  unfold wor2. intros P; split.
  - intros _. trivial.
  - intros _. right. intros _. trivial.
Qed.
(* end hide *)

Lemma wor2_True_r :
  forall P : Prop,
    wor2 P True <-> True.
(* begin hide *)
Proof.
  unfold wor2. intros P; split; intros _.
  - trivial.
  - left. intros _. trivial.
Qed.
(* end hide *)

Lemma wor2_comm :
  forall P Q : Prop,
    wor2 P Q <-> wor2 Q P.
(* begin hide *)
Proof.
  unfold wor2. intros P Q. split.
  - intros [q | p]; [right | left]; assumption.
  - intros [p | q]; [right | left]; assumption.
Qed.
(* end hide *)

Lemma wor2_assoc :
  LEM ->
    forall P Q R : Prop,
      wor2 (wor2 P Q) R <-> wor2 P (wor2 Q R).
(* begin hide *)
Proof.
  unfold LEM.
  intros lem P Q R; split.
  - intros [r | npq].
    + unfold wor2. left. intros _. left. intros _. apply r. unfold wor2. admit.
    + red. left. intros np. red. right. intros nr.
      destruct (npq nr) as [q | p].
      * apply q. assumption.
      * contradict np. apply p. intros q.
Abort.
(* end hide *)

Lemma or_wor2_classically :
  LEM ->
    forall P Q : Prop,
      wor2 P Q -> P \/ Q.
(* begin hide *)
Proof.
  unfold LEM, wor2.
  intros lem P Q f.
  destruct (lem P) as [p | np].
  - left. assumption.
  - destruct (lem Q) as [q | nq].
    + right. assumption.
    + destruct f as [f | f].
      * right. apply f. intros p. contradiction.
      * left. apply f. intros q. contradiction.
Qed.
(* end hide *)

Lemma or_wor2_tabu :
  (forall P Q : Prop, wor2 P Q -> P \/ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, wor2.
  intros or_wor2 P.
  apply or_wor2. left. intros np. assumption.
Qed.
(* end hide *)

(** * Słaba koniunkcja *)

Definition aand (P Q : Prop) : Prop := ~ (~ P \/ ~ Q).

Lemma and_aand :
  forall P Q : Prop,
    P /\ Q -> aand P Q.
(* begin hide *)
Proof.
  unfold aand.
  intros P Q [p q] [np | nq].
  - apply np. assumption.
  - apply nq. assumption.
Qed.
(* end hide *)

Lemma aand_and_classically :
  LEM ->
    forall P Q : Prop,
      aand P Q -> P /\ Q.
(* begin hide *)
Proof.
  unfold LEM, aand.
  intros lem P Q f; split.
  - destruct (lem P) as [p | np].
    + assumption.
    + contradict f. left. assumption.
  - destruct (lem Q) as [q | nq].
    + assumption.
    + contradict f. right. assumption.
Qed.
(* end hide *)

Lemma aand_and_tabu :
  (forall P Q : Prop, aand P Q -> P /\ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, aand.
  intros aand_and P.
  destruct (aand_and (P \/ ~ P) True).
  - intros [f | f].
    + eapply Irrefutable_LEM. eassumption.
    + contradiction.
  - assumption.
Qed.
(* end hide *)

Lemma aand_elim :
  forall P Q R : Prop,
    (P -> R) -> (Q -> R) -> (~ ~ R -> R) -> ~ (~ P /\ ~ Q) -> R.
(* begin hide *)
Proof.
  intros P Q R pr qr nnrr pq.
  apply nnrr. intro nr.
  apply pq. split.
  - intro p. apply nr, pr, p.
  - intro q. apply nr, qr, q.
Qed.
(* end hide *)

(** * Silna równoważność *)

Definition siff (P Q : Prop) : Prop := P /\ Q \/ ~ P /\ ~ Q.

Lemma iff_siff :
  forall P Q : Prop,
    siff P Q -> P <-> Q.
(* begin hide *)
Proof.
  unfold siff. intros P Q [[p q] | [np nq]].
  - split; intros _; assumption.
  - split; intros; contradiction.
Qed.
(* end hide *)

Lemma siff_iff :
  LEM ->
    forall P Q : Prop,
      P <-> Q -> siff P Q.
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P Q [pq qp].
  destruct (lem P) as [p | np], (lem Q) as [q | nq].
  - left. split; assumption.
  - contradiction nq. apply pq. assumption.
  - contradiction np. apply qp. assumption.
  - right. split; assumption.
Qed.
(* end hide *)

Lemma siff_iff_iff :
  LEM ->
    forall P Q : Prop,
      P <-> Q <-> siff P Q.
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P Q. split.
  - apply siff_iff. assumption.
  - apply iff_siff.
Qed.
(* end hide *)

Lemma siff_siff_iff :
  LEM ->
    forall P Q : Prop,
      siff (siff P Q) (P <-> Q).
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P Q.
  destruct (lem P) as [p | np], (lem Q) as [q | nq].
  - left. split.
    + left. split; assumption.
    + split; intros _; assumption.
  - right. split.
    + intros [[] | []]; contradiction.
    + intros [pq qp]. contradict nq. apply pq. assumption.
  - right. split.
    + intros [[] | []]; contradiction.
    + intros [pq qp]. contradict np. apply qp. assumption.
  - left. split.
    + right. split; assumption.
    + split; intros; contradiction.
Qed.
(* end hide *)

Lemma siff_xor :
  forall P Q : Prop,
    siff P Q -> xor P Q -> False.
(* begin hide *)
Proof.
  unfold siff, xor.
  intros P Q [[p q] | [np nq]] [[p' nq'] | [np' q']]; contradiction.
Qed.
(* end hide *)

Lemma siff_id :
  LEM ->
    forall P : Prop,
      siff P P.
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P.
  destruct (lem P) as [p | np].
  - left. split; assumption.
  - right. split; assumption.
Qed.
(* end hide *)

Lemma siff_comm :
  LEM ->
    forall P Q : Prop,
      siff (siff P Q) (siff Q P).
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P Q.
  destruct (lem P) as [p | np], (lem Q) as [q | nq]; firstorder.
Qed.
(* end hide *)

Lemma siff_assoc :
  LEM ->
    forall P Q R : Prop,
      siff (siff (siff P Q) R) (siff P (siff Q R)).
(* begin hide *)
Proof.
  unfold LEM.
  intros lem P Q R.
  specialize (lem P) as lemP.
  specialize (lem Q) as lemQ.
  specialize (lem R) as lemR.
  clear lem. unfold siff. tauto.
Qed.
(* end hide *)

(** * Silna antyimplikacja *)

Definition snimpl (P Q : Prop) : Prop := P /\ ~ Q.

(* TODO: jakieś lematy *)

Definition NI : Prop :=
  forall P Q : Prop, ~ (P -> Q) -> P /\ ~ Q.

Lemma NI_LEM :
  NI -> LEM.
(* begin hide *)
Proof.
  unfold NI, LEM.
  intros NI P.
  destruct (NI (P \/ ~ P) False) as [lem _].
  - apply Irrefutable_LEM.
  - assumption.
Qed.
(* end hide *)

Definition wxor (P Q : Prop) : Prop := ~ (P <-> Q).

Lemma wxor_irrefl :
  forall P : Prop, ~ wxor P P.
(* begin hide *)
Proof.
  unfold wxor. intros A f.
  apply f. split; trivial.
Qed.
(* end hide *)

Lemma wxor_comm :
  forall P Q : Prop, wxor P Q -> wxor Q P.
(* begin hide *)
Proof.
  unfold wxor. intros P Q f g.
  apply f. apply iff_symm. assumption.
Qed.
(* end hide *)

Lemma wxor_cotrans :
  LEM ->
    (forall P Q R : Prop, wxor P Q -> wxor P R \/ wxor Q R).
(* begin hide *)
Proof.
  unfold LEM, wxor. intros lem P Q R f.
  destruct (lem (P <-> R)) as [HR | HR]; cycle 1.
  - left. assumption.
  - destruct (lem (Q <-> R)) as [HQ | HQ]; cycle 1.
    + right. assumption.
    + contradiction f. apply iff_trans with R.
      * assumption.
      * apply iff_symm. assumption.
Qed.
(* end hide *)

Lemma wxor_assoc :
  forall P Q R : Prop,
    wxor P (wxor Q R) <-> wxor (wxor P Q) R.
(* begin hide *)
Proof.
  unfold wxor. split; firstorder.
Qed.
(* end hide *)

Lemma wxor_xor :
  forall P Q : Prop, xor P Q -> wxor P Q.
(* begin hide *)
Proof.
  unfold xor, wxor.
  intros P Q [[p nq] | [np q]].
  - intros f. apply nq, f. assumption.
  - intros f. apply np, f. assumption.
Qed.
(* end hide *)

Lemma xor_wxor_classically :
  LEM ->
    forall P Q : Prop, wxor P Q -> xor P Q.
(* begin hide *)
Proof.
  unfold LEM, xor, wxor.
  intros lem P Q npq.
  destruct (lem P) as [p | np].
  - left. split; [assumption |]. intros q. apply npq. split; trivial.
  - right. split; [assumption |]. destruct (lem Q) as [q | nq].
    + assumption.
    + exfalso. apply npq. split; intros; contradiction.
Qed.
(* end hide *)

Lemma wxor_False_r_classically :
  LEM ->
    forall P : Prop, wxor P False <-> P.
(* begin hide *)
Proof.
  unfold LEM, wxor, iff.
  intros lem P. split.
  - intros f. destruct (lem P) as [p | np].
    + assumption.
    + contradict f. split; intros; contradiction.
  - intros p [np _]. contradiction.
Qed.
(* end hide *)

Lemma wxor_False_l_classically :
  LEM ->
    forall P : Prop, wxor False P <-> P.
(* begin hide *)
Proof.
  unfold LEM, wxor.
  intros lem P; split.
  - intros H. destruct (lem P) as [p | np].
    + assumption.
    + exfalso. apply H. split; [intros [] | contradiction].
  - intros p f. apply f. assumption.
Qed.
(* end hide *)

Lemma wxor_True_l :
  forall P : Prop, wxor True P <-> ~ P.
(* begin hide *)
Proof.
  unfold wxor. tauto.
Qed.
(* end hide *)

Lemma wxor_True_r :
  forall P : Prop, wxor P True <-> ~ P.
(* begin hide *)
Proof.
  unfold wxor. tauto.
Qed.
(* end hide *)

(** * Klasyczna dysjunkcja (TODO) *)

Definition cor (P Q : Prop) : Prop :=
  ~ ~ (P \/ Q).

Lemma cor_in_l :
  forall P Q : Prop,
    P -> cor P Q.
(* begin hide *)
Proof.
  unfold cor. intros P Q p f.
  apply f. left. assumption.
Qed.
(* end hide *)

Lemma cor_in_r :
  forall P Q : Prop,
    Q -> cor P Q.
(* begin hide *)
Proof.
  unfold cor. intros P Q p f.
  apply f. right. assumption.
Qed.
(* end hide *)

Lemma cor_assoc :
  forall P Q R : Prop,
    cor (cor P Q) R <-> cor P (cor Q R).
(* begin hide *)
Proof.
  unfold cor. intros P Q; split; intros f g.
  - apply f. intros h. apply g. right. intros i. destruct h as [nnpq | r].
    + apply nnpq. intros [p | q].
      * apply g. left. assumption.
      * apply i. left. assumption.
    + apply i. right. assumption.
  - apply g. left. intros npq. apply f. intros [p | nnqr].
    + apply npq. left. assumption.
    + apply nnqr. intros [q | r].
      * apply npq. right. assumption.
      * apply g. right. assumption.
Qed.
(* end hide *)

Lemma cor_comm :
  forall P Q : Prop,
    cor P Q -> cor Q P.
(* begin hide *)
Proof.
  unfold cor. intros P Q f g.
  apply f. intros [p | q]; apply g.
  - right. assumption.
  - left. assumption.
Qed.
(* end hide *)

Lemma cor_True_l :
  forall P : Prop,
    cor True P <-> True.
(* begin hide *)
Proof.
  unfold cor. intros P; split.
  - intros _. trivial.
  - intros _ f. apply f. left. trivial.
Qed.
(* end hide *)

Lemma cor_True_r :
  forall P : Prop,
    cor P True <-> True.
(* begin hide *)
Proof.
  unfold cor. intros P; split.
  - intros _. trivial.
  - intros _ f. apply f. right. trivial.
Qed.
(* end hide *)

Lemma cor_False_l :
  forall P : Prop,
    cor False P <-> ~ ~ P.
(* begin hide *)
Proof.
  unfold cor. intros P; split.
  - intros f np. apply f. intros [? | p]; contradiction.
  - intros nnp f. apply nnp. intros p. apply f. right. assumption.
Qed.
(* end hide *)

Lemma cor_False_r :
  forall P : Prop,
    cor P False <-> ~ ~ P.
(* begin hide *)
Proof.
  unfold cor. intros P; split.
  - intros f np. apply f. intros [? | p]; contradiction.
  - intros nnp f. apply nnp. intros p. apply f. left. assumption.
Qed.
(* end hide *)

Lemma cor_or :
  forall P Q : Prop,
    P \/ Q -> cor P Q.
(* begin hide *)
Proof.
  unfold cor. intros P Q [p | q] npq.
  - apply npq. left. assumption.
  - apply npq. right. assumption.
Qed.
(* end hide *)

Lemma cor_LEM :
  forall P : Prop,
    cor P (~ P).
(* begin hide *)
Proof.
  unfold cor.
  intros P f.
  apply f. right. intros p.
  apply f. left. assumption.
Qed.
(* end hide *)

Lemma or_cor_classically :
  LEM -> forall P Q : Prop, cor P Q -> P \/ Q.
(* begin hide *)
Proof.
  unfold LEM, cor.
  intros lem P Q f. destruct (lem (P \/ Q)).
  - assumption.
  - contradiction.
Qed.
(* end hide *)

Lemma or_cor_tabu :
  (forall P Q : Prop, cor P Q -> P \/ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold cor, LEM.
  intros or_cor P. apply or_cor. tauto.
Qed.
(* end hide *)

Lemma cor_spec :
  forall P Q : Prop,
    cor P Q <-> ~ (~ P /\ ~ Q).
(* begin hide *)
Proof.
  split.
  - intros H [np nq]. apply H. intros [p | q].
    + apply np, p.
    + apply nq, q.
  - intros pq npq. apply pq. split.
    + intro p. apply npq. left. assumption.
    + intro q. apply npq. right. assumption.
Qed.
(* end hide *)

Lemma cor_wor :
  forall P Q : Prop,
    wor P Q -> cor P Q.
(* begin hide *)
Proof.
  unfold wor, cor.
  intros P Q f npq. apply npq. right. apply f.
  intros p. apply npq. left. assumption.
Qed.
(* end hide *)

Lemma cor_wor2 :
  forall P Q : Prop,
    wor2 P Q -> cor P Q.
(* begin hide *)
Proof.
  unfold wor2, cor.
  intros P Q [f | f] npq.
  - apply npq. right. apply f. intros p. apply npq. left. assumption.
  - apply npq. left. apply f. intros p. apply npq. right. assumption.
Qed.
(* end hide *)

(** * Bonus: klasyczna koń-junkcja (TODO) *)

Lemma cand_and_LEM :
  (forall P Q : Prop, ~ ~ (P /\ Q) -> P /\ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM. intros H P.
  destruct (H (P \/ ~ P) True).
  - intros f. apply f. split.
    + right. intros p. apply f. split.
      * left. assumption.
      * trivial.
    + trivial.
  - assumption.
Qed.
(* end hide *)

(** * Bonus 2: klasyczny kwantyfikator egzystencjalny (TODO) *)

Lemma weak_ex_elim :
  forall (A : Type) (P : A -> Prop) (R : Prop),
    (forall x : A, P x -> R) -> (~ ~ R -> R) ->
      ~ (forall x : A, ~ P x) -> R.
(* begin hide *)
Proof.
  intros A P R Hpr Hnr Hnp.
  apply Hnr. intro nr.
  apply Hnp. intros x np.
  apply nr, (Hpr x), np.
Qed.
(* end hide *)

(** * Słaby kwantyfikator egzystencjalny *)

Definition wexists {A : Type} (P : A -> Prop) : Prop :=
  ~ forall x : A, ~ P x.

Lemma wexists_exists :
  forall {A : Type} (P : A -> Prop),
    ex P -> wexists P.
(* begin hide *)
Proof.
  unfold wexists.
  intros A P [x p] H.
  apply (H x). assumption.
Qed.
(* end hide *)

Lemma exists_wexists_classically :
  LEM ->
    forall {A : Type} (P : A -> Prop),
      wexists P -> ex P.
(* begin hide *)
Proof.
  unfold LEM, wexists.
  intros lem A P H.
  destruct (lem (exists y, P y)) as [e | ne].
  - assumption.
  - exfalso. apply H. intros x p. apply ne. exists x. assumption.
Qed.
(* end hide *)

Lemma exists_wexists_tabu :
  (forall {A : Type} (P : A -> Prop), wexists P -> ex P)
    ->
  LEM.
(* begin hide *)
Proof.
  unfold LEM, wexists.
  intros exists_wexists P.
  specialize (exists_wexists bool (fun b => if b then P else ~ P)); cbn in *.
  destruct exists_wexists as [[] H].
  - intros H.
    specialize (H true) as np; cbn in np.
    specialize (H false) as nnp; cbn in nnp.
    contradiction.
  - left. assumption.
  - right. assumption.
Qed.
(* end hide *)

(** * Słaby kwantyfikator uniwersalny *)

Definition wforall {A : Type} (P : A -> Prop) : Prop :=
  ~ exists x : A, ~ P x.

Lemma wforall_forall :
  forall {A : Type} (P : A -> Prop),
    (forall x : A, P x) -> wforall P.
(* begin hide *)
Proof.
  unfold wforall.
  intros A P H [x np].
  apply np, H.
Qed.
(* end hide *)

Lemma forall_wforall_classically :
  LEM ->
    forall {A : Type} (P : A -> Prop),
      wforall P -> forall x : A, P x.
(* begin hide *)
Proof.
  unfold LEM, wforall.
  intros lem A P H x.
  destruct (lem (P x)) as [p | np].
  - assumption.
  - contradict H. exists x. assumption.
Qed.
(* end hide *)

Lemma forall_wforall_tabu :
  (forall {A : Type} (P : A -> Prop), wforall P -> forall x : A, P x)
    ->
  LEM.
(* begin hide *)
Proof.
  unfold LEM, wforall.
  intros forall_wforall P.
  apply (forall_wforall unit (fun _ => P \/ ~ P)).
  - intros [_ H]. apply Irrefutable_LEM in H. assumption.
  - exact tt.
Qed.
(* end hide *)

(** * Wymyśl to sam... *)

(** **** Ćwiczenie *)

(** Jeżeli jeszcze ci mało, spróbuj sam wymyślić jakieś
    spójniki logiczne, których nie ma w logice konstruktywnej
    ani klasycznej.

    Zastanów się, czy taki spójnik ma sens matematyczny, czy nadaje się do
    użytku jedynie w językach naturalnych. Da się go jakoś wyrazić za pomocą
    znanych nam spójników, czy nie bardzo? Twój spójnik jest fajny czy głupi?
    Użyteczny czy bezużyteczny? *)